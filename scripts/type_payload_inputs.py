#!/usr/bin/env python3
"""Read-only inventory and narrowly scoped restoration for Tella comparisons.

The input selection and 510-row copy classification follow the earlier audited
lifecycle runner. This module does not clean, compile or authorize a workload.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


PACKAGES = (
    '@rescript/react', '@rescript/belt', '@jfrolich/ppx-spice',
    'rescript-debounce-react', 'rescript-nodejs', 'rescript-debounce',
    'bs-css', 'bs-css-dom', '@tella-fusion/webapp',
    '@tella-fusion/webapp/packages/tella-std',
    '@tella-fusion/webapp/node_modules/rescript-webapi',
)


def load(path):
    return json.loads(Path(path).read_text())


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True)


def file_state(path):
    path = Path(path)
    if not path.is_file():
        return {'exists': False}
    return {'exists': True, 'sha256': sha(path), 'mtime_ns': path.stat().st_mtime_ns}


def classify_copies(inputs, ledger):
    """Check every row, including absent and unchanged copies, before removal."""
    normalized = dict(inputs)
    evidence = {}
    for path, entry in ledger.items():
        expected = entry['removed_sha256']
        actual = normalized.get(path)
        if actual is not None and actual != expected:
            raise RuntimeError('generated copy content changed: ' + path)
        authored = [name for name in entry['surviving_same_package_sources']
                    if Path(name).is_file() and sha(name) == expected]
        if not authored:
            raise RuntimeError('generated copy lacks matching authored source: ' + path)
        evidence[path] = {'copy_present': actual is not None,
                          'copy_sha256': actual, 'authored_match': authored[0]}
        normalized.pop(path, None)
    return normalized, evidence


class Inventory:
    def __init__(self, root):
        self.root = Path(root)
        self.plan = load(self.root / 'plan.json')
        self.repos = {name: Path(path) for name, path in self.plan['repos'].items()}
        self.tella = self.repos['tella']
        self.web = self.tella / 'packages/core/webapp'
        self.runtime = self.repos['main'] / 'packages/@rescript/runtime'
        self.protected = load(self.root / 'protected.json')
        self.ledger = load(self.root / 'generated-source-copies.json')
        if len(self.ledger) != 510:
            raise RuntimeError('expected exactly 510 generated-copy rows')
        kinds = [entry['kind'] for entry in self.protected.values()]
        if (kinds.count('generated') != 18 or kinds.count('untracked') != 4
                or kinds.count('working_fixture') not in (0, 2)
                or set(kinds) - {'generated', 'untracked', 'working_fixture'}):
            raise RuntimeError('expected 18 generated, four legacy untracked and optional two new-worktree fixtures')

    def metadata(self):
        paths = {str(self.tella / 'node_modules' / name / 'lib/bs/compiler-info.json')
                 for name in PACKAGES}
        paths.add(str(self.tella / 'node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json'))
        if len(paths) != 12:
            raise RuntimeError('metadata set must contain exactly 12 paths')
        return paths

    def dependencies(self):
        return (self.tella / 'node_modules', self.web / 'node_modules', self.runtime)

    def dependency_walk(self):
        seen = set()
        for root in self.dependencies():
            for base, dirs, files in os.walk(root, followlinks=True):
                real = os.path.realpath(base)
                if real in seen:
                    dirs[:] = []
                    continue
                seen.add(real)
                dirs[:] = [name for name in dirs if name not in ('.git', '.cache')]
                yield Path(base), dirs, files

    def inputs(self):
        names = git(self.tella, 'ls-files', '-z').split('\0')[:-1]
        paths = {self.tella / name for name in names
                 if not name.endswith(('.gen.ts', '.js', '.map'))
                 and (self.tella / name).is_file()}
        for base, dirs, files in self.dependency_walk():
            for name in files:
                path = base / name
                if path.is_file() and (path.suffix in ('.res', '.resi', '.ml', '.mli', '.json', '.exe', '.wasm')
                                       or name.endswith(('lock', '.lockb')) or 'ppx' in name.lower()):
                    paths.add(path)
        return {str(path): sha(path) for path in sorted(paths)}

    def snapshot(self):
        links = {}
        for base, dirs, files in self.dependency_walk():
            for name in dirs + files:
                path = base / name
                if path.is_symlink():
                    links[str(path)] = {'link': os.readlink(path), 'resolved': str(path.resolve())}
        sources, heads, statuses = {}, {}, {}
        for name, root in self.repos.items():
            heads[name] = git(root, 'rev-parse', 'HEAD').strip()
            statuses[name] = git(root, 'status', '--porcelain=v1', '-z').split('\0')[:-1]
            if name != 'tella':
                names = git(root, 'ls-files', '-z').split('\0')[:-1]
                sources[name] = {rel: sha(root / rel) for rel in names if (root / rel).is_file()}
        return {'inputs': self.inputs(), 'sources': sources, 'heads': heads,
                'statuses': statuses, 'links': links,
                'protected': {path: file_state(path) for path in self.protected},
                'binaries': {name: sha(self.root / rel)
                             for name, rel in self.plan['binaries'].items()}}

    def compare(self, baseline, current, metadata, restored=False):
        errors = []
        before, before_copies = classify_copies(baseline['inputs'], self.ledger)
        after, after_copies = classify_copies(current['inputs'], self.ledger)
        actual_metadata = self.metadata() & after.keys()
        if actual_metadata != set(metadata):
            errors.append({'metadata': {'expected': sorted(metadata), 'actual': sorted(actual_metadata)}})
        for path in self.metadata():
            before.pop(path, None)
            after.pop(path, None)
        changes = sorted(path for path in before.keys() | after.keys()
                         if before.get(path) != after.get(path))
        if changes:
            errors.append({'unexpected_inputs': changes})
        for key in ('sources', 'heads', 'statuses', 'links', 'binaries'):
            if baseline[key] != current[key]:
                errors.append({'changed_invariant': key})
        for path, entry in self.protected.items():
            if entry['kind'] != 'generated' or restored:
                if current['protected'].get(path) != entry['state']:
                    errors.append({'protected_mismatch': path})
        return {'valid': not errors, 'errors': errors,
                'metadata_present': sorted(actual_metadata), 'ledger_rows': len(after_copies),
                'baseline_present_copies': sum(row['copy_present'] for row in before_copies.values()),
                'current_copies': after_copies}

    def verify_protected(self):
        for path, entry in self.protected.items():
            backup = self.root / entry['backup']
            if file_state(backup) != entry['state']:
                raise RuntimeError('protected backup changed: ' + str(backup))
            if file_state(path) != entry['state']:
                raise RuntimeError('protected live state changed: ' + path)

    def restore(self):
        errors = []
        for path, entry in self.protected.items():
            source, target = self.root / entry['backup'], Path(path)
            try:
                state = entry['state']
                if file_state(source) != state:
                    raise RuntimeError('protected backup changed')
                if not target.is_file() or sha(target) != state['sha256']:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source, target)
                # Equal bytes do not imply the original timestamp survived.
                os.utime(target, ns=(target.stat().st_atime_ns, state['mtime_ns']))
                if file_state(target) != state:
                    raise RuntimeError('restoration verification failed')
            except Exception as exc:
                errors.append({'path': path, 'error': repr(exc)})
        if errors:
            raise RuntimeError('protected restoration failed: ' + repr(errors))

    def outputs(self):
        paths = []
        for base, dirs, names in os.walk(self.web):
            dirs[:] = [name for name in dirs if name != 'node_modules']
            paths.extend(Path(base) / name for name in names if name.endswith('.js'))
        digest, manifest = hashlib.sha256(), {}
        for path in sorted(paths):
            relative = path.relative_to(self.web).as_posix()
            encoded, data = relative.encode(), path.read_bytes()
            digest.update(len(encoded).to_bytes(4, 'big'))
            digest.update(encoded)
            digest.update(len(data).to_bytes(8, 'big'))
            digest.update(data)
            manifest[relative] = hashlib.sha256(data).hexdigest()
        return {'count': len(manifest), 'sha256': digest.hexdigest(), 'manifest': manifest}

    def runtime_sources(self):
        return {str(path): sha(path) for path in sorted((self.runtime / 'lib/ocaml').glob('*.res'))}
