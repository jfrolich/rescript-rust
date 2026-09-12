#!/usr/bin/env python3
"""Prepare a fresh comparison archive. Does not authorize or run any compiler."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess

import type_payload_inputs as inputs
import type_payload_measure as measure
import type_payload_supervisor as supervisor


CAMPAIGN = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260912/type-payload-storage')
BASIS = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260907/simplify-and-speed/lifecycle-handoff-diagnostic')
BASIS_SEAL = '494f789b838b887b88e6d396a305d2b0a0ab0b4e779f4d75f803d7ba6dafbb4a'
REPOS = {
    'worktree': Path('/Users/jake/.opensession/worktrees/rescript-compiler-can-you-do-a-torough-look'),
    'main': Path('/Users/jake/checkouts/rescript-rust'),
    'previous_feature': Path('/Users/jake/.opensession/worktrees/rescript-rust-revert-unaccepted-performance'),
    'tella': Path('/Users/jake/dev/tella-fusion'),
}
CONTROL_HASHES = {
    'bsc': '68d69a39b0bf95ea0d22c0bf5c226c1ca1de4d5722b056e32af92f96d89f1cb3',
    'rescript': '046ffafaef583117779fde98933030775f6f66ebd13edb5df457d3d821f81e8b',
}


def copy_new(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        raise RuntimeError('archive collision: ' + str(target))
    shutil.copy2(source, target)
    if inputs.sha(source) != inputs.sha(target):
        raise RuntimeError('archive copy mismatch: ' + str(target))


def prepare(name, candidate_dir, candidate_head, baseline_delta=None):
    if not re.fullmatch(r'comparison-[a-z0-9-]+', name):
        raise ValueError('use a fresh comparison-name within the campaign')
    if not re.fullmatch(r'[0-9a-f]{40}', candidate_head):
        raise ValueError('candidate head must be a full commit hash')
    candidate_dir = candidate_dir.resolve()
    relative = candidate_dir.relative_to(CAMPAIGN)
    if not ((len(relative.parts) == 1 and relative.name.startswith('candidate-')
             and relative.name.endswith('-bin'))
            or (len(relative.parts) == 2 and relative.parts[0].startswith('candidate-')
                and relative.parts[1] == 'bin')):
        raise ValueError('candidate binaries must be a preserved campaign bin directory')
    root = CAMPAIGN / name
    if root.exists():
        raise RuntimeError('comparison root already exists; never reuse it')
    if shutil.disk_usage(CAMPAIGN).free < 3 * 1024 ** 3:
        raise RuntimeError('less than 3 GiB free; no cleanup is authorized by this script')
    if inputs.sha(BASIS / 'seal.json') != BASIS_SEAL:
        raise RuntimeError('historical basis seal changed')
    basis_seal = inputs.load(BASIS / 'seal.json')
    for relative in ('generated-source-copies.json', 'protected-original-state.json',
                     'protected-untracked-state.json'):
        if inputs.sha(BASIS / relative) != basis_seal['assets'][relative]:
            raise RuntimeError('historical protection basis changed: ' + relative)
    worktree = REPOS['worktree']
    if inputs.git(worktree, 'branch', '--show-current').strip() != 'can-you-do-a-torough-look':
        raise RuntimeError('wrong branch')
    if inputs.git(REPOS['main'], 'rev-parse', 'HEAD').strip() != 'd98b8b9430045d40d08ed89dd75174b5669fa829':
        raise RuntimeError('main changed')
    if inputs.git(REPOS['previous_feature'], 'rev-parse', 'HEAD').strip() != '218e0380aa55160a81aa18a4aa5893438ebf3156':
        raise RuntimeError('previous feature changed')
    if inputs.git(REPOS['tella'], 'rev-parse', 'HEAD').strip() != '66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa':
        raise RuntimeError('Tella changed')
    for args in (['diff', '--exit-code', 'HEAD'], ['diff', '--cached', '--exit-code'],
                 ['diff', '--exit-code', candidate_head, 'HEAD', '--', 'compiler-rust', 'rewatch']):
        subprocess.run(['git', '-C', str(worktree), *args], check=True, stdout=subprocess.PIPE)
    root.mkdir()
    for directory in ('protocol', 'bin', 'stages', 'logs', 'observations', 'provenance', 'qualification-outputs'):
        (root / directory).mkdir()
    try:
        for relative in ('generated-source-copies.json', 'protected-original-state.json',
                         'protected-untracked-state.json'):
            copy_new(BASIS / relative, root / 'provenance' / ('basis-' + relative))
        copy_new(BASIS / 'generated-source-copies.json', root / 'generated-source-copies.json')
        binaries = {}
        for variant, source in (('C', CAMPAIGN / 'control-bin'), ('N', candidate_dir)):
            for binary in ('bsc', 'rescript'):
                if variant == 'C' and inputs.sha(source / binary) != CONTROL_HASHES[binary]:
                    raise RuntimeError('normal control binary changed: ' + binary)
                target = root / 'bin' / (binary + '-' + variant)
                copy_new(source / binary, target)
                binaries[binary + '-' + variant] = str(target.relative_to(root))
        protected = {}
        original_generated = inputs.load(BASIS / 'protected-original-state.json')
        original_untracked = inputs.load(BASIS / 'protected-untracked-state.json')['files']
        for relative, expected in original_generated.items():
            path = REPOS['tella'] / relative
            state = inputs.file_state(path)
            if state != {'exists': True, **expected}:
                raise RuntimeError('original generated state changed: ' + str(path))
            backup = root / 'backups/generated' / relative
            copy_new(path, backup)
            protected[str(path)] = {'kind': 'generated', 'state': state,
                                    'backup': str(backup.relative_to(root))}
        for i, (name, expected) in enumerate(original_untracked.items()):
            path = Path(name)
            state = inputs.file_state(path)
            if state != {'exists': True, **expected}:
                raise RuntimeError('original untracked state changed: ' + name)
            backup = root / 'backups/untracked' / str(i) / path.name
            copy_new(path, backup)
            protected[name] = {'kind': 'untracked', 'state': state,
                               'backup': str(backup.relative_to(root))}
        for name in ('package_missing_ml_dependency.mjs', 'package_script_dependency.mjs'):
            path = worktree / 'src' / name
            if path.is_file():
                state = inputs.file_state(path)
                backup = root / 'backups/working-fixtures' / name
                copy_new(path, backup)
                protected[str(path)] = {'kind': 'working_fixture', 'state': state,
                                        'backup': str(backup.relative_to(root))}
        supervisor.publish(root / 'protected.json', protected)
        plan = {
            'schema': 1, 'slots': measure.schedule(), 'repos': {name: str(path) for name, path in REPOS.items()},
            'binaries': binaries, 'hyperfine': '/opt/homebrew/bin/hyperfine',
            'control_source_head': '75d1ac49daf49ecf85009d8a4c7381643843bd4c',
            'candidate_source_head': candidate_head, 'workspace_head': inputs.git(worktree, 'rev-parse', 'HEAD').strip(),
            'required': {'project_modules': 3248, 'runtime_sources': 107, 'js_files': 5048,
                         'js_digest': measure.EXPECTED_JS},
            'acceptance_milestone': '>=10% lower mean full-clean parallel time; paired CI excludes no improvement',
            'serial': 'report separately; no historical or instrumented timing pooling',
            'correctness': 'no new regression; known syntax/AST0/native-external red or blocked gates remain unwaived',
            'runtime_proof': 'fresh CLI BuildCommandState/ModuleRegistry; mandatory source bootstrap before project scheduling; minimum runtime pool2 even projectw1',
            'lock': '/tmp/rescript-tella-heavy.lock',
            'limits_seconds': {'stage': 420, 'build': 180, 'hyperfine': 240, 'clean': 120},
            'no_retries_replacements_exclusions_extensions': True,
        }
        supervisor.publish(root / 'plan.json', plan)
        copy_new(CAMPAIGN / 'baseline-source.tar', root / 'provenance/control-source.tar')
        with (root / 'provenance/candidate-source.tar').open('xb') as stream:
            subprocess.run(['git', '-C', str(worktree), 'archive', candidate_head, 'compiler-rust', 'rewatch'],
                           stdout=stream, check=True)
        for name in ('type_payload_inputs.py', 'type_payload_supervisor.py', 'type_payload_measure.py',
                     'prepare_type_payload_measure.py', 'test_prepare_type_payload_measure.py',
                     'test_type_payload_measure.py', 'test_type_payload_supervisor.py'):
            copy_new(worktree / 'scripts' / name, root / 'protocol' / name)
        inventory = inputs.Inventory(root)
        inventory.verify_protected()
        baseline = inventory.snapshot()
        # Retain the first observation even if preparation validation fails.
        supervisor.publish(root / 'baseline.json', baseline)
        prior_path = BASIS / 'inventory-final.json'
        prior = inputs.load(prior_path)
        approval = inputs.load(baseline_delta) if baseline_delta is not None else None
        expected_count = approval['new_count'] if approval is not None else 42463
        if len(baseline['inputs']) != expected_count:
            raise RuntimeError('unexpected baseline input count: ' + str(len(baseline['inputs'])))
        if approval is not None:
            if inputs.sha(prior_path) != approval['prior_inventory_sha256']:
                raise RuntimeError('historical inventory basis changed')
            copy_new(Path(baseline_delta), root / 'provenance/approved-pre-cohort-delta.json')
        previous_inputs, _ = inputs.classify_copies(prior['inputs'], inventory.ledger)
        current_inputs, _ = inputs.classify_copies(baseline['inputs'], inventory.ledger)
        for path in inventory.metadata():
            previous_inputs.pop(path, None)
            current_inputs.pop(path, None)
        delta = [{'path': path, 'resolved': str(Path(path).resolve()),
                  'old': previous_inputs.get(path), 'new': current_inputs.get(path)}
                 for path in sorted(previous_inputs.keys() | current_inputs.keys())
                 if previous_inputs.get(path) != current_inputs.get(path)]
        if delta != (approval['rows'] if approval is not None else []):
            raise RuntimeError('inputs differ from the exact approved pre-cohort baseline delta')
        supervisor.publish(root / 'provenance/historical-input-delta.json', delta)
        verdict = inventory.compare(baseline, baseline, inventory.metadata(), True)
        if not verdict['valid']:
            raise RuntimeError('initial inventory verification failed: ' + repr(verdict))
        supervisor.publish(root / 'provenance/initial-verification.json', verdict)
        runtime = inventory.runtime_sources()
        if len(runtime) != 107:
            raise RuntimeError('runtime source count changed')
        supervisor.publish(root / 'runtime-sources.json', runtime)
        observed = inventory.outputs()
        if observed['count'] != 5048 or observed['sha256'] != measure.EXPECTED_JS:
            raise RuntimeError('initial JavaScript manifest changed')
        supervisor.publish(root / 'provenance/initial-js.json', observed)
        files = {str(path): inputs.sha(path) for path in root.rglob('*') if path.is_file()}
        for name, root_path in REPOS.items():
            if name != 'tella':
                for relative, digest in baseline['sources'][name].items():
                    files[str(root_path / relative)] = digest
        # Pin the actual runtime/tool bytes as well as their input manifests.
        files.update(runtime)
        files[plan['hyperfine']] = inputs.sha(plan['hyperfine'])
        supervisor.publish(root / 'seal.json', {'files': files})
        supervisor.publish(root / 'PREPARED_NOT_ADMITTED.json', {
            'seal_sha256': inputs.sha(root / 'seal.json'),
            'plan_sha256': inputs.sha(root / 'plan.json'),
            'next': 'independent parent review and admission; no workload has run',
        })
        return root
    except BaseException as exc:
        supervisor.publish(root / 'PREPARATION_FAILED.json', {'error': repr(exc), 'workload_launched': False})
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('name')
    parser.add_argument('--candidate-dir', type=Path, required=True)
    parser.add_argument('--candidate-head', required=True)
    parser.add_argument('--baseline-delta', type=Path)
    args = parser.parse_args()
    print(prepare(args.name, args.candidate_dir, args.candidate_head, args.baseline_delta))


if __name__ == '__main__':
    main()
