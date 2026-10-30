"""Check actual directory entries, including on case-insensitive filesystems."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class PackageOutputFilenames(unittest.TestCase):
    def test_package_filenames_match_native_in_normal_and_dump_modes(self):
        compilers = [Path(os.environ.get("OCAML_BSC", ROOT / "_build/install/default/bin/bsc")),
                     Path(os.environ.get("RUST_BSC", ROOT / "rewatch/target/release/bsc"))]
        for stem in ("lower_case", "mixedCase", "UpperCase"):
            for dump in (False, True):
                with self.subTest(stem=stem, dump=dump), tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    for index, compiler in enumerate(compilers):
                        directory = root / str(index)
                        directory.mkdir()
                        source = directory / f"{stem}.res"
                        source.write_text("let value = 1\n")
                        output = directory / "output"
                        output.mkdir()
                        args = [str(compiler), "-nopervasives", "-bs-project-root", str(directory),
                                "-bs-package-name", "filename-test",
                                "-bs-package-output", "esmodule:output:.mjs"]
                        if dump:
                            args.append("-dlambda-sexp")
                        args.append(str(source))
                        env = dict(os.environ, RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"))
                        result = subprocess.run(args, cwd=directory, env=env,
                                                capture_output=True, text=True, timeout=10)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(sorted(p.name for p in output.iterdir()), [f"{stem}.mjs"])
                    self.assertEqual((root / "0/output" / f"{stem}.mjs").read_bytes(),
                                     (root / "1/output" / f"{stem}.mjs").read_bytes())


if __name__ == "__main__":
    unittest.main()
