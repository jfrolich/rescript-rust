#!/usr/bin/env python3
"""Debug flags must affect tracing only, never marshaled AST bytes."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BSC = Path(os.environ.get("RUST_BSC", ROOT / "rewatch/target/release/bsc"))


class MarshalDebugFlags(unittest.TestCase):
    def test_debug_flags_preserve_ast_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "trace.res"
            source.write_text('let values = ("None", "Mic", "Camera")\n')
            base_env = os.environ.copy()
            for flag in ("DEBUG_MARSHAL", "DEBUG_CONST_SHARE"):
                base_env.pop(flag, None)
            baseline = None
            for index, flags in enumerate(({}, {"DEBUG_MARSHAL": ""},
                                           {"DEBUG_CONST_SHARE": "0"},
                                           {"DEBUG_MARSHAL": "1", "DEBUG_CONST_SHARE": "1"})):
                with self.subTest(flags=flags):
                    output = root / f"{index}.ast"
                    result = subprocess.run(
                        [str(BSC), "-bs-ast", "-o", str(output), str(source)],
                        env={**base_env, **flags}, capture_output=True, text=True, timeout=10,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    data = output.read_bytes()
                    if baseline is None:
                        baseline = data
                    self.assertEqual(data, baseline)
                    self.assertEqual("WRITE PosIdx(" in result.stderr, "DEBUG_MARSHAL" in flags)
                    self.assertEqual("WRITE LocIdx(" in result.stderr, "DEBUG_MARSHAL" in flags)
                    self.assertEqual("SHARE PosIdx(" in result.stderr, "DEBUG_MARSHAL" in flags)
                    self.assertEqual("CONST None " in result.stderr, "DEBUG_CONST_SHARE" in flags)


if __name__ == "__main__":
    unittest.main()
