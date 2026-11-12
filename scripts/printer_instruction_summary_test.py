"""Self-attribution must account for every instruction without double counting."""
import unittest
from printer_instruction_summary import category, parse_annotation


class SummaryTests(unittest.TestCase):
    def test_import_and_bir_view_are_separate(self):
        self.assertEqual(category("rescript_compiler::bir::bridge_j::import_js"), "J import (named self)")
        self.assertEqual(category("<rescript_compiler::bir::emit_view::EmitterView>::ek"), "Other emitter")
        self.assertEqual(category("rescript_compiler::emit::bir_naming::Names::collect"), "Naming")

    def test_complete_self_accounting(self):
        result = parse_annotation("""
Ir
1,000 PROGRAM TOTALS
  400 source.rs:rescript_compiler::emit::build::Build::expr
  300 source.rs:oxc_codegen::Codegen::build
  200 source.rs:rescript_compiler::bir::bridge_j::import_js
  100 ???:???
""", 1000)
        self.assertEqual(result["total"], 1000)
        self.assertEqual(result["self_instructions"]["AST construction / oxc arena"], 400)
        self.assertEqual(result["self_instructions"]["Unresolved"], 100)
        with self.assertRaisesRegex(ValueError, "sums to"):
            parse_annotation("1 source.rs:fn", 2)

    def test_shared_allocations_are_not_claimed_as_import(self):
        self.assertEqual(category("alloc::vec::Vec::grow"), "Shared allocation / containers")
        self.assertEqual(category("rescript_compiler::driver::compile"), "Other compiler/runtime")


if __name__ == "__main__":
    unittest.main()
