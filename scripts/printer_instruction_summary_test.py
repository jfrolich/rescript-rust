"""Self-attribution must account for every instruction without double counting."""
import unittest
from printer_instruction_summary import category, parse_profile, callgrind_phases


class SummaryTests(unittest.TestCase):
    def test_import_and_bir_view_are_separate(self):
        self.assertEqual(category("rescript_compiler::bir::bridge_j::import_js"), "Bir support / import (named self)")
        self.assertEqual(category("<rescript_compiler::bir::emit_view::EmitterView>::ek"), "Other emitter")
        self.assertEqual(category("rescript_compiler::emit::bir_naming::Names::collect"), "Naming")

    def test_complete_self_accounting(self):
        result = parse_profile("""
events: Ir
fl=source.rs
fn=rescript_compiler::emit::build::Build::expr
10 400
fn=oxc_codegen::Codegen::build
20 300
fn=rescript_compiler::bir::bridge_j::import_js
30 200
fl=???
fn=???
0 100
summary: 1000
""".splitlines())
        self.assertEqual(result["total"], 1000)
        self.assertEqual(result["self_instructions"]["AST construction / oxc arena"], 400)
        self.assertEqual(result["self_instructions"]["Unresolved"], 100)
        with self.assertRaisesRegex(ValueError, "sums to"):
            parse_profile(["events: Ir", "fn=f", "1 1", "summary: 2"])

    def test_repeated_function_names_are_disjoint_self_rows(self):
        result = parse_profile(["events: Ir", "fl=a", "fn=f", "1 7",
                                "fl=b", "fn=f", "2 8", "summary: 15"])
        self.assertEqual(result["self_instructions"]["Other compiler/runtime"], 15)
        with self.assertRaisesRegex(ValueError, "instruction-only"):
            parse_profile(["events: Ir Dr"])
        with self.assertRaisesRegex(ValueError, "nonzero"):
            parse_profile(["events: Ir", "fn=f", "1 1"])

    def test_inclusive_edges_do_not_double_count_inline_file_splits(self):
        profile = ["events: Ir", "summary: 30", "fn=(1) caller", "1 5",
                   "cfn=(2) rescript_compiler::bir::bridge_j::import_js", "calls=1 2", "* 25",
                   "fn=(2)", "2 10", "cfn=(2)", "calls=1 3", "* 15",
                   "fl=(9) inline.rs", "fn=(2)", "3 15"]
        result = callgrind_phases(profile)
        self.assertEqual(result["total"], 30)
        self.assertEqual(result["inclusive_instructions"]["import"], 25)
        with self.assertRaisesRegex(ValueError, "sum to"):
            callgrind_phases(profile[:-1])

    def test_shared_allocations_are_not_claimed_as_import(self):
        self.assertEqual(category("alloc::vec::Vec::grow"), "Shared allocation / containers")
        self.assertEqual(category("rescript_compiler::driver::compile"), "Other compiler/runtime")


if __name__ == "__main__":
    unittest.main()
