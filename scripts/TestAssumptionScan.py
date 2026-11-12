#!/usr/bin/env python3
"""Regression tests for comments versus actual empirical binders."""
import tempfile
import unittest
from pathlib import Path

import AssumptionScan


class CommentPremiseRegression(unittest.TestCase):
    def setUp(self):
        self.old_root = AssumptionScan.ROOT
        self.tempdir = tempfile.TemporaryDirectory(prefix="assumption-scan-")
        root = Path(self.tempdir.name)
        (root / "Hagi").mkdir()
        AssumptionScan.ROOT = root

    def tearDown(self):
        AssumptionScan.ROOT = self.old_root
        self.tempdir.cleanup()

    def write_probe(self, text):
        path = AssumptionScan.ROOT / "Hagi" / "Probe.lean"
        path.write_text(text, encoding="utf-8")
        hmap, _, proven, _ = AssumptionScan.scan()
        return hmap["Hagi/Probe.lean"], proven

    def test_docstrings_do_not_create_premise_binders(self):
        names, _ = self.write_probe('''/-! `h_emp_documented` is external prose. -/
example (h_emp_real : 0 = 0) : 0 = 0 := by rfl
''')
        self.assertEqual(names, ["h_emp_real"])

    def test_docstrings_do_not_create_proven_theorems(self):
        names, proven = self.write_probe('''/-!
theorem h_emp_documented (h_emp_fake : True) : True := by trivial
-/
theorem h_emp_proved (h_emp_input : True) : True := by trivial
''')
        self.assertEqual(names, ["h_emp_input", "h_emp_proved"])
        self.assertEqual(proven, {"h_emp_proved"})


    def test_nested_comments_hide_fake_binders_and_primitives(self):
        path = AssumptionScan.ROOT / "Hagi" / "Probe.lean"
        path.write_text('''/- outer /-
def klFake : Nat := 0
theorem h_emp_fake : True := by trivial
-/
''', encoding="utf-8")
        hmap, prims, proven, _ = AssumptionScan.scan()
        self.assertEqual(hmap, {})
        self.assertEqual(prims, [])
        self.assertEqual(proven, set())


    def write_operational_probe(self, text):
        path = AssumptionScan.ROOT / "Hagi" / "Probe.lean"
        path.write_text(text, encoding="utf-8")
        _, _, _, operational = AssumptionScan.scan()
        return operational

    def test_operational_regex_ignores_witness_substrings(self):
        operational = self.write_operational_probe('''
theorem ceQuantWitness_shortcutScales_eq_knownSample : True := by trivial
theorem ceQuantWitness_shortcutScales_strict_descent : True := by trivial
''')
        # Regression: a plain h followed later by Sample/Descent inside
        # an ordinary identifier is NOT an h-prefixed operational name.
        self.assertEqual(operational, set())

    def test_operational_regex_preserves_whole_identifier_prefixes(self):
        operational = self.write_operational_probe('''
example (h_exec_retry : True) (hActualDescent : True) : True := by trivial
example (h_sample_input' : True) : True := by trivial
''')
        self.assertEqual(operational,
                         {"h_exec_retry", "hActualDescent", "h_sample_input'"})
        report = AssumptionScan.registry({}, [], set(), operational)
        self.assertIn(
            "[operational]\nhActualDescent\nh_exec_retry\nh_sample_input'",
            report)


class UnprefixedEmpiricalRegistry(unittest.TestCase):
    """C218: per-file count registry (shrink-only, not a name-registry)."""

    def setUp(self):
        self.saved = dict(AssumptionScan.UNPREFIXED_EMPIRICAL)
        self.target = AssumptionScan.ROOT / "Hagi" / "Probe.lean"

    def tearDown(self):
        AssumptionScan.UNPREFIXED_EMPIRICAL = self.saved
        if self.target.exists():
            self.target.unlink()

    def test_baseline_check_passes_on_current_tree(self):
        self.assertEqual(AssumptionScan.unprefixed_check(), [])

    def test_shrink_is_detected(self):
        AssumptionScan.UNPREFIXED_EMPIRICAL = {
            "Hagi/Probe.lean": {"h_step": 2}}
        self.target.write_text(
            "theorem a (h_step : True) : True := h_step" + chr(10),
            encoding="utf-8")
        problems = AssumptionScan.unprefixed_check()
        self.assertTrue(any("h_step" in p and "shrink" in p
                            for p in problems), problems)

    def test_growth_is_detected(self):
        AssumptionScan.UNPREFIXED_EMPIRICAL = {
            "Hagi/Probe.lean": {"h_step": 1}}
        self.target.write_text(
            "theorem a (h_step : True) : True := h_step" + chr(10)
            + "theorem b (h_step : True) : True := h_step" + chr(10),
            encoding="utf-8")
        problems = AssumptionScan.unprefixed_check()
        self.assertTrue(any("h_step" in p and "GROWTH" in p
                            for p in problems), problems)

    def test_missing_file_is_stale(self):
        AssumptionScan.UNPREFIXED_EMPIRICAL = {
            "Hagi/DoesNotExist.lean": {"h_step": 1}}
        problems = AssumptionScan.unprefixed_check()
        self.assertTrue(any("file missing" in p for p in problems))


if __name__ == "__main__":
    unittest.main()
