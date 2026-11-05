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


if __name__ == "__main__":
    unittest.main()
