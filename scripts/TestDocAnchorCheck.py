#!/usr/bin/env python3
"""Regression tests for the doc-anchor gate (scripts/DocAnchorCheck.py)."""
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import DocAnchorCheck as D  # noqa: E402

WATER = "Water line one.\nWater line two.\nWater line three.\nWater line four.\n"
# line:      1          2             3                 4          5        6     7
OLD = """import Mathlib.Tactic

namespace Hagi.Probe

/-- First theorem. -/
theorem first (n : ℕ) : n + 0 = n := by
  omega

/-- Water.
""" + WATER + """-/
def second : ℕ := 2

/-! ## Section header -/

/-- Docstring of third. -/
theorem third : True := trivial

/-- `structure` after the closer on the same line.
-/ structure Fourth where
  x : ℕ

end Hagi.Probe
"""
# OLD: first 5-8, second 9-16 (doc 9, def 15), header 17, third 19-21 (doc 19, theorem 20),
#      Fourth doc 22, `-/ structure Fourth` 23
NEW = OLD.replace(WATER, "").replace("/-! ## Section header -/\n\n", "")
# NEW: second 9-12 (def 11), third 13-15 (doc 13, theorem 14), Fourth 16 (decl 17)


class Chunks(unittest.TestCase):
    def test_docstring_joins_declaration(self):
        cs = D.chunks(OLD.split("\n"))
        got = [(c.start, c.doc, c.decl, c.name) for c in cs
               if c.name and not c.name.startswith("§")]
        self.assertEqual(got, [(5, 5, 6, "first"), (9, 9, 15, "second"),
                               (19, 19, 20, "third"), (22, 22, 23, "Fourth")])

    def test_block_comment_depth(self):
        text = "/-\nCopyright\n-/\n\n/-- Doc. -/\ntheorem t : True := trivial\n"
        cs = D.chunks(text.split("\n"))
        self.assertEqual([c.name for c in cs if c.name], ["§/-", "t"])


class Reanchor(unittest.TestCase):
    """A docstring pass that deletes the water lines shifts `second` and `third`."""

    def land(self, n, new=None):
        t = D.aim(OLD.split("\n"), n)
        self.assertIsNotNone(t)
        with patch.object(D, "FILES", []):
            return D.landing((new or NEW).split("\n"), t, "Hagi/Probe.lean")[1:]

    def test_keyword_line_keeps_role(self):
        self.assertEqual(self.land(15), (11, "decl"))        # `def second`
        self.assertEqual(self.land(20), (14, "decl"))        # `theorem third`

    def test_docstring_opener_keeps_role(self):
        self.assertEqual(self.land(9), (9, "doc"))
        self.assertEqual(self.land(19), (13, "doc"))

    def test_inner_line_without_text_falls_back_to_opener(self):
        self.assertEqual(self.land(12), (9, "coarsened"))    # deleted water line

    def test_inner_line_with_unique_text_keeps_line(self):
        self.assertEqual(self.land(7), (7, "text"))          # `omega`

    def test_last_line_keeps_role(self):
        self.assertEqual(self.land(8), (8, "end"))

    def test_deleted_header_lands_on_its_first_declaration(self):
        self.assertEqual(self.land(17), (13, "header->decl"))

    def test_closer_plus_declaration(self):
        self.assertEqual(self.land(22), (16, "doc"))
        self.assertEqual(self.land(23), (17, "decl"))

    def test_declaration_lost(self):
        gone = NEW.replace("theorem first (n : ℕ) : n + 0 = n := by\n  omega\n\n", "")
        self.assertEqual(self.land(6, gone), (None, "NAME-LOST"))


class Scan(unittest.TestCase):
    BASE = {"Probe.lean": ["Hagi/Theory/Probe.lean"]}

    def occ(self, line):
        D.PROBLEM.clear()
        return [(f, n, n2) for _, _, _, f, n, n2 in D.scan("d.md", [line], self.BASE)]

    def test_full_short_and_continuation(self):
        self.assertEqual(self.occ("Hagi/Theory/Probe.lean:12, :14-16; Probe.lean:20 (:22)"),
                         [("Hagi/Theory/Probe.lean", 12, None), ("Hagi/Theory/Probe.lean", 14, "16"),
                          ("Hagi/Theory/Probe.lean", 20, None), ("Hagi/Theory/Probe.lean", 22, None)])

    def test_foreign_anchor_is_not_a_continuation(self):
        self.assertEqual(self.occ("Hagi/Theory/Probe.lean:12 | lm.py:1314, :1323-1324"),
                         [("Hagi/Theory/Probe.lean", 12, None)])
        self.assertEqual(self.occ("Probe.lean:117, :132 | :390-440"),
                         [("Hagi/Theory/Probe.lean", 117, None), ("Hagi/Theory/Probe.lean", 132, None)])

    def test_dash_range_is_one_anchor(self):
        self.assertEqual(self.occ("Hagi/Theory/Probe.lean:458–:541"),
                         [("Hagi/Theory/Probe.lean", 458, "541")])

    def test_ambiguous_short_form_is_reported(self):
        D.PROBLEM.clear()
        D.scan("d.md", ["Probe.lean:12 and Other.lean:3"],
               {"Probe.lean": ["Hagi/A/Probe.lean", "Hagi/B/Probe.lean"]})
        self.assertEqual(len(D.PROBLEM), 2)      # both short forms are unknown


if __name__ == "__main__":
    unittest.main()
