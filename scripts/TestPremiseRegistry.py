#!/usr/bin/env python3
"""Regression tests for the typed premise registry (C361 step 2.2)."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import AssumptionScan
import PremiseRegistry


def scan_of(hmap=None, proven=(), operational=()):
    return (dict(hmap or {}), [], set(proven), set(operational))


class PremiseRegistryRegression(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory(prefix="premise-reg-")
        self.addCleanup(self.tempdir.cleanup)

    def write_toml(self, text):
        path = Path(self.tempdir.name) / "reg.toml"
        path.write_text(text, encoding="utf-8")
        return path

    def test_real_registry_passes_and_covers_every_scanned_name(self):
        problems, stats = PremiseRegistry.validate()
        self.assertEqual(problems, [])
        self.assertEqual(sum(stats.values()), 60)
        # every enum type is represented
        for t in PremiseRegistry.TYPES:
            self.assertIn(t, stats)

    def test_unknown_name_fails(self):
        # a fresh scan discovers a NEW h_emp binder not in the registry
        scan = scan_of({"Hagi/Probe.lean": ["h_emp_known", "h_emp_new"]},
                       proven=set(),
                       operational=set())
        problems, _ = PremiseRegistry.validate(scan_result=scan, data={
            "premises": {
                "h_emp_known": {"type": "empirical", "measured": "x"},
            }})
        self.assertTrue(any("h_emp_new" in p for p in problems))
        self.assertTrue(any("unclassified" in p for p in problems))

    def test_unknown_operational_and_unprefixed_fail(self):
        scan = scan_of({"Hagi/Probe.lean": []},
                       operational={"hexec"},
                       proven=set())
        with patch.object(AssumptionScan, "UNPREFIXED_EMPIRICAL",
                          {"Hagi/Probe.lean": {"h_quiet": 1}}):
            problems, _ = PremiseRegistry.validate(scan_result=scan, data={
                "premises": {
                    "hexec": {"type": "operational"},
                }})
        self.assertTrue(any("hexec" not in p and "h_quiet" in p
                            for p in problems))
        self.assertTrue(any("unprefixed" in p for p in problems))

    def test_stale_entry_fails(self):
        scan = scan_of({"Hagi/Probe.lean": ["h_emp_live"]},
                       proven=set(), operational=set())
        problems, _ = PremiseRegistry.validate(scan_result=scan, data={
            "premises": {
                "h_emp_live": {"type": "model"},
                "h_emp_ghost": {"type": "model"},
            }})
        self.assertTrue(any("h_emp_ghost" in p and "stale" in p
                            for p in problems))

    def test_proven_theorem_is_not_a_required_premise(self):
        scan = scan_of({"Hagi/Probe.lean": ["h_emp_thm", "h_emp_binder"]},
                       proven={"h_emp_thm"},
                       operational=set())
        with patch.object(AssumptionScan, "UNPREFIXED_EMPIRICAL", {}):
            problems, _ = PremiseRegistry.validate(scan_result=scan, data={
                "premises": {
                    "h_emp_binder": {"type": "model"},
                }})
        self.assertEqual(problems, [])

    def test_invalid_type_enum_fails(self):
        path = self.write_toml(
            '[premises.h_x]\ntype = "statistical"\n')
        _data, problems = PremiseRegistry.load_registry(path)
        self.assertTrue(any("invalid type" in p for p in problems))

    def test_empirical_requires_measured(self):
        path = self.write_toml(
            '[premises.h_x]\ntype = "empirical"\nnote = "n"\n')
        _data, problems = PremiseRegistry.load_registry(path)
        self.assertTrue(any("measured" in p for p in problems))
        path2 = self.write_toml(
            '[premises.h_x]\ntype = "empirical"\nmeasured = "m"\n')
        _data, problems2 = PremiseRegistry.load_registry(path2)
        self.assertEqual(problems2, [])

    def test_unicode_and_prime_keys_parse(self):
        path = self.write_toml(
            '[premises."hβ"]\ntype = "model"\n'
            "[premises.\"hdescent'\"]\ntype = \"operational\"\n"
            '[premises."Hagi/A.lean::hβ"]\ntype = "empirical"\n'
            'measured = "m"\n')
        data, problems = PremiseRegistry.load_registry(path)
        self.assertEqual(problems, [])
        self.assertEqual(len(data["premises"]), 3)

    def test_status_enum_frozen(self):
        # 2.1 status vocabulary must stay stable (index generator
        # and audit language depend on it)
        self.assertEqual(PremiseRegistry.STATUS_ENUM,
                         ("Proven", "Conditional", "Empirical",
                          "Speculative", "Deprecated"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
