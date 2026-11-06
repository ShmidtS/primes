#!/usr/bin/env python3
"""Regression tests for declaration preservation and statement hashing."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import Freeze
import StatusLint


def record(name, start=1, finish=1, end=1, private=False,
           type_hash="closed-type", constructors="", alias=False):
    """One parsed inventory record, with source range and Lean identity."""
    return (start, finish, end, name, private,
            type_hash + "|" + constructors, name, alias)


class FreezeRegression(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory(prefix="freeze-scan-")
        self.root = Path(self.tempdir.name) / "Hagi"
        self.root.mkdir()
        self.metadata = {}

    def tearDown(self):
        self.tempdir.cleanup()

    def collect(self, path="Probe.lean", text=None, semantic=False):
        if text is not None:
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        if semantic:
            with patch.object(Freeze, "semantic_types",
                              return_value=self.metadata):
                return Freeze.collect(self.root, semantic=True)
        return Freeze.collect(self.root, semantic=False)

    def test_comments_do_not_change_structure_hash(self):
        base = "structure S where\n  a : Nat\n  -- ordinary\n  b : Nat\n"
        plain = self.collect(text=base)
        nested = self.collect(text=base.replace(
            "-- ordinary", "/- outer /- inner -/ first -/\n  -- ordinary"))
        self.assertEqual(plain, nested)

    def test_terminal_structure_field_change_is_detected(self):
        base = "structure S where\n  a : Nat\n  b : Nat\n"
        before = self.collect(text=base)
        after = self.collect(text=base.replace("b : Nat", "b : Int"))
        _, _, changed, _ = Freeze.diff(before, after)
        self.assertEqual(changed, ["S"])

    def test_real_names_expose_deleted_namespace_collisions(self):
        self.metadata["Hagi/A.lean", "same"] = [record("A.same")]
        self.collect("A.lean", "theorem same : True := by trivial\n",
                     semantic=True)
        self.metadata["Hagi/B.lean", "same"] = [
            record("B.same", type_hash="another-closed-type")]
        rows = self.collect("B.lean",
                            "theorem same : True := by contradiction\n",
                            semantic=True)
        self.assertEqual({row[0] for row in rows}, {"A.same", "B.same"})
        (self.root / "A.lean").unlink()
        del self.metadata["Hagi/A.lean", "same"]
        lost, _, changed, _ = Freeze.diff(rows, self.collect(semantic=True))
        self.assertEqual(lost, ["A.same"])
        self.assertEqual(changed, [])

    def test_elaborated_types_and_constructor_types_are_hashed(self):
        self.metadata["Hagi/Probe.lean", "item"] = [
            record("Hagi.Probe.item", constructors="constructor")]
        before = self.collect(text="theorem item : True := by trivial\n",
                              semantic=True)
        self.collect(text="theorem item : True := by exact True.intro\n",
                     semantic=True)
        self.assertEqual(before, self.collect(semantic=True))
        self.metadata["Hagi/Probe.lean", "item"] = [
            record("Hagi.Probe.item")]
        without_constructor = self.collect(semantic=True)
        self.assertNotEqual(before[0][2], without_constructor[0][2])
        self.metadata["Hagi/Probe.lean", "item"] = [
            record("Hagi.Probe.item", type_hash="other-type")]
        _, _, changed, _ = Freeze.diff(before, self.collect(semantic=True))
        self.assertEqual(changed, ["Hagi.Probe.item"])

    def test_source_matching_is_fail_closed(self):
        text = "theorem original : True := by trivial\n"
        with self.assertRaisesRegex(RuntimeError, "found 0"):
            self.collect(text=text, semantic=True)
        self.metadata["Hagi/Probe.lean", "original"] = [
            record("Hagi.Probe.original"), record("Hagi.Probe.original")]
        with self.assertRaisesRegex(RuntimeError, "found 2"):
            self.collect(text=text, semantic=True)
        self.metadata["Hagi/Probe.lean", "original"] = [
            record("Hagi.Probe.original")]
        self.collect(text=text, semantic=True)

    def test_alias_target_type_and_marker_are_tracked(self):
        text = "theorem original : True := by trivial\nalias copy := original\n"
        self.metadata["Hagi/Probe.lean", "original"] = [
            record("Hagi.Probe.original")]
        self.metadata["Hagi/Probe.lean", "copy"] = [
            record("Hagi.Probe.copy", start=2, finish=2, end=2, alias=True)]
        before = self.collect(text=text, semantic=True)
        self.assertEqual([row[0] for row in before],
                         ["Hagi.Probe.copy", "Hagi.Probe.original"])
        self.assertEqual(before[0][3], "alias")
        self.metadata["Hagi/Probe.lean", "copy"] = [
            record("Hagi.Probe.copy", start=2, finish=2, end=2)]
        with self.assertRaisesRegex(RuntimeError, "Alias marker mismatch"):
            self.collect(text=text, semantic=True)
        self.metadata["Hagi/Probe.lean", "copy"] = [
            record("Hagi.Probe.copy", start=2, finish=2, end=2,
                   type_hash="wrong-target", alias=True)]
        after = self.collect(text=text, semantic=True)
        _, _, changed, _ = Freeze.diff(before, after)
        self.assertEqual(changed, ["Hagi.Probe.copy"])
        self.assertIn("gibbs_variational_floor", StatusLint.lean_names())

    def test_generated_api_and_anonymous_instances_are_tracked(self):
        repo = Path(__file__).resolve().parents[1]
        environment = Freeze.semantic_types()
        self.metadata = environment
        source = (repo / "Hagi/Unified/StepContract.lean").read_text(
            encoding="utf-8")
        before = self.collect("Unified/StepContract.lean", text=source,
                              semantic=True)
        parent_key = "Hagi/Unified/StepContract.lean", "StepContract"
        instance_key = ("Hagi/Unified/StepContract.lean",
                        "instZeroStepContract")
        instance_name = environment[instance_key][0][3]
        self.assertIn(instance_name, {row[0] for row in before})
        structure_payload = environment[parent_key][0][5]
        self.assertIn("StepContract.mk", structure_payload)
        self.assertIn("StepContract.decrease", structure_payload)

        def changed_payload(key, payload):
            changed_env = dict(environment)
            value = changed_env[key][0]
            changed_env[key] = [(*value[:5], payload, *value[6:])]
            return changed_env

        self.metadata = changed_payload(instance_key, "different-type|")
        after = self.collect("Unified/StepContract.lean", semantic=True)
        lost, _, changed, _ = Freeze.diff(before, after)
        self.assertEqual(lost, [])
        self.assertEqual(changed, [instance_name])

        type_hash, constructors = structure_payload.split("|", 1)
        self.metadata = changed_payload(parent_key,
            type_hash + "|" + constructors.replace(
                "decrease", "renamedDecrease"))
        renamed_source = source.replace("decrease : ℝ", "renamedDecrease : ℝ")
        after = self.collect("Unified/StepContract.lean",
                             text=renamed_source, semantic=True)
        _, _, changed, _ = Freeze.diff(before, after)
        self.assertEqual(changed, ["Hagi.Unified.StepCert.StepContract"])

        # Constructor names are public API too, even when their types match.
        self.metadata = environment
        before_rhs = self.collect("Unified/StepContract.lean", text=source,
                                  semantic=True)
        self.metadata = changed_payload(parent_key, structure_payload.replace(
            "StepContract.mk", "StepContract.renamedCtor"))
        after = self.collect("Unified/StepContract.lean", semantic=True)
        _, _, changed, _ = Freeze.diff(before_rhs, after)
        self.assertEqual(changed, ["Hagi.Unified.StepCert.StepContract"])

        self.metadata = environment
        percolation = (repo / "Hagi/Percolation/Site.lean").read_text(
            encoding="utf-8")
        rows = self.collect("Percolation/Site.lean", text=percolation,
                            semantic=True)
        self.assertIn("Hagi.Percolation.ThresholdSystem",
                      {row[0] for row in rows})

    def test_cli_uses_repository_root(self):
        repo = Path(__file__).resolve().parents[1]
        result = subprocess.run(
            [sys.executable, str(repo / "scripts/Freeze.py")],
            cwd=self.tempdir.name, capture_output=True, text=True, timeout=90)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse((self.root.parent / "declarations.lock").exists())

    def test_pure_rename_still_passes(self):
        old = self.collect(text="theorem before : True := by trivial\n")
        new = self.collect(text="theorem after : True := by trivial\n")
        lost, renamed, changed, added = Freeze.diff(old, new)
        self.assertEqual((lost, renamed, changed, added),
                         ([], ["before"], [], ["after"]))

    def test_statement_duplicate_check_uses_statement_hash_and_kind(self):
        lock = self.root.parent / "declarations.lock"
        lock.write_text("A.same\th_a\tduplicate\ttheorem\n"
                        "B.same\th_b\tduplicate\tlemma\n", encoding="utf-8")
        command = [sys.executable,
                   str(Path(__file__).with_name("StatementDupCheck.py"))]
        result = subprocess.run(command, cwd=self.root.parent,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("STMDUP: FAIL (1 groups)", result.stdout)
        lock.write_text("A.same\th_a\ttype_a\ttheorem\n"
                        "B.same\th_b\ttype_b\ttheorem\n"
                        "A.alias\th_a\ttype_a\talias\n", encoding="utf-8")
        result = subprocess.run(command, cwd=self.root.parent,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout)
        lock.write_text("A.same\th_a\ttype_a\ttheorem\textra\n",
                        encoding="utf-8")
        result = subprocess.run(command, cwd=self.root.parent,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1, result.stdout)

    def test_lexer_preserves_strings_and_qualified_unicode_names(self):
        text = 'def s : String := "/- -- not a comment -/"\n'
        self.assertEqual(Freeze.strip_comments(text), text)
        rows = self.collect(text="theorem t₁ : True := by trivial\n"
                                 "theorem IsProjection.foo : True := by trivial\n")
        self.assertEqual([row[0] for row in rows],
                         ["IsProjection.foo", "t₁"])
        self.metadata["Hagi/Probe.lean", "foo"] = [
            record("Hagi.Probe.IsProjection.foo")]
        rows = self.collect(text="theorem IsProjection.foo : True := by trivial\n",
                            semantic=True)
        self.assertEqual([row[0] for row in rows],
                         ["Hagi.Probe.IsProjection.foo"])


if __name__ == "__main__":
    unittest.main()
