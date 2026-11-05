#!/usr/bin/env python3
"""Environment/schema regressions, including the two original comment regressions."""
import copy
import io
import json
from contextlib import redirect_stdout
from types import SimpleNamespace
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import AssumptionScan


HEADER = {
    "kind": "header", "format": "v2", "root": "Hagi",
    "binder_source": "Lean.Environment.forallTelescope",
}


def primitive_rows():
    modules = {
        "Hagi.Prelude": "Hagi.Prelude.Info",
        "Hagi.Core": "Hagi.Core.Concat",
        "Hagi.Energy": "Hagi.Energy.EntropyProduction",
        "Hagi.Information": "Hagi.Information.DiscreteFannes",
        "Hagi.Omni": "Hagi.Omni.OmniState",
    }
    output = []
    for name in sorted(AssumptionScan.ALL_CURATED_PRIMITIVES):
        prefix, _ = name.rsplit(".", 1)
        if name == "Hagi.Step.sourceEntropy":
            module = "Hagi.Step.MDLThreeCurrency"
        elif name == "Hagi.Data.softmaxW":
            module = "Hagi.Step.Upgrades"
        else:
            module = modules[prefix]
        output.append({
            "kind": "primitive_candidate", "module": module,
            "declaration": name, "declaration_kind": "def",
        })
    return output


def empirical_row(name="h_emp_real", declaration="Hagi.Probe.concrete_proof",
                  ordinal=1, typ="P -> P"):
    return {
        "kind": "empirical", "module": "Hagi.Probe",
        "declaration": declaration, "declaration_kind": "theorem",
        "binder": name, "ordinal": ordinal, "type": typ,
        "execution_name_candidate": False,
    }


def metadata(*rows):
    return "\n".join(json.dumps(row) for row in [HEADER, *primitive_rows(), *rows])


class EnvPremiseRegressions(unittest.TestCase):
    def test_repeated_names_retained_across_declarations(self):
        text = AssumptionScan.registry(AssumptionScan.parse_inventory(metadata(
            empirical_row(declaration="Hagi.Probe.first"),
            empirical_row(declaration="Hagi.Probe.second"),
        )))
        self.assertIn("h_emp binder occurrences: 2", text)
        self.assertIn("h_emp declaration+ordinal keys: 2", text)
        self.assertIn("h_emp distinct binder labels: 1", text)

    def test_same_decl_same_name_different_ordinal(self):
        first = empirical_row(ordinal=1, typ="P")
        second = empirical_row(ordinal=2, typ="Q")
        text = AssumptionScan.registry(AssumptionScan.parse_inventory(metadata(first, second)))
        self.assertIn("h_emp binder occurrences: 2", text)
        self.assertIn(" | 1 | h_emp_real | P", text)
        self.assertIn(" | 2 | h_emp_real | Q", text)

    def test_named_declaration_keeps_declaration_and_binder_separate(self):
        name = "Hagi.Probe.h_emp_proved"
        decl = {
            "kind": "declaration", "module": "Hagi.Probe",
            "declaration": name, "declaration_kind": "theorem", "type": "True",
        }
        text = AssumptionScan.registry(AssumptionScan.parse_inventory(metadata(decl)))
        self.assertIn("[h_emp-named declaration records]", text)
        self.assertIn(name, text)
        self.assertIn("h_emp binder occurrences: 0", text)

    def test_execution_uses_whole_names_not_fragments(self):
        valid = {
            "kind": "structural", "module": "Hagi.Probe",
            "declaration": "Hagi.Probe.step", "declaration_kind": "theorem",
            "binder": "h_exec", "ordinal": 1, "type": "next S = step S",
            "execution_name_candidate": True,
        }
        rows = AssumptionScan.parse_inventory(metadata(valid))
        registry = AssumptionScan.registry(rows)
        self.assertIn("execution-name candidate occurrences: 1", registry)
        self.assertNotIn("hastic_safeqp_descent", registry)
        self.assertNotIn("hedule_descent", registry)
        self.assertNotIn("hes_exec", registry)
        self.assertNotIn("hine_actual_descent", registry)

    def test_entryCount_is_not_an_information_primitive(self):
        records = AssumptionScan.parse_inventory(metadata())
        text = AssumptionScan.registry(records)
        primitives = text.split("[information primitives]\n", 1)[1].split(
            "[excluded primitive candidates]", 1)[0]
        self.assertNotIn("entryCount", primitives)
        self.assertIn("matrix spectral entropy definitions: 1", text)
        self.assertIn("legacy named information definitions: 7", text)
        self.assertIn("excluded primitive candidates: 1", text)
        self.assertIn("index-counter, not entropy", text)

    def test_bad_json_or_documented_prose_fails_closed(self):
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory("not a JSON object")
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory(metadata({"kind": "prose", "name": "h_emp_fake"}))
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory("")
        bad = empirical_row(ordinal=True)
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory(metadata(bad))

    def test_missing_empirical_type_fails_closed(self):
        bad = empirical_row()
        del bad["type"]
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory(metadata(bad))


    def test_execution_marker_cannot_contradict_whole_name(self):
        bad = {
            "kind": "structural", "module": "Hagi.Probe",
            "declaration": "Hagi.Probe.example", "declaration_kind": "theorem",
            "binder": "h_value", "ordinal": 1, "type": "True",
            "execution_name_candidate": True,
        }
        with self.assertRaises(ValueError):
            AssumptionScan.parse_inventory(metadata(bad))

    def test_root_rebuild_precedes_inventory_generation(self):
        with patch.object(AssumptionScan, "run_checked", side_effect=["", metadata()]) as run:
            AssumptionScan.read_inventory()
        commands = [call.args[0] for call in run.call_args_list]
        self.assertEqual(commands, [
            ["lake", "build", "Hagi"],
            ["lake", "env", "lean", "scripts/AssumptionBinders.lean"],
        ])

    def test_missing_canonical_primitives_fail_closed(self):
        raw = "\n".join(json.dumps(row) for row in [HEADER, empirical_row()])
        with self.assertRaises(ValueError):
            AssumptionScan.registry(AssumptionScan.parse_inventory(raw))


    def test_missing_legacy_primitive_fails_closed(self):
        records = AssumptionScan.parse_inventory(metadata())
        records = [row for row in records
                   if row.get("declaration") != "Hagi.Step.sourceEntropy"]
        with self.assertRaisesRegex(ValueError, "curated information definitions missing"):
            AssumptionScan.registry(records)

    def test_nonzero_root_build_fails_main_without_lock(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lock_file = root / "assumptions.lock"
            failed_build = SimpleNamespace(
                returncode=17, stdout="root build failed", stderr="missing target")
            with (patch.object(AssumptionScan, "ROOT", root),
                  patch.object(AssumptionScan, "LOCK", lock_file),
                  patch.object(AssumptionScan.subprocess, "run",
                               return_value=failed_build) as invoke):
                output = io.StringIO()
                with redirect_stdout(output):
                    status = AssumptionScan.main()
            self.assertEqual(status, 1)
            self.assertIn("ASSUMPTIONSCAN: FAIL", output.getvalue())
            self.assertIn("command failed (17)", output.getvalue())
            self.assertFalse(lock_file.exists())
            self.assertEqual(
                (root / ".tmp/assumption-scan-root-build.stderr.log").read_text(
                    encoding="utf-8"), "missing target")
            invoke.assert_called_once()


class CommentPremiseRegression(unittest.TestCase):
    """The original docstring cases, now driven by typed inventory records."""

    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory(prefix="assumption-scan-")
        self.root = Path(self.tempdir.name)
        (self.root / "Hagi").mkdir()
        self.old_root = AssumptionScan.ROOT
        self.old_lock = AssumptionScan.LOCK
        AssumptionScan.ROOT = self.root
        AssumptionScan.LOCK = self.root / "assumptions.lock"

    def tearDown(self):
        AssumptionScan.ROOT = self.old_root
        AssumptionScan.LOCK = self.old_lock
        self.tempdir.cleanup()

    def write_probe(self, original):
        path = self.root / "Hagi" / "Probe.lean"
        path.write_text(original, encoding="utf-8")
        return path

    def run_registry(self, rows):
        good = copy.deepcopy(rows)
        with patch.object(AssumptionScan, "read_inventory", return_value=metadata(*good)):
            self.assertEqual(AssumptionScan.main(), 0)
        return AssumptionScan.LOCK.read_text(encoding="utf-8")

    def test_docstrings_do_not_create_premise_binders(self):
        probe = self.write_probe('''
/- `h_emp_documented` is only a docstring occurrence. -/
namespace Hagi.Probe
theorem concrete_proof (h_emp_real : 0 = 0) : 0 = 0 := by rfl
end Hagi.Probe
''')
        self.assertIn("h_emp_documented", probe.read_text(encoding="utf-8"))
        # The fake docstring remains in its source file, not the Lean type inventory.
        text = self.run_registry([
            empirical_row(typ="0 = 0, not a docstring-mentioned h_emp_fake")
        ])
        self.assertIn("h_emp binder occurrences: 1", text)
        self.assertIn(" | h_emp_real |", text)
        self.assertNotIn(" | h_emp_documented |", text)
        self.assertNotIn(" | h_emp_fake |", text)

    def test_docstrings_do_not_create_proven_theorems(self):
        self.write_probe('''
/-!
A comment mentioning theorem h_emp_documented and h_emp_fake.
-/
namespace Hagi.Probe
theorem h_emp_proved (h_emp_input : True) : True := by trivial
end Hagi.Probe
''')
        declaration = {
            "kind": "declaration", "module": "Hagi.Probe",
            "declaration": "Hagi.Probe.h_emp_proved",
            "declaration_kind": "theorem", "type": "True",
        }
        text = self.run_registry([
            empirical_row("h_emp_input", declaration="Hagi.Probe.h_emp_proved"),
            declaration,
        ])
        self.assertIn("h_emp-named declaration records: 1", text)
        self.assertIn("Hagi.Probe.h_emp_proved", text)
        self.assertIn(" | h_emp_input |", text)
        self.assertNotIn(" | h_emp_documented |", text)
        self.assertNotIn(" | h_emp_fake |", text)


if __name__ == "__main__":
    unittest.main()
