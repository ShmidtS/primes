#!/usr/bin/env python3
"""Execution-grounded regressions for the real axiom traversal.

The original failure was a forbidden axiom hidden in an `opaque` value:
the traversal missed it.  The fixture is appended to the actual scanner
source and evaluated in its frontend environment, not a copy of collectAll.
All custom axioms/sorries exist only in ignored .tmp probe files.  The
production Hagi environment remains free of these declarations.
"""

from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]


_BAD_FIXTURE = r'''
namespace Hagi.AxiomRegression
axiom direct_forbidden : False
theorem direct_witness : False := direct_forbidden

axiom def_forbidden : False
def def_hidden : False := def_forbidden
theorem def_witness : False := def_hidden

axiom opaque_forbidden : False
opaque opaque_hidden : False := opaque_forbidden
theorem opaque_witness : False := opaque_hidden

theorem sorry_witness : False := by sorry
end Hagi.AxiomRegression

open Lean Elab Command in
run_cmd do
  let (axs, _) ← unsafe AllAxiomCheck.collectAll (← getEnv)
  let expect := [
    (`Hagi.AxiomRegression.direct_forbidden, "DIRECT_AXIOM: PASS"),
    (`Hagi.AxiomRegression.def_forbidden, "DEFINITION_AXIOM: PASS"),
    (`Hagi.AxiomRegression.opaque_forbidden, "OPAQUE_AXIOM: PASS"),
    (`sorryAx, "SORRY_AXIOM: PASS")]
  for (nm, tag) in expect do
    if axs.contains nm then
      logInfo tag
    else
      throwError "{tag} -- FAILED: missed {nm}"
'''


_ALLOWED_FIXTURE = r'''
namespace Hagi.AllowedAxiomRegression
theorem excluded_middle (p : Prop) : p ∨ ¬p := Classical.em p
end Hagi.AllowedAxiomRegression

open Lean Elab Command in
run_cmd do
  let (axs, _) ← unsafe AllAxiomCheck.collectAll (← getEnv)
  if axs.toList.all (fun a => AllAxiomCheck.allowed.contains a) then
    logInfo "ALLOWED_AXIOMS: PASS"
  else
    throwError "ALLOWED_AXIOMS: FAIL {axs.toList}"
'''


class TestAllAxiomCheck(unittest.TestCase):
    """Compile the production source with deliberate ignored fixtures."""

    def runProbe(self, tag: str, fixture: str, markers: tuple[str, ...]) -> None:
        source = (ROOT / "scripts" / "AllAxiomCheck.lean").read_text(encoding="utf-8")
        probe_dir = ROOT / ".tmp"
        probe_dir.mkdir(exist_ok=True)
        probe = probe_dir / f"axiom-check-{tag}.lean"
        probe.write_text(source + fixture, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe.relative_to(ROOT))],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=180,
        )
        self.assertEqual(result.returncode, 0, result.stdout)
        for marker in markers:
            self.assertIn(marker, result.stdout)

    def test_all_dependency_classes(self) -> None:
        # Root causes are asserted by actual kernel dependency collection.
        self.runProbe(
            "classes",
            _BAD_FIXTURE,
            (
                "DIRECT_AXIOM: PASS",
                "DEFINITION_AXIOM: PASS",
                "OPAQUE_AXIOM: PASS",
                "SORRY_AXIOM: PASS",
            ),
        )

    def test_allowed_base_axioms(self) -> None:
        self.runProbe("allowed", _ALLOWED_FIXTURE, ("ALLOWED_AXIOMS: PASS",))


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestAllAxiomCheck)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)
    print("ALLAXIOMS: REGRESSION PASS")
