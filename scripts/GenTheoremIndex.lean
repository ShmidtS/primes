/-
GenTheoremIndex (C361, audit step 2.1): per-module environment
census for the generated theorem index.

Emits TSV on stdout:
  MOD\ttheorems\tN
  MOD\tdefs\tN
  MOD\tnoncomputable\tNAME
  AXIOMS\t<found allowed axioms, comma-joined>\tOK|NONSTANDARD:<names>

Import set mirrors scripts/inventory.lean (root closure + C347
quarantined growth modules) so every Freeze-tracked module is
censused. The axiom traversal is the AllAxiomCheck v2 algorithm
(single pass over the dependency graph with a visited set); the
allowed set is the AllAxiomCheck whitelist
(propext / Classical.choice / Quot.sound).

Run: lake env lean --run scripts/GenTheoremIndex.lean
Consumer: scripts/GenTheoremIndex.py (writes
.omc/analysis/generated/theorem-index.md).
-/
import Hagi
import Hagi.Research.Legacy
import Hagi.Benchmarks
import Hagi.Research
import Hagi.Growth.Takeoff
import Hagi.Growth.LinearCone
import Hagi.Growth.Saturation
import Hagi.Growth.GainDecomposition
import Hagi.Growth.StateBinding
import Hagi.Dynamics.GrowthBridge
open Lean

def allowed : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- Single-pass axiom collection over ALL Hagi.* theorem seeds
(AllAxiomCheck v2 algorithm: getUsedConstants on type+value,
visited set, each constant visited once). -/
def collectAll (env : Environment) : IO (Array Name × Nat) := do
  let mut seeds : Array Name := #[]
  for (_n, ci) in env.constants.toList do
    if ci.isTheorem then
      seeds := seeds.push _n
  let mut visited : Std.HashMap Name Unit := {}
  let mut axioms : Array Name := #[]
  let mut stack : Array Name := seeds
  while h : stack.size > 0 do
    let nm := stack.back
    stack := stack.pop
    if visited.contains nm then
      continue
    visited := visited.insert nm ()
    match env.find? nm with
    | some (.axiomInfo _) => axioms := axioms.push nm
    | some ci =>
      let mut deps := ci.type.getUsedConstants
      match ci with
      | .thmInfo t => deps := deps ++ t.value.getUsedConstants
      | .defnInfo d => deps := deps ++ d.value.getUsedConstants
      | .opaqueInfo o => deps := deps ++ o.value.getUsedConstants
      | _ => pure ()
      for d in deps do
        unless visited.contains d do
          stack := stack.push d
    | none => pure ()
  return (axioms, seeds.size)

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let roots : Array Name := #[`Hagi, `Hagi.Research.Legacy, `Hagi.Benchmarks,
    `Hagi.Research, `Hagi.Growth.Takeoff, `Hagi.Growth.LinearCone,
    `Hagi.Growth.Saturation, `Hagi.Growth.GainDecomposition,
    `Hagi.Growth.StateBinding, `Hagi.Dynamics.GrowthBridge]
  let imports := roots.map (fun m => { module := m : Import })
  let env ← importModules imports ∅ (trustLevel := 1024)
  for (sourceModule, moduleData) in env.header.moduleNames.zip env.header.moduleData do
    if (`Hagi).isPrefixOf sourceModule then
      let mut theorems := 0
      let mut defs := 0
      let mut ncDefs : Array Name := #[]
      for (n, ci) in moduleData.constNames.zip moduleData.constants do
        let userName := (privateToUserName? n).getD n
        match ci with
        | .thmInfo _ => theorems := theorems + 1
        | .defnInfo _d =>
          defs := defs + 1
          if isNoncomputable env n then
            ncDefs := ncDefs.push userName
        | _ => pure ()
      IO.println s!"{sourceModule}\ttheorems\t{theorems}"
      IO.println s!"{sourceModule}\tdefs\t{defs}"
      for n in ncDefs do
        IO.println s!"{sourceModule}\tnoncomputable\t{n}"
  let (axs, _n) ← collectAll env
  let bad := axs.filter (fun a => !(allowed.contains a))
  let found := axs.filter (fun a => allowed.contains a)
  let marker := if bad.isEmpty then "OK"
                else "NONSTANDARD:" ++ ",".intercalate (bad.toList.map (·.toString))
  IO.println s!"AXIOMS\t{",".intercalate (found.toList.map (·.toString))}\t{marker}"
