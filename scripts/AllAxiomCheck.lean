/-
AllAxiomCheck v2 (аудит №5 H3, оптимизация такта №283):
аксиоматические зависимости ВСЕХ Hagi.*-теорем.

v1 (collectAxioms per-const) — 19 мин (транзитивный обход
заново для каждой из 5463 теорем). v2: ЕДИНЫЙ обход графа
зависимостей с visited-set — каждая константа посещается
один раз, O(V+E): на порядок быстрее.

Запуск: lake env lean --run scripts/AllAxiomCheck.lean
Маркер: ALLAXIOMS: PASS/FAIL (последняя строка).
-/
import Hagi
import Lean

open Lean

namespace AllAxiomCheck

def allowed : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

/-- Единый обход: getUsedConstants (ядро, быстрый) на
type+value каждой константы; visited-HashMap: каждая
константа обрабатывается один раз. -/
def collectAll (env : Environment) : IO (Array Name × Nat) := do
  let mut seeds : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    let userName := privateToUserName? nm |>.getD nm
    if (`Hagi).isPrefixOf userName && ci.isTheorem then
      seeds := seeds.push nm
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
  let env ← importModules #[{ module := `Hagi }] ∅ (trustLevel := 1024)
  let (axs, nTh) ← collectAll env
  let bad := axs.filter (fun a => !(allowed.contains a))
  IO.println s!"transitive axioms of all {nTh} Hagi.* theorems:"
  for a in axs do
    IO.println s!"  {a}"
  if bad.isEmpty then
    IO.println "ALLAXIOMS: PASS"
  else
    IO.println s!"ALLAXIOMS: FAIL ({bad.size} nonstandard)"

end AllAxiomCheck

open AllAxiomCheck

unsafe def main : IO Unit := AllAxiomCheck.main
