/-
AllAxiomCheck (аудит №5 H3): аксиоматические зависимости
ВСЕХ публичных констант Hagi.*, а не только 21 capstone.

Метапрограмма: итерирует окружение, для каждой константы в
namespace Hagi.* выполняет collectAxioms; нестандартные
аксиомы (вне {propext, Classical.choice, Quot.sound})
флагаются. Печатает ALLAXIOMS: PASS/FAIL (последняя строка —
машиночитаемый маркер для CI).

Запуск: lake env lean --run scripts/AllAxiomCheck.lean
-/
import Hagi
import Lean.Util.CollectAxioms
import Lean.Util.Path

open Lean Lean.Meta Core

namespace AllAxiomCheck

def allowed : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

end AllAxiomCheck

open AllAxiomCheck

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Hagi }] ∅ (trustLevel := 1024)
  let ctx : Core.Context :=
    { fileName := "<AllAxiomCheck>", options := {}, fileMap := default }
  let state : Core.State := { env := env }
  let (summary, _, _) ← (MetaM.toIO · ctx state) do
    let mut bad : Array (Name × Array Name) := #[]
    let mut total := 0
    let mut ok := 0
    for (nm, ci) in env.constants.toList do
      if nm.toString.startsWith "Hagi" then
        match ci with
        | .thmInfo _ =>
          total := total + 1
          let axs ← collectAxioms nm
          let bads := Array.filter (fun a => !(allowed.contains a)) axs
          if bads.isEmpty then
            ok := ok + 1
          else
            bad := bad.push (nm, bads)
        | _ => pure ()
    let mut rep : String :=
      s!"checked {ok}/{total} theorems in Hagi.*"
    for (nm, bads) in bad do
      rep := rep ++ "
" ++ s!"BAD_AXIOMS | {nm} | {bads}"
    if bad.isEmpty then
      return rep ++ "
ALLAXIOMS: PASS"
    else
      return rep ++ "
ALLAXIOMS: FAIL"
  IO.println summary
