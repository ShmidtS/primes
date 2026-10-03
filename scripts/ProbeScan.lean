import Lean
open Lean

/-- Diagnostic: where do imported `Hagi` constants actually live after
`importModules`? Counts theorem declarations via `SMap.fold` (both stages). -/
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Hagi }] ∅ (trustLevel := 4)
  IO.println s!"moduleNames: {env.header.moduleNames.size}"
  let init : Nat × Nat × Nat × Array Name := (0, 0, 0, #[])
  let (total, thms, hagiThms, sample) :=
    env.constants.fold (init := init)
      (fun (t, th, hh, s) n info =>
        match info with
        | .thmInfo _ =>
          if (n.replacePrefix `_private Name.anonymous).getRoot == `Hagi then
            (t + 1, th + 1, hh + 1, if s.size < 10 then s.push n else s)
          else
            (t + 1, th + 1, hh, s)
        | _ => (t + 1, th, hh, s))
  IO.println s!"total constants: {total}"
  IO.println s!"thmInfo: {thms}"
  IO.println s!"Hagi-root theorems: {hagiThms}"
  IO.println s!"sample: {sample}"
