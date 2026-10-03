/-
Dump every constant name visible after importing `Hagi`
(Hagi + Mathlib + core) to `scripts/namepool.txt`, one per line.
Consumed by `scripts/DocLint.py` (rule 4: docstring names must exist).
Run: lake env lean --run scripts/NamePool.lean
-/
import Lean
open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Hagi }] ∅ (trustLevel := 4)
  let out ← IO.FS.Handle.mk "scripts/namepool.txt" .write
  env.constants.forM fun n _ => out.putStrLn n.toString
