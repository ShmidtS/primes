/-
Inventory probe: dumps every Hagi.* declaration with a stable
type hash, so refactors can be verified losslessly
("only planned names disappear; all survivors keep their types").
Run: lake env lean scripts/inventory.lean > inventory.txt
-/
import Hagi
open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if (`Hagi).isPrefixOf n && !n.isInternal then
      out := out.push s!"{n} {ci.type.hash}"
  out := out.qsort (· < ·)
  for l in out do
    IO.println l
