/-
Semantic declaration inventory for Freeze and human refactors.

For every declaration owned by a Hagi.* module, emit its actual fully
qualified name, private-name user form, defining module, source ranges,
elaborated type, constructor/projection names and Batteries-alias marker.
Proof bodies are deliberately excluded. A compatibility alias remains tracked

Run: lake env lean scripts/inventory.lean > inventory.txt
-/
import Hagi
import Hagi.Legacy
import Batteries.Tactic.Alias
open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  for (sourceModule, moduleData) in env.header.moduleNames.zip env.header.moduleData do
    if (`Hagi).isPrefixOf sourceModule then
      for (n, ci) in moduleData.constNames.zip moduleData.constants do
        let userName := (privateToUserName? n).getD n
        let isAlias := (← Batteries.Tactic.Alias.getAliasInfo? n).isSome
        let (startLine, selectionLine, endLine) := match (declRangeExt.find? (level := .exported) env n).orElse
            (fun _ => declRangeExt.find? (level := .server) env n) with
          | some ranges => (ranges.range.pos.line, ranges.selectionRange.pos.line,
              ranges.range.endPos.line)
          | none => (0, 0, 0)
        let mut constructorMetadata : List String := []
        if let .inductInfo info := ci then
          for constructor in info.ctors do
            let some constructorInfo := env.find? constructor
              | throwError "missing constructor {constructor} of {n}"
            constructorMetadata := constructorMetadata ++ [s!"{constructor}={constructorInfo.type.hash}"]
        if let some structureInfo := getStructureInfo? env n then
          constructorMetadata := constructorMetadata ++ ["fields=" ++
            String.intercalate "," (structureInfo.fieldNames.toList.map (·.toString))]
          for field in structureInfo.fieldInfo do
            constructorMetadata := constructorMetadata ++ [field.projFn.toString]
        IO.println s!"{n}\t{userName}\t{sourceModule}\t{startLine}\t{selectionLine}\t{endLine}\t{ci.type.hash}\t{String.intercalate "," constructorMetadata}\t{isAlias}"
