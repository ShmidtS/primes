import Hagi
import Lean

/-
Machine inventory of explicit named formal parameters in Hagi's root environment.
The input is elaborated declarations, not text, source comments or docstrings.
The JSON is consumed by AssumptionScan.py; this file proves no Hagi theorem.
-/

open Lean
open Lean.Meta

namespace AssumptionBinders

/-- Source module, reused from the existing checked TrivialLint helper. -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "?"

/-- Canonical finite-real information primitives from cycle 67. -/
def canonicalInfoDefs : List Name :=
  [`Hagi.Prelude.klDef, `Hagi.Prelude.ceDef, `Hagi.Prelude.entDef,
   `Hagi.Prelude.tvDef, `Hagi.Prelude.softDef]

/-- Existing other definitions whose treatment is deliberately explicit.
Raw entropy/prefix matching is not a sufficient domain classifier. -/
def informationCandidates : List Name :=
  [`Hagi.Core.lse, `Hagi.Core.softmaxP,
   `Hagi.Energy.entropyProduction,
   `Hagi.Information.entropy, `Hagi.Information.shannon,
   `Hagi.Information.tvHalf, `Hagi.Step.sourceEntropy,
   `Hagi.Data.softmaxW,
   `Hagi.Omni.entryCount]

def isEmpirical (n : Name) : Bool :=
  n.toString.startsWith "h_emp_"

def isNamedHypothesis (n : Name) : Bool :=
  n.toString.startsWith "h"

def isExecutionCandidate (n : Name) : Bool :=
  let name := n.toString.toLower
  name.contains "exec" || name.contains "descent" || name.contains "sample"

def isNamedHEMPDecl (n : Name) : Bool :=
  (n.toString.splitOn ".").any fun part => part.startsWith "h_emp_"

def declKind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | _ => "other"

def jsonRow (fields : List (String × Json)) : String :=
  (Json.mkObj fields).compress

/-- Check the real telescope of a known declaration, not textual context. -/
def checkTakeoffRegression (env : Environment) : MetaM Unit := do
  let some ci := env.find? `Hagi.Unified.state_capability_takeoff
    | throwError "missing state_capability_takeoff"
  forallTelescope ci.type fun localBinders _ => do
    let mut actual : List Name := []
    for localBinder in localBinders do
      let declaration ← getFVarLocalDecl localBinder
      if isEmpirical declaration.userName then
        actual := actual ++ [declaration.userName]
    let expected : List Name :=
      [`h_emp_cone0, `h_emp_gain_prod, `h_emp_dyn,
       `h_emp_C_cap, `h_emp_beta]
    if actual != expected then
      throwError "unexpected state_takeoff binder list: {actual}"

#eval show MetaM Unit from do
  let env ← getEnv
  checkTakeoffRegression env
  IO.println (jsonRow [("kind", "header"), ("format", "v2"),
    ("root", "Hagi"), ("binder_source", "Lean.Environment.forallTelescope")])
  for (name, ci) in env.constants.toList do
    if name.toString.startsWith "Hagi" then
      let sourceModule := moduleOf env name
      if isNamedHEMPDecl name then
        let type ← ppExpr ci.type
        IO.println (jsonRow [("kind", "declaration"),
          ("module", sourceModule), ("declaration", name.toString),
          ("declaration_kind", declKind ci), ("type", type.pretty 120)])
      if canonicalInfoDefs.contains name || informationCandidates.contains name then
        unless ci.isDefinition do
          throwError "primitive candidate is not a definition: {name}"
        IO.println (jsonRow [("kind", "primitive_candidate"),
          ("module", sourceModule), ("declaration", name.toString),
          ("declaration_kind", declKind ci)])
      forallTelescope ci.type fun localBinders _ => do
        let mut ordinal := 1
        for localBinder in localBinders do
          let localBinderDeclaration ← getFVarLocalDecl localBinder
          let binderName := localBinderDeclaration.userName
          if isNamedHypothesis binderName then
            let type ← ppExpr localBinderDeclaration.type
            let className := if isEmpirical binderName then "empirical" else "structural"
            IO.println (jsonRow [("kind", className),
              ("module", sourceModule), ("declaration", name.toString),
              ("declaration_kind", declKind ci),
              ("ordinal", toJson ordinal), ("binder", binderName.toString),
              ("type", type.pretty 120),
              ("execution_name_candidate", toJson (isExecutionCandidate binderName))])
          ordinal := ordinal + 1

end AssumptionBinders
