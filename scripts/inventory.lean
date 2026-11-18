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
import Hagi.Benchmarks
import Hagi.Research
/- C347: quarantined speculative growth modules (A14 QW7) stay
frozen-tracked though outside the root closure. -/
import Hagi.Growth.Takeoff
import Hagi.Growth.LinearCone
import Hagi.Growth.Saturation
import Hagi.Growth.Ceilings
import Hagi.Growth.RsiCriterion
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.SeedOnly
import Hagi.Growth.GainDecomposition
import Hagi.Growth.StateBinding
import Hagi.Growth.ChainUnification
import Hagi.Growth.RoundViability
import Hagi.Dynamics.GrowthBridge
import Batteries.Tactic.Alias
open Lean

namespace CanonPrivate

/- C406: canonical private-name hashing (move-invariant Freeze).

Private constants carry path-keyed internal names; any statement
referencing one in a type position bakes the defining-module path
into `Expr.hash`. Before hashing, every private `.const` is replaced
by the marker `⟦priv.<id>⟧` where `<id>` is a content-derived fixpoint
id (own user-name leaf + own normalized type). Self-references map to
`⟦priv.self⟧`. Types without private references hash exactly as
before, so unaffected statement-hashes are preserved by construction. -/

/- C415: alpha-invariant statement hashing.

Lean `Expr` is de Bruijn internally: bound variables are indices and
binder names are display-only annotations. `Expr.hash` happens to
ignore them, but that is an undocumented emergent property (Hyrum
risk: any future name-sensitive printer/fold re-opens the gap and
α-renamed duplicates slip past Freeze/STMDUP). `alphaCanonical`
makes α-invariance explicit by construction: every lam/forallE/letE
binder name is erased before hashing. Since the hash ignored names
already, all statement hashes are VALUE-UNCHANGED by this layer
(proven: old- vs new-scheme bake on identical tree -> byte-identical
8035-row lock).

Scope boundary: α-equivalence (binder renaming) is IN; defeq but
structurally different statements (`a+b` vs `b+a`) are OUT — proof-
reduction equality is undecidable to enumerate at hashing time.
BinderInfo differences were already ignored by `Expr.hash`; left
as-is (over-merge only, never a miss). -/

abbrev Markers := NameMap String

def replaceConst (ids : Markers) (self : Name) (e : Expr) : Option Expr :=
  if let .const name lvls := e then
    let marker :=
      if name == self then some "self"
      else ids.get? name
    match marker with
    | some m => some (.const (Name.mkSimple s!"⟦priv.{m}⟧") lvls)
    | none => none
  else none

/-- Erase binder names (lam/forallE/letE), recursing into all
subterms. Alpha-equivalent expressions become structurally equal. -/
partial def alphaCanonical (e : Expr) : Expr :=
  match e with
  | .app f a => .app (alphaCanonical f) (alphaCanonical a)
  | .lam _ t b bi => .lam Name.anonymous (alphaCanonical t) (alphaCanonical b) bi
  | .forallE _ t b bi => .forallE Name.anonymous (alphaCanonical t) (alphaCanonical b) bi
  | .letE _ t v b nd => .letE Name.anonymous (alphaCanonical t) (alphaCanonical v) (alphaCanonical b) nd
  | .mdata m e => .mdata m (alphaCanonical e)
  | .proj t i e => .proj t i (alphaCanonical e)
  | e => e

def canonHash (ids : Markers) (self : Name) (e : Expr) : UInt64 :=
  (alphaCanonical (e.replace (replaceConst ids self))).hash

def leafOf (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

def canonName (ids : Markers) (n : Name) : String :=
  match ids.get? n with
  | some m => s!"⟦priv.{m}⟧.{leafOf ((privateToUserName? n).getD n)}"
  | none => n.toString

end CanonPrivate

/- C415 fail-closed self-check: canonical hashing is alpha-invariant
(lam/forallE/letE binder renames collide) and still distinguishes
non-alpha-equivalent bodies. Throws on violation; runs on every
inventory invocation (i.e. every Freeze gate). -/
#eval show CoreM Unit from do
  let n : Expr := .const `Nat []
  let alphaPairs : List (Expr × Expr) :=
    [(.lam `x n (.bvar 0) .default, .lam `y n (.bvar 0) .default),
     (.forallE `x n (.bvar 0) .default, .forallE `y n (.bvar 0) .default),
     (.letE `x n (.bvar 0) (.bvar 0) true,
      .letE `y n (.bvar 0) (.bvar 0) true)]
  for (a, b) in alphaPairs do
    let ca := CanonPrivate.alphaCanonical a
    let cb := CanonPrivate.alphaCanonical b
    unless ca == cb && ca.hash == cb.hash do
      throwError "C415 self-check: alpha-equivalent pair split by canonical hash"
  let d1 : Expr := .forallE `x n (.bvar 0) .default
  let d2 : Expr := .forallE `x n (.app (.const `id [0]) (.bvar 0)) .default
  if CanonPrivate.alphaCanonical d1 == CanonPrivate.alphaCanonical d2
      || d1.hash == d2.hash then
    throwError "C415 self-check: non-alpha-equivalent pair collided"

#eval show CoreM Unit from do
  let env ← getEnv
  -- Pass 1: collect Hagi private constants (raw name -> elaborated type).
  let mut privTypes : NameMap Expr := {}
  for (sourceModule, moduleData) in env.header.moduleNames.zip env.header.moduleData do
    if (`Hagi).isPrefixOf sourceModule then
      for (n, ci) in moduleData.constNames.zip moduleData.constants do
        if (privateToUserName? n).isSome then
          privTypes := privTypes.insert n ci.type
  -- Pass 2: content-addressed fixpoint ids (leaf user name + normalized
  -- own type). Fails closed if mutual cycles prevent convergence.
  let limit := privTypes.size + 2
  let mut ids : CanonPrivate.Markers := {}
  let mut converged := false
  for _ in [0:limit] do
    let mut next : CanonPrivate.Markers := {}
    for (n, ty) in privTypes do
      let leaf := CanonPrivate.leafOf ((privateToUserName? n).getD n)
      next := next.insert n
        s!"{CanonPrivate.canonHash ids n ty}.{leaf}"
    let same := next.size == ids.size
      && next.toList.all (fun (k, v) => ids.get? k == some v)
    if same then
      converged := true
      break
    ids := next
  unless converged do
    throwError "private-id fixpoint did not converge ({privTypes.size} privates)"
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
            constructorMetadata := constructorMetadata ++
              [s!"{CanonPrivate.canonName ids constructor}={CanonPrivate.canonHash ids n constructorInfo.type}"]
        if let some structureInfo := getStructureInfo? env n then
          constructorMetadata := constructorMetadata ++ ["fields=" ++
            String.intercalate "," (structureInfo.fieldNames.toList.map (·.toString))]
          for field in structureInfo.fieldInfo do
            constructorMetadata := constructorMetadata ++ [CanonPrivate.canonName ids field.projFn]
        IO.println s!"{n}\t{userName}\t{sourceModule}\t{startLine}\t{selectionLine}\t{endLine}\t{CanonPrivate.canonHash ids n ci.type}\t{String.intercalate "," constructorMetadata}\t{isAlias}"
