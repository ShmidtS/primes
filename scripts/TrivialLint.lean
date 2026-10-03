/-
Trivial-theorem linter for the `Hagi` namespace.

Run AFTER `lake build`:
  lake env lean --run scripts/TrivialLint.lean

Import strategy: the root aggregator module `Hagi` exists (E:/primes/Hagi.lean,
`lean_lib Hagi` with default globs), so this script imports it directly. If the
root module were absent, the fallback would be `import Hagi.Unified.MasterHAGI`
(the deepest aggregator); both bring the full `Hagi.*` environment.
`scripts/` is outside both `lean_lib`s (`Primes`, `Hagi`), so this file never
enters `lake build`.

Checks (only `ConstantInfo.thmInfo` declarations in namespace `Hagi.*`):
  TRIV_RFL    proof term (after `instantiateMVars`, head found by walking the
              `.app` spine via `Expr.getAppFn`) is the constant `Eq.refl` or
              `Iff.rfl` AND the conclusion is an `Eq`/`Iff` whose sides are
              syntactically identical (`Expr.equal`, NO `whnf`) — a pure
              tautology. If the sides differ syntactically, the `rfl` performed
              a definitional unfolding, which is legitimate and NOT flagged.
  TRIV_AEQ_A  conclusion is `Eq a a` with syntactically identical sides,
              regardless of the proof tactic used.
  TRIV_PREM   conclusion is syntactically equal (`Expr.equal`) to the type of
              one of the theorem's own ∀-premises (Pi chain unfolded).
  BAD_AXIOM   `Lean.collectAxioms` reports an axiom outside
              {`propext`, `Classical.choice`, `Quot.sound`}; `sorryAx` included.

Output: summary counts per flag, then `flag | decl | module:line | detail` lines.
Exit code: `lean --run` does not reliably forward the script's exit code, so the
LAST output line is the machine-readable marker `LINT: PASS` / `LINT: FAIL`;
CI should check that marker. `IO.Process.exit 1` is still issued for callers
that do honor exit codes.
-/

import Hagi
import Lean.Util.Recognizers
import Lean.Util.CollectAxioms
import Lean.DeclarationRange
import Lean.Util.Path

open Lean Lean.Meta

namespace TrivialLint

/-- Axioms accepted as benign; anything else (including `sorryAx`) is flagged. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- One linter finding. -/
structure Finding where
  flag : String
  decl : Name
  detail : String

/-- Strip the `_private.<module>.0` prefix so namespace tests see the real root. -/
def normalizeName (n : Name) : Name :=
  n.replacePrefix `_private Name.anonymous

/-- Is this declaration inside the `Hagi.*` namespace? -/
def inHagi (n : Name) : Bool :=
  (normalizeName n).getRoot == `Hagi

/-- Head constant of an application spine (handles `@Eq.refl α h` etc.);
`none` if not a const. Note the elaborated `rfl` term IS `rfl.{u}` applied to
`(α, a)`, whose head constant is `rfl` itself (an abbreviation unfolding to
`Eq.refl`), so both names are accepted below. -/
def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

/-- Is this proof-head a reflexivity proof (`Eq.refl` or its abbreviation `rfl`)? -/
def isReflHead (n : Name) : Bool :=
  n == ``Eq.refl || n == ``rfl

/-- Split a signature into its ∀-premise types and the conclusion. -/
def piChain (e : Expr) : Array Expr × Expr :=
  go e #[]
where
  go : Expr → Array Expr → Array Expr × Expr
    | .forallE _ ty body _, acc => go body (acc.push ty)
    | e, acc => (acc, e)

/-- Strip leading lambdas off a proof term, exposing its head application. -/
def stripLams : Expr → Expr
  | .lam _ _ body _ => stripLams body
  | e => e

/-- Defining module of a declaration; inline re-implementation of ImportGraph's
`Environment.getModuleFor?` (that helper lives in the external `importGraph`
package, which we deliberately do not depend on here). -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none =>
    if env.constants.map₂.contains n then env.header.mainModule.toString else "?"

/-- `module:line` with a 1-based line number (0 = position unknown). -/
def declLocation (env : Environment) (n : Name) : String :=
  let line : Nat :=
    match (declRangeExt.find? (level := .exported) env n).orElse
        fun _ => declRangeExt.find? (level := .server) env n with
    | some r => r.range.pos.line + 1
    | none => 0
  s!"{moduleOf env n}:{line}"

/-- All checks for one theorem. `sorryAx` is caught by the axiom scan (BAD_AXIOM).

Two subtleties the self-test caught:
- `Expr.eq?` must be applied to the CONCLUSION, not the whole type: for
  `∀ a, a = a` the type itself is a `.forallE` and `eq?` returns none, so all
  theorems with premises were silently skipped by the eq-checks.
- The proof term of `∀ a, a = a := rfl` is `fun a => Eq.refl a`; its head is
  a lambda, so `headConst?` must run after `stripLams`. -/
def checkTheorem (name : Name) (ty : Expr) (val : Expr) : MetaM (Array Finding) := do
  let ty ← instantiateMVars ty
  let val ← instantiateMVars val
  let mut findings : Array Finding := #[]
  let (premises, concl) := piChain ty
  -- TRIV_AEQ_A / TRIV_RFL (direct Eq.refl / Iff.rfl heads only, per spec)
  if let some (_, lhs, rhs) := concl.eq? then
    if Expr.equal lhs rhs then
      findings := findings.push
        { flag := "TRIV_AEQ_A", decl := name
          detail := "conclusion `Eq a a` (syntactically identical sides)" }
      if (headConst? (stripLams val)).any isReflHead then
        findings := findings.push
          { flag := "TRIV_RFL", decl := name
            detail := "proof is `Eq.refl` with identical sides (no definitional unfolding)" }
  else if let some (lhs, rhs) := concl.iff? then
    if Expr.equal lhs rhs && (headConst? (stripLams val)).any isReflHead then
      findings := findings.push
        { flag := "TRIV_RFL", decl := name
          detail := "proof is `Iff.rfl` with identical sides" }
  -- TRIV_PREM: conclusion syntactically equals one of the theorem's own premises
  if premises.any (Expr.equal · concl) then
    findings := findings.push
      { flag := "TRIV_PREM", decl := name
        detail := "conclusion is syntactically one of the theorem's own premises" }
  -- BAD_AXIOM
  for ax in (← Lean.collectAxioms name) do
    unless allowedAxioms.contains ax do
      findings := findings.push
        { flag := "BAD_AXIOM", decl := name, detail := s!"depends on axiom `{ax}`" }
  return findings

/-- Run-length encode an already-sorted flag list into (flag, count) pairs.
Structural recursion on the tail keeps termination obvious without a
`decreasing_by` side goal (`List.length_dropWhile_le` does not exist in
this toolchain). -/
def flagCounts (flags : List String) : List (String × Nat) :=
  match flags with
  | [] => []
  | f :: rest =>
    let run := (f :: rest.takeWhile (· == f)).length
    (f, run) :: flagCounts (rest.dropWhile (· == f))
termination_by flags.length
decreasing_by
  simp_wf
  have h1 : (rest.dropWhile (· == f)).length ≤ rest.length :=
    (List.dropWhile_sublist (p := (· == f)) (l := rest)).length_le
  omega

/- Self-test: plant known-bad and known-good declarations and confirm the
linter flags exactly the bad ones. Guards against a vacuous PASS (0 findings
because the checks never fire, not because the code is clean).

The planted theorems are elaborated directly in THIS module (normal constants
of the script's own environment after `import Hagi`), so `main`'s post-import
env already contains them. `private` gives `_private.scripts.TrivialLint.0`
prefixes, which `normalizeName` strips. Both `checkTheorem` and this runner
live in MetaM, so a plain call suffices.

Plain comment (not docstring): a docstring must attach to a declaration and
cannot precede `namespace`. -/
namespace SelfTest

private theorem trivRfl (a : Nat) : a = a := rfl
private theorem trivAeqA (a : Nat) : a = a := by simp
private theorem trivPrem (h : 1 + 1 = 2) : 1 + 1 = 2 := h
private theorem okUnfold (a : Nat) : a + 0 = a + 0 + 0 := by simp
private theorem okReal (a b : Nat) (h : a = b) : b = a := h.symm

/-- Expected findings for the planted theorems above. -/
def expected : List (String × Name) :=
  [ ("TRIV_RFL", ``trivRfl)
  , ("TRIV_AEQ_A", ``trivAeqA)
  , ("TRIV_PREM", ``trivPrem) ]

/-- Run `checkTheorem` over the planted set and report mismatches. `main`
sets `Core.State.env` to the SCRIPT's elaboration environment (which contains
the planted theorems from this very module), not the fresh post-importModules
one used for scanning — those are two different environments. -/
def run : MetaM (List String) := do
  let mut errs : List String := []
  for (flag, name) in expected do
    let env ← getEnv
    match env.find? name with
    | some (.thmInfo t) =>
      let found ← checkTheorem name t.type t.value
      unless found.any (·.flag == flag) do
        errs := s!"self-test MISS: {name} expected {flag}, got {found.map (·.flag)}" :: errs
    | _ => errs := s!"self-test MISS: {name} not found in environment" :: errs
  for name in [``okUnfold, ``okReal] do
    let env ← getEnv
    match env.find? name with
    | some (.thmInfo t) =>
      let found ← checkTheorem name t.type t.value
      unless found.isEmpty do
        errs := s!"self-test FALSE-POSITIVE: {name} got {found.map (·.flag)}" :: errs
    | _ => errs := s!"self-test MISS: {name} (good theorem) not found in environment" :: errs
  return errs.reverse

end SelfTest

end TrivialLint

open TrivialLint

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  -- Requires `lake build` (Hagi olean on the search path).
  let env ← importModules #[{ module := `Hagi }] ∅ (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<TrivialLint>", options := {}, fileMap := default }
  let state : Core.State := { env := env }
  let ((scanned, findings), _, _) ← (MetaM.toIO · ctx state) do
    -- `SMap.fold` covers BOTH stages: after `importModules` all imported
    -- constants live in stage 1 (`map₁`), while stage 2 (`map₂`) holds only
    -- constants added after the stage switch during elaboration.
    let thms : Array (Name × Expr × Expr) := env.constants.fold (init := #[])
      (fun acc n info =>
        if let .thmInfo t := info then
          if inHagi n then acc.push (n, t.type, t.value) else acc
        else acc)
    let mut acc : Array Finding := #[]
    for (n, ty, val) in thms do
      try
        acc := acc ++ (← checkTheorem n ty val)
      catch e =>
        IO.println s!"warn: check failed for `{n}`: {← e.toMessageData.toString}"
    return (thms.size, acc)
  let findings := findings.qsort fun a b =>
    if a.flag != b.flag then a.flag < b.flag else a.decl.toString < b.decl.toString
  IO.println s!"=== TrivialLint: {scanned} theorems scanned in `Hagi.*` ==="
  if findings.isEmpty then
    IO.println "no findings"
  else
    for (flag, count) in flagCounts (findings.toList.map (·.flag)) do
      IO.println s!"{flag}: {count}"
    IO.println "---"
    for f in findings do
      IO.println s!"{f.flag} | {f.decl} | {declLocation env f.decl} | {f.detail}"
  IO.println (if findings.isEmpty then "LINT: PASS" else "LINT: FAIL")
  unless findings.isEmpty do
    IO.Process.exit 1

/- Elaboration-time self-test: `#eval` executes while THIS file's environment
still contains the planted theorems (stage-2 constants of the script itself),
unlike `main`, whose state is seeded from the fresh `importModules` env. If it
reports FAIL, the run's LINT: PASS is vacuous — the checks never fired. -/
#eval show Lean.Elab.TermElabM Unit from do
  let errs ← SelfTest.run
  if errs.isEmpty then
    IO.println "SELF-TEST: PASS"
  else
    for e in errs do
      IO.println e
    IO.println "SELF-TEST: FAIL"
