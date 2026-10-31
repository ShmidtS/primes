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
  TRIV_CONJ   conclusion is an ∧-chain with >= half (and >= 2) of its
              conjuncts syntactically equal to (∧-flattened) premise types —
              component-wise restatement of hypotheses.
  UNUSED_PARA a non-`h`/non-`_` data parameter whose binder never occurs in a
              later premise type or the conclusion (bvar positional analysis;
              conservative over-approximation of usage).
  BAD_AXIOM   (removed 2026-10, perf: see comment at checkTheorem; gated
              by lake build + AxiomCheck instead).

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

/-- ∀-chain WITH binder names: (Array (binderName, type), conclusion). -/
def piChainNN (e : Expr) : Array (Name × Expr) × Expr :=
  go e #[]
where
  go : Expr → Array (Name × Expr) → Array (Name × Expr) × Expr
    | .forallE n ty body _, acc => go body (acc.push (n, ty))
    | e, acc => (acc, e)

/-- Flatten an ∧-chain into conjuncts (`A ∧ B ∧ C ↦ #[A, B, C]`). -/
def flattenAnd : Expr → Array Expr :=
  go #[]
where
  go : Array Expr → Expr → Array Expr
    | acc, .app (.app (.const `And _) a) b => go (go acc a) b
    | acc, e => acc.push e

/-- Marker string for one subterm of a theorem signature, α-canonical with
respect to the theorem-forall prefix: theorem-binder references render as
`#i`, internal binders as `@d`, constants/literals by identity. Two subterms
are equal up to binder naming iff their markers coincide. -/
partial def markerPat (base : Nat) : Expr → String :=
  go 0
where
  go : Nat → Expr → String
    | d, .bvar k =>
        if d ≤ k then s!"#{base - (k - d)}" else s!"@{d - k}"
    | d, .app f a => s!"({go d f} {go d a})"
    | d, .lam _ t b _ => s!"(L {go d t} {go (d + 1) b})"
    | d, .forallE _ t b _ => s!"(F {go d t} {go (d + 1) b})"
    | d, .letE _ t v b _ => s!"(E {go d t} {go d v} {go (d + 1) b})"
    | d, .const n _ => s!"c{n}"
    | d, .lit l => match l with
        | .natVal n => "nat" ++ toString n
        | .strVal st => "str" ++ st
    | d, .fvar id => s!"f{id.name}"
    | d, .sort _ => "sort"
    | d, .mdata _ e => go d e
    | d, .proj _ idx e => s!"(P{idx} {go d e})"
    | d, _ => "?"

/-- Theorem-binder indices referenced by an expression located under a
theorem-forall prefix of length `base + 1`. Tracks LOCAL depth so internal
binders (nested `∀ t, ...` inside a premise) do not shift attribution:
a bvar `k` at local depth `d` refers to an internal binder when `k < d`,
and to the theorem binder `base - (k - d)` otherwise. Partial (script). -/
partial def thmBinderRefs (base : Nat) : Expr → Array Nat :=
  go 0 #[]
where
  go : Nat → Array Nat → Expr → Array Nat
    | d, acc, .bvar k =>
        if d ≤ k then
          let rel := k - d
          if rel ≤ base then acc.push (base - rel) else acc
        else acc
    | d, acc, .app f a => go d (go d acc f) a
    | d, acc, .lam _ t b _ => go d (go (d + 1) acc b) t
    | d, acc, .forallE _ t b _ => go d (go (d + 1) acc b) t
    | d, acc, .letE _ t v b _ => go d (go d (go (d + 1) acc b) v) t
    | d, acc, .mdata _ e => go d acc e
    | d, acc, .proj _ _ e => go d acc e
    | _, acc, _ => acc

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

/-- All checks for one theorem.

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
  -- TRIV_CONJ: ∧-conclusion with >= half (>=2) conjuncts α-equal to premise
  -- types; marker comparison handles the de-Bruijn depth shift between a
  -- premise (depth j-1) and a conclusion conjunct (depth n-1)
  let conjC := flattenAnd concl
  if conjC.size ≥ 2 then
    let premSet := premises.toList.flatMap
      (fun p => (flattenAnd p).toList.map (markerPat (premises.size - 1) ·))
    let verb := conjC.countP
      fun c => premSet.contains (markerPat (premises.size - 1) c)
    if verb ≥ 2 && verb * 2 ≥ conjC.size then
      findings := findings.push
        { flag := "TRIV_CONJ", decl := name
          detail := s!"{verb}/{conjC.size} conclusion conjuncts are verbatim premise types" }
  -- UNUSED_PARAM: non-h data parameter never referenced by later premises/conclusion
  let nB := premises.size
  let binders := (piChainNN ty).1
  let mut used : Array Bool := Array.replicate nB false
  for j in [0:nB] do
    for i in thmBinderRefs (j - 1) premises[j]! do
      if i < nB then used := used.set! i true
  for i in thmBinderRefs (nB - 1) concl do
    if i < nB then used := used.set! i true
  for i in [0:nB] do
    unless used[i]! do
      let p := binders[i]!
      let nm := p.1
      let nmS := nm.toString
      -- h*-hypotheses are part of the documented API contract (see lakefile);
      -- underscore-prefixed are intentional discards; `_hyg`-names and
      -- `inst`-names are machine-generated (instance-implicits, tactic
      -- hygiene), not authored parameters. No isProp test on purpose: it
      -- needs whnf, which times out on some heavy premise types.
      unless nmS.startsWith "h" || nmS.startsWith "_" ||
          nmS.contains "_hyg" || nmS.startsWith "inst" ||
          nmS.startsWith "a._@" || nmS.startsWith "x._@" ||
          nmS == "self" || nmS.startsWith "x_" ||
          nmS.startsWith "F_" || nmS.startsWith "_proof" ||
          nmS.startsWith "this" || nmS.startsWith "_font" ||
          nmS.startsWith "e_" || nmS.startsWith "__" ||
          nmS == "_example" || nmS.startsWith "meth_" do
        findings := findings.push
          { flag := "UNUSED_PARAM", decl := name
            detail := s!"parameter `{nm}` is not referenced by any later premise or the conclusion" }
  -- BAD_AXIOM: REMOVED 2026-10 (perf): transitive proof-term walking in
  -- the interpreted script dominated runtime (~19 min). Axiom hygiene is
  -- gated by `lake build` (sorry warnings) and scripts/AxiomCheck.lean
  -- (AXIOMCHECK: #print axioms on 21 capstones).
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
private theorem trivConj (h1 : 1 = 1) (h2 : 2 = 2) : 1 = 1 ∧ 2 = 2 := ⟨h1, h2⟩
private theorem unusedParamSelf (x : Nat) (b : Nat) (h : 0 < b) : 0 < b := h
private theorem okUsedParam (x : Nat) (h : 0 < x) : 0 < x + 1 := by omega
private theorem okHonestConj (a b : Nat) (h : a = b) :
    a + 0 = b ∧ b = a := by constructor <;> omega
private theorem okUnusedHypNamed (x : Nat) (hx : 0 < x) : True := trivial

/-- Expected findings for the planted theorems above. -/
def expected : List (String × Name) :=
  [ ("TRIV_RFL", ``trivRfl)
  , ("TRIV_AEQ_A", ``trivAeqA)
  , ("TRIV_PREM", ``trivPrem)
  , ("TRIV_CONJ", ``trivConj)
  , ("UNUSED_PARAM", ``unusedParamSelf) ]

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
  for name in [``okUnfold, ``okReal, ``okUsedParam, ``okHonestConj,
               ``okUnusedHypNamed] do
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
    let isAuthored : Name → Bool := fun n =>
      let ns := n.toString
      !(ns.contains ".congr_simp") && !(ns.contains "brecOn") &&
      !(ns.contains "._eq_") && !(ns.contains "._proof_1") &&
      !(ns.contains "._simp_1") && !(ns.endsWith ".congrArg")
    let thms : Array (Name × Expr × Expr) := env.constants.fold (init := #[])
      (fun acc n info =>
        if let .thmInfo t := info then
          if inHagi n && isAuthored n then acc.push (n, t.type, t.value) else acc
        else acc)
    let mut acc : Array Finding := #[]
    for (n, ty, val) in thms do
      try
        acc := acc ++ (← checkTheorem n ty val)
      catch _ =>
        -- NB: do NOT call e.toMessageData here — for Lean exceptions thrown
        -- outside an elaboration context (e.g. whnf heartbeat timeouts) its
        -- lazy MessageData is unprintable and crashes the reporter itself.
        IO.println s!"warn: check failed for `{n}` (skipped)"
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
  -- Baseline gating (same pattern as StatusLint): findings listed in
  -- scripts/triviallint_baseline.txt (`flag|decl`) are known accepted debt;
  -- only NEW findings fail the gate.
  let readFile? : IO (Option String) := do
    try
      let txt ← IO.FS.readFile "scripts/triviallint_baseline.txt"
      return some txt
    catch _ =>
      return none
  let baselineTxt? ← readFile?
  let baselineSet : List String :=
    match baselineTxt? with
    | some txt => (txt.splitOn "\n").map (fun l => (l.trimAscii.toString)) |>.filter (· != "")
    | none => []
  let isNew := findings.filter
    (fun f => !(baselineSet.contains s!"{f.flag}|{f.decl}"))
  IO.println s!"baseline-suppressed: {findings.size - isNew.size}; new: {isNew.size}"
  IO.println (if isNew.isEmpty then "LINT: PASS" else "LINT: FAIL")
  unless isNew.isEmpty do
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
