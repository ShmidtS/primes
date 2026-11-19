import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# SelfEditGate — certified self-edit adopt-gate over a finite knob-space

Formalization of the HAGI_v2 self-edit mechanism (implementation
source, READ-ONLY: `C:\HAGI_v2\hagi\selfedit.py`, 242 lines):

* a DECLARED finite knob-space ("KNOBS", source: hagi/selfedit.py:42-46
  — "floor_ladder" / "batch_size" / "proposals" with enumerated
  candidate values; arbitrary AST rewriting of learning code is
  explicitly NOT attempted, source: hagi/selfedit.py:18-20);
* one propose→gate→adopt cycle (source: hagi/selfedit.py:170-227):
  a patch changes exactly ONE knob ("apply_patch", source:
  hagi/selfedit.py:157-159) and is adopted ONLY on strict positive
  evidence (`no_regress = cand.adopted > baseline.adopted ∨
  cand.experts > baseline.experts`, source: hagi/selfedit.py:221-223);
* no-op patches are skipped WITHOUT spending gate budget
  (source: hagi/selfedit.py:102-121 propose-only-changes,
  124-130 "is_noop", 190 "noop-skipped");
* a rejection series is trimmed to `MAX_GATE_RUNS = 6` (source:
  hagi/selfedit.py:167, 180-182: `log["rejected"][-MAX_GATE_RUNS:]`).

Honest limits (not claimed): the code's two-metric disjunction is
modeled by ONE deterministic score `Config → ℝ`; each disjunct is a
special case (a lexicographic pair order also instantiates this).
The gate is a deterministic fixed-seed no-regression test, not a
statistical guarantee — the code itself says so
(hagi/selfedit.py:217-220). The RNG proposal mechanism carries no
mathematical content and is not modeled. What IS claimed: the no-op
fast path is sound, the adopt search terminates in a finite
knob-space, and the strict `>` of the gate is necessary (a weak `≥`
gate admits eternal cycling).
-/

namespace Hagi.Theory.SelfEditGate

variable {κ : Type*} [DecidableEq κ] {V : Type*} [DecidableEq V]

/-- Knob configuration: a value for every declared knob name.
source: hagi/selfedit.py:78-101 "current_settings" — snapshot of the
current knob values (loop defaults overridden by gate-adopted ones). -/
abbrev Config (κ V) := κ → V

/-- A patch overwrites exactly ONE knob with a new value.
source: hagi/selfedit.py:157-159 "apply_patch" —
`out[patch["knob"]] = patch["value"]` on a settings overlay (the
source code is never edited). -/
def applyPatch (cfg : Config κ V) (k : κ) (v : V) : Config κ V :=
  Function.update cfg k v

omit [DecidableEq V] in
/-- Structural lemma: a patch leaves every other knob untouched.
source: hagi/selfedit.py:157-159 (overlay semantics). -/
theorem applyPatch_ne (cfg : Config κ V) {k k' : κ} (v : V)
    (h : k' ≠ k) : applyPatch cfg k v k' = cfg k' := by
  simp [applyPatch, Function.update, h]

omit [DecidableEq V] in
/-- Structural lemma: a patch sets its own knob to the new value.
source: hagi/selfedit.py:157-159. -/
theorem applyPatch_self (cfg : Config κ V) (k : κ) (v : V) :
    applyPatch cfg k v k = v := by
  simp [applyPatch, Function.update]

variable (score : Config κ V → ℝ)

/-- Deterministic benchmark score of a configuration (fixed-seed
mini-suite: adopted rounds / final experts).
source: hagi/selfedit.py:56-68 "run_benchmark" — deterministic
fixture; honest limit: fixed-seed test, not a statistical bound
(hagi/selfedit.py:217-220: 2 rounds give no eta guarantee). -/
abbrev Score (κ V) := Config κ V → ℝ

/-- The adopt gate: a patch is adopted ONLY on strict positive
evidence — the candidate benchmark STRICTLY exceeds the incumbent's.
source: hagi/selfedit.py:221-223 `no_regress = cand.adopted >
baseline.adopted ∨ cand.experts > baseline.experts` (strict `>` on
each disjunct; one-score model, see module docstring). -/
def adoptGate (cfg : Config κ V) (k : κ) (v : V) : Prop :=
  score (applyPatch cfg k v) > score cfg

/-- A no-op patch: the proposed value equals the incumbent setting
on its knob (so the patched config equals the incumbent config).
source: hagi/selfedit.py:124-130 "is_noop". -/
def isNoop (cfg : Config κ V) (k : κ) (v : V) : Prop :=
  applyPatch cfg k v = cfg

omit [DecidableEq V] in
/-- No-op patches can NEVER pass the strict adopt gate: the score is
deterministic in the configuration, so a no-op candidate scores
exactly the incumbent's value. This formally justifies the code's
"noop-skipped" fast path — skipping a no-op without spending gate
runs loses nothing, because it could never be adopted.
source: hagi/selfedit.py:190 (skip), 221 (strict `>`). -/
theorem noop_not_adopted (cfg : Config κ V) (k : κ) (v : V)
    (h : isNoop cfg k v) : ¬ adoptGate score cfg k v := by
  intro hg
  unfold adoptGate isNoop at *
  rw [h] at hg
  exact lt_irrefl _ hg

/-! ### Termination of the adopt chain in a finite knob-space -/

/-- A pointwise strict gain along a chain makes the score chain
strictly monotone. Auxiliary for `adopt_chain_terminates`;
the gain hypothesis is exactly one adoption per step
(`adoptGate`, hagi/selfedit.py:221). -/
theorem chain_strictMono {g : ℕ → ℝ} (h : ∀ i, g (i + 1) > g i) :
    StrictMono g := by
  intro i j hij
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero _)
  | succ j ih =>
    have h1 : i ≤ j := Nat.lt_succ_iff.mp hij
    have h2 : g j < g (j + 1) := h j
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact (ih hlt).trans h2
    · have heq : i = j := Nat.le_antisymm h1 hge
      subst heq; exact h2

set_option linter.unusedFintypeInType false in
/-- MAIN THEOREM: in a finite knob-space the certified self-edit
search TERMINATES — an infinite chain of adoptions is impossible:
each adoption strictly increases a deterministic score over a finite
set of configurations, and an infinite strictly ascending chain
would inject ℕ into a finite type (cardinality contradiction).
source: knob-space finiteness — hagi/selfedit.py:42-46 (three knobs,
enumerated candidate values); strict gain per adoption —
hagi/selfedit.py:221. Honest limits: termination of ADOPTIONS is
claimed, not optimality of the final configuration, and not
termination of proposal attempts (those can continue, being
rejected/no-op-skipped). -/
theorem adopt_chain_terminates [Fintype κ] [Fintype V]
    (f : ℕ → Config κ V)
    (h : ∀ i, score (f (i + 1)) > score (f i)) : False := by
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt2 : score (f a) < score (f b) := chain_strictMono h hlt
      rw [hab] at hlt2
      exact lt_irrefl _ hlt2
    · have hgt2 : score (f b) < score (f a) := chain_strictMono h hgt
      rw [hab] at hgt2
      exact lt_irrefl _ hgt2
  have hcard : ∀ n : ℕ, n ≤ Fintype.card (Config κ V) := fun n => by
    simpa using Fintype.card_le_of_injective (fun (i : Fin n) => f i)
      (fun a b hab2 => Fin.ext (hinj hab2))
  have := hcard (Fintype.card (Config κ V) + 1)
  omega

/-! ### Negative result: the strictness of `>` is necessary -/

/-- NEGATIVE THEOREM: a WEAK gate (non-strict `≥`) admits an
infinite adoption chain of non-no-op patches: with a constant score
and a single boolean knob, the value can be flipped forever — every
step "does not regress" (score equal) and every patch changes the
incumbent (not a no-op), so the gate budget is consumed eternally
and no progress accumulates. This is the formal justification for
the STRICT `>` in hagi/selfedit.py:221 (adopt only on strict
positive evidence, comment at selfedit.py:217-222). -/
theorem weak_gate_cycles : ∃ (weak : Config Bool Bool → ℝ)
    (f : ℕ → Config Bool Bool),
    (∀ i, weak (f (i + 1)) ≥ weak (f i)) ∧
    (∀ i, ∃ (k : Bool) (v : Bool),
      applyPatch (f i) k v = f (i + 1) ∧ applyPatch (f i) k v ≠ f i) := by
  refine ⟨fun _ => 0, fun i k => if k then decide (i % 2 == 1) else false,
    fun i => le_refl 0, ?_⟩
  intro i
  have key : ((i + 1) % 2 == 1) = !(i % 2 == 1) := by
    rcases Nat.lt_or_ge (i % 2) 1 with h | h
    · have h0 : i % 2 = 0 := by omega
      have h1 : (i + 1) % 2 = 1 := by omega
      simp [h0, h1]
    · have h1 : i % 2 = 1 := by omega
      have h0 : (i + 1) % 2 = 0 := by omega
      simp [h0, h1]
  refine ⟨true, (i + 1) % 2 == 1, ?_, ?_⟩
  · funext k
    by_cases hk : k = true
    · subst hk
      simp only [applyPatch, Function.update]
      rw [key]
      by_cases hq : i % 2 = 1 <;> simp_all
    · simp [applyPatch, hk]
  · intro hc
    have h0 : ((i + 1) % 2 == 1) = decide (i % 2 == 1) := by
      have := congrFun hc true
      simpa [applyPatch] using this
    rw [key] at h0
    by_cases hq : i % 2 = 1 <;> simp_all

/-! ### Rejection-series budget invariant -/

/-- "MAX_GATE_RUNS" — maximum rejections kept per series before the
reset. source: hagi/selfedit.py:167 `MAX_GATE_RUNS = 6` (tied to the
GatePipeline C264 delta-schedule bound Σ_{k≤6} 6/(π²k²) ≤ 1). -/
def maxGateRuns : ℕ := 6

/-- Rejection-series trim: at `≥ maxGateRuns` accumulated rejections
the log is truncated to the LAST `maxGateRuns` entries (a fresh
series re-enters the budget-covered range).
source: hagi/selfedit.py:180-182 `if len(rejected) >= MAX_GATE_RUNS:
log["rejected"] = log["rejected"][-MAX_GATE_RUNS:]`. -/
def rejectSeriesTrim (L : List α) : List α :=
  if L.length ≥ maxGateRuns then L.drop (L.length - maxGateRuns) else L

/-- INVARIANT: after the trim performed at the top of each
self-edit cycle, the rejection series is bounded by `maxGateRuns`
(the certified-regime range of the C264 delta schedule).
source: hagi/selfedit.py:180-182. -/
theorem reject_series_bounded (L : List α) :
    (rejectSeriesTrim L).length ≤ maxGateRuns := by
  unfold rejectSeriesTrim
  split
  · rw [List.length_drop]; omega
  · omega

end Hagi.Theory.SelfEditGate
