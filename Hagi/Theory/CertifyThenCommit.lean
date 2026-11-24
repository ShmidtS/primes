/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.Core
import Hagi.Runtime.CertChecker
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Real

set_option relaxedAutoImplicit false

/-!
# Certify-then-commit — the end-to-end cycle theorem

A THROUGH-CYCLE theorem for the certify-then-commit
loop — T rounds, each round owned by one of the four gates
(HeadStep / GrowBlock / Compress / SelfEdit), each round either
COMMITS a certified ledger step or HOLDS (no state change), with
the anytime holdout stop able to BLOCK commits. With probability
≥ 1 − δtotal: the objective telescopes against the committed drops,
the holdout risk grows by at most ε, the budget ledger balances,
and there are no false commits.

## Coordination only — the mathematics lives in the components

Every substantive leg is an EXISTING theorem, cited here as the
construction route for the per-round `CertStep` supply (interface
fields only; nothing restated):

- **HeadStep** (adaptive majorizer): the certified drop
  `A ^ 2 / (4 * C)` at the bounded safe step —
  `Hagi.Theory.AdaptiveMajorizer.adaptive_descent` and its CE
  instantiation `ce_adaptive_descent`.
- **GrowBlock**: admission with the LCB margin
  `λM·Δcost + λR·Δrisk + ε_cert ≤ drop` —
  `Hagi.Theory.BlockAdmission.block_admission_sound` (checker-
  verified `CertStepData`); the anytime holdout stop —
  `Hagi.Theory.AnytimeHoldoutStop.grow_stop_sound` /
  `false_stop_bound` (false stop ≤ δ, Ville) and the blocking law
  `admitWithStop` / `stop_blocks_admission` (here: `stop_blocks`).
- **Compress** (MDL prune): objective non-increasing, code
  cost strictly decreasing, fiber floors preserved —
  `Hagi.Theory.MDLPrune.mdl_prune_cycle_sound`,
  `prune_preserves_fiber_floor`.
- **SelfEdit** (strict adopt gate): adoptions strictly
  increase the score over a finite knob space —
  `Hagi.Theory.SelfEditGate.adopt_chain_terminates`,
  `Hagi.Theory.KnobMomentum.momentum_adopt_gated` /
  `momentum_chain_terminates`.
- **Executable checker**: `Hagi.Runtime.checkStep` /
  `checkStep_sound` — a committed round's reported data is
  machine-checked (positive drop, real descent) — the (a) leg.
- **Probability glue** (Ville stitching): the per-round
  false-commit level premises are DISCHARGED by
  `Hagi.Training.AdaptiveAnytime.adaptive_anytime_valid`
  (stitched master, Σ weights ≤ 1, ≤ K·α) or
  `adaptive_anytime_budget_split` (≤ α); the union leg here is the
 `ttcat_complete` pattern (`measureReal_iUnion_fintype_le`).

## Honesty pins

- **The mixed hold/commit induction is NEW but pure ledger
  bookkeeping** (`ctc_mixed_ledger`): linarith over `descent`,
  `budget_next`, `riskStep` and the hold equalities. This is pure
  coordination accounting, no new component mathematics.
- **`CertStep` does NOT imply risk monotonicity** (the sign of
  `riskSpend` is free): the (d) holdout channel is premise-form —
  per-round allowances `e i ≥ 0` with `Σ e ≤ ε`, discharged through
  the risk channel / stop routes. ε is a premise, not a
  derived quantity.
- **Measure premises are PREMISE-form** (repo convention):
  `μ.real {falseCommit i} ≤ δ i` is the consumer's
  to discharge (cited routes above); `commit`/`stop` are
  ω-INDEPENDENT record fields (the convention).
- The checker leg (a) verifies the reported readouts (`checkStep`);
  the full data-to-kernel bridge is `Hagi.Runtime.mkCertStep`
  (cited; the list-level `checkTrajectory` fold is not duplicated
  here — the drop positivity and the ledger coupling are what the
  cycle needs).
- The trajectory is only pinned on `0..T`; the accounting core is
  stated for `n ≤ T` (no claims about the system after the
  horizon, no trajectory extension).

Layer: Theory (7), like BlockAdmission/CertCEHoldout —
the module must see the Cert kernel (2), the Runtime checker (3)
and the Measure vocabulary (Mathlib); layer 7 sees all of them.
-/

open MeasureTheory
open Hagi.Cert (SystemMetrics StepObligations FloorsKept CertStep)

namespace Hagi.Theory.CertifyThenCommit

/-! ## Round kinds -/

/-- The four gate owners of a certify-then-commit round: a certified head step (adaptive majorizer), a growth
block admission, an MDL compression prune, or a
strict-gate self-edit adoption. The kind is a TAG for
the construction route (cited in the module docstring); the cycle
theorem consumes only the `CertStep` interface. -/
inductive CTCRound where
  /-- Certified head step: drop A²/4C at the bounded safe step
  (`adaptive_descent` / `ce_adaptive_descent`). -/
  | headStep
  /-- Growth block admission with the LCB margin and the anytime
  stop (`block_admission_sound` `grow_stop_sound`). -/
  | growBlock
  /-- MDL compression prune (`mdl_prune_cycle_sound`). -/
  | compress
  /-- Strict-gate self-edit adoption (`adoptGate` /
 momentum). -/
  | selfEdit

/-! ## The cycle record (interface fields only) -/

variable {S TaskId : Type}

/-- THE certify-then-commit cycle over T rounds: the ledger carrier
(`M`/`obl`, kernel), the round kinds, the state trajectory
(round `i` occupies `t i → t (i + 1)`), the ω-independent commit
decisions, the certified ledger steps at commits (`step` — the
interface every gate discharges through its cited component
theorem), the hold law (no commit ⇒ no state change), the anytime
holdout stop with its blocking law, the ledger readout channels
(drop/spend values coupled to the steps, holds paying 0), and the
(d)-channel premises (per-round holdout-risk allowances `e ≥ 0`,
floors and budget invariant at the initial state). -/
structure CertifyThenCommitCycle (M : SystemMetrics S TaskId)
    (obl : StepObligations TaskId) (T : ℕ) where
  /-- Which gate owns round i (construction-route tag). -/
  kind : Fin T → CTCRound
  /-- The state trajectory; round i occupies `t i → t (i + 1)`. -/
  t : ℕ → S
  /-- The commit decision of round i (ω-independent). -/
  commit : Fin T → Bool
  /-- A committed round's certified ledger entry (kernel
  interface; construction routes cited in the module docstring). -/
  step : ∀ i : Fin T, commit i = true → CertStep M obl (t i) (t (i + 1))
  /-- A held round is a no-op: the state does not move. -/
  held : ∀ i : Fin T, commit i = false → t (i + 1) = t i
  /-- The anytime holdout stop flag of round i. -/
  stop : Fin T → Bool
  /-- A fired stop blocks the commit (`admitWithStop` /
  `stop_blocks_admission`): growth can only be stopped, never
  committed through. -/
  stop_blocks : ∀ i : Fin T, stop i = true → commit i = false
  /-- The ledger drop channel: the certified drop of each commit
  (0 for holds). -/
  dropV : Fin T → ℝ
  drop_step : ∀ i : Fin T, (h : commit i = true) → dropV i = (step i h).drop
  drop_hold : ∀ i : Fin T, commit i = false → dropV i = 0
  /-- The ledger budget-spend channel (0 for holds). -/
  spendV : Fin T → ℝ
  spend_step : ∀ i : Fin T, (h : commit i = true) →
    spendV i = (step i h).budgetSpend
  spend_hold : ∀ i : Fin T, commit i = false → spendV i = 0
  /-- The per-round holdout-risk allowance (premise-form (d)
  channel; discharged through the risk channel / stop
  routes). -/
  e : Fin T → ℝ
  e_nonneg : ∀ i : Fin T, 0 ≤ e i
  riskStep : ∀ i : Fin T, M.risk (t (i + 1)) ≤ M.risk (t i) + e i
  /-- Floor and budget invariants at the initial state. -/
  init_floors : FloorsKept M obl (t 0)
  init_budget : 0 ≤ M.budget (t 0)

/-! ## The bookkeeping core -/

/-- **The mixed hold/commit ledger accounting** (pure bookkeeping — linarith over `descent`,
`budget_next`, `riskStep` and the hold equalities, NO component
mathematics): over any horizon-N trajectory of certified commits
and no-op holds with coupled drop/spend channels, at every time
n ≤ N the objective telescopes against the committed drops, the
budget ledger BALANCES by an equality, the risk grew by at most Σ
allowances, and the budget/floor invariants persist. Stated for
`n ≤ N` only — no claims beyond the horizon. -/
theorem ctc_mixed_ledger {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} (t : ℕ → S) (commit : ℕ → Bool)
    (N : ℕ)
    (step : ∀ j : ℕ, j < N → commit j = true →
      CertStep M obl (t j) (t (j + 1)))
    (held : ∀ j : ℕ, j < N → commit j = false → t (j + 1) = t j)
    (dropV spendV erisk : ℕ → ℝ)
    (hd : ∀ j (hj : j < N) (h : commit j = true),
      dropV j = (step j hj h).drop)
    (hd0 : ∀ j (_hj : j < N) (_h : commit j = false), dropV j = 0)
    (hsd : ∀ j (hj : j < N) (h : commit j = true),
      spendV j = (step j hj h).budgetSpend)
    (hsd0 : ∀ j (_hj : j < N) (_h : commit j = false), spendV j = 0)
    (henn : ∀ j : ℕ, 0 ≤ erisk j)
    (hrisk : ∀ j : ℕ, j < N → M.risk (t (j + 1)) ≤ M.risk (t j) + erisk j)
    (h0f : FloorsKept M obl (t 0)) (h0b : 0 ≤ M.budget (t 0)) :
    ∀ n ≤ N, M.objective (t n) ≤ M.objective (t 0)
        - ∑ j ∈ Finset.range n, dropV j
      ∧ M.budget (t n) + ∑ j ∈ Finset.range n, spendV j
          = M.budget (t 0)
      ∧ M.risk (t n) ≤ M.risk (t 0) + ∑ j ∈ Finset.range n, erisk j
      ∧ 0 ≤ M.budget (t n) ∧ FloorsKept M obl (t n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, h0b, h0f⟩ <;> simp
  | succ n ih =>
    intro hN
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (Nat.le_of_succ_le hN)
    have hnlt : n < N := Nat.lt_of_succ_le hN
    by_cases hcb : commit n = true
    · -- commit round
      set hs := step n hnlt hcb with hsd0
      have hdn : dropV n = hs.drop := hd n hnlt hcb
      have hsn : spendV n = hs.budgetSpend := hsd n hnlt hcb
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [hdn, hsn]
      refine ⟨by linarith [ih1, hs.descent], ?_, by linarith [ih3, hrisk n hnlt],
        hs.budget_nonneg, hs.floorsKept⟩
      rw [hs.budget_next]
      linarith
    · -- hold round
      have hcf : commit n = false := by simpa using hcb
      have hhold : t (n + 1) = t n := held n hnlt hcf
      have hdn : dropV n = 0 := hd0 n hnlt hcf
      have hsn : spendV n = 0 := hsd0 n hnlt hcf
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [hdn, hsn]
      simp only [add_zero]
      rw [hhold]
      exact ⟨ih1, ih2, by linarith [henn n], ih4, ih5⟩

/-! ## Coordination laws -/

/-- **A fired stop never commits** (the coordination law,
pure field consequence of `stop_blocks`): when the anytime holdout
stop fires in round i, that round HOLDS — no growth-block, no
ledger entry, no drop claim. -/
theorem stop_never_commits {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {T : ℕ}
    (cyc : CertifyThenCommitCycle M obl T) (i : Fin T)
    (h : cyc.stop i = true) : cyc.commit i = false :=
  cyc.stop_blocks i h

/-! ## Leg (a): the checker verifies every commit -/

/-- **Leg (a)**: every COMMIT round of the cycle produces a
machine-CHECKED step record: if round i's readout data `data i`
passes the executable checker (`checkStep`) and the declared
drop agrees with the ledger entry, then the committed drop is
positive — the certified-descent side of
`certify_then_commit_sound`, established by the leg
`checkStep_sound` (the data-to-kernel bridge is
`Hagi.Runtime.mkCertStep`, cited). -/
theorem commit_drop_checked {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {T : ℕ}
    (cyc : CertifyThenCommitCycle M obl T)
    (data : Fin T → Hagi.Runtime.CertStepData)
    (i : Fin T) (_hcom : cyc.commit i = true)
    (hagree : ((data i).drop : ℝ) = cyc.dropV i)
    (hchk : Hagi.Runtime.checkStep (data i) = true) :
    0 < ((data i).drop : ℝ) ∧ ((data i).drop : ℝ) = cyc.dropV i :=
  ⟨(Hagi.Runtime.checkStep_sound hchk).1, hagree⟩

/-! ## Fin-to-ℕ lift plumbing (pure casting, no content) -/

variable {T : ℕ}

/-- Lift a `Fin T` boolean decision sequence to ℕ (false beyond
the horizon). Pure plumbing. -/
def liftCommit (commit : Fin T → Bool) : ℕ → Bool :=
  fun j => if h : j < T then commit ⟨j, h⟩ else false

/-- Lift a `Fin T` real channel to ℕ (zero beyond the horizon).
Pure plumbing. -/
def liftFun (f : Fin T → ℝ) : ℕ → ℝ :=
  fun j => if h : j < T then f ⟨j, h⟩ else 0

theorem liftCommit_of_lt {commit : Fin T → Bool} {j : ℕ} (hj : j < T) :
    liftCommit commit j = commit ⟨j, hj⟩ := by
  simp only [liftCommit, dite_eq_left hj]

theorem liftFun_of_lt {f : Fin T → ℝ} {j : ℕ} (hj : j < T) :
    liftFun f j = f ⟨j, hj⟩ := by
  simp only [liftFun, dite_eq_left hj]

theorem liftFun_of_ge {f : Fin T → ℝ} {j : ℕ} (hj : ¬ j < T) :
    liftFun f j = 0 := by
  simp only [liftFun, dite_eq_right hj]

theorem liftFun_nonneg {f : Fin T → ℝ} (hf : ∀ i, 0 ≤ f i) (j : ℕ) :
    0 ≤ liftFun f j := by
  by_cases hj : j < T
  · rw [liftFun_of_lt hj]; exact hf _
  · rw [liftFun_of_ge hj]

theorem liftFun_sum (f : Fin T → ℝ) :
    ∑ i : Fin T, f i = ∑ j ∈ Finset.range T, liftFun f j := by
  rw [← Fin.sum_univ_eq_sum_range (f := fun j => liftFun f j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [liftFun_of_lt i.2]

/-! ## The main theorem -/

variable {Ω : Type}

/-- The false-commit event family of the cycle:
round i committed (`commit i = true`) while the committed claim
was false (`falseCommit i ω` — the consumer predicate,
premise-form). -/
def ctcFalseCommitSet (commit : Fin T → Bool)
    (falseCommit : Fin T → Ω → Prop) (i : Fin T) : Set Ω :=
  {ω | commit i = true ∧ falseCommit i ω}

/-- **certify_then_commit_sound — the end-to-end cycle
theorem**: for any T-round certify-then-commit cycle, under the
per-round false-commit measure premises (premise-form; discharge
routes CITED: `adaptive_anytime_valid` — the stitched Ville
master with Σ weights ≤ 1 — or `adaptive_commit_bridge`; for
stop-mediated rounds `false_stop_bound`), with levels summing
to at most `δtotal` and per-round holdout allowances summing to at
most `ε`:
- (b) the objective TELESCOPES: `obj (t T) ≤ obj (t 0) − Σ drops`
  over the committed ledger entries;
- (c) with probability ≥ 1 − δtotal NO commit is false: the
  union-bound leg over the T false-commit events;
- (d) the holdout risk grew by at most ε (premise-form channel);
- (e) the budget ledger BALANCES (`budget (t T) + Σ spends =
  budget (t 0)`), the budget stays nonnegative and the floors are
  kept at the terminal state. -/
theorem certify_then_commit_sound {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {T : ℕ}
    (cyc : CertifyThenCommitCycle M obl T)
    {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (falseCommit : Fin T → Ω → Prop) (δ : Fin T → ℝ)
    (hFalse : ∀ i : Fin T, μ.real {ω | falseCommit i ω} ≤ δ i)
    {δtotal : ℝ} (hsumd : ∑ i : Fin T, δ i ≤ δtotal)
    {ε : ℝ} (hε : ∑ i : Fin T, cyc.e i ≤ ε) :
    -- (b) objective telescope against the committed drops
    M.objective (cyc.t T) ≤ M.objective (cyc.t 0)
      - ∑ i : Fin T, cyc.dropV i
    -- (c) with high probability no commit is false
    ∧ μ.real {ω | ∃ i : Fin T,
        cyc.commit i = true ∧ falseCommit i ω} ≤ δtotal
    -- (d) holdout risk grows by at most ε
    ∧ M.risk (cyc.t T) ≤ M.risk (cyc.t 0) + ε
    -- (e) budget balance + nonnegativity + floors
    ∧ M.budget (cyc.t T) + ∑ i : Fin T, cyc.spendV i = M.budget (cyc.t 0)
    ∧ 0 ≤ M.budget (cyc.t T) ∧ FloorsKept M obl (cyc.t T) := by
  -- the lifted ℕ-indexed supply (pure plumbing)
  have hcom : ∀ j (hj : j < T) (h : liftCommit cyc.commit j = true),
      cyc.commit ⟨j, hj⟩ = true := by
    intro j hj h
    rw [liftCommit_of_lt hj] at h
    exact h
  have hcomf : ∀ j (hj : j < T) (h : liftCommit cyc.commit j = false),
      cyc.commit ⟨j, hj⟩ = false := by
    intro j hj h
    rw [liftCommit_of_lt hj] at h
    exact h
  have key := ctc_mixed_ledger (N := T) cyc.t (liftCommit cyc.commit)
    (fun j hj h => cyc.step ⟨j, hj⟩ (hcom j hj h))
    (fun j hj h => cyc.held ⟨j, hj⟩ (hcomf j hj h))
    (liftFun cyc.dropV) (liftFun cyc.spendV) (liftFun cyc.e)
    (fun j hj _h => by
      rw [liftFun_of_lt hj]
      exact cyc.drop_step ⟨j, hj⟩ (hcom j hj _h))
    (fun j hj h => by
      rw [liftFun_of_lt hj]
      exact cyc.drop_hold ⟨j, hj⟩ (hcomf j hj h))
    (fun j hj _h => by
      rw [liftFun_of_lt hj]
      exact cyc.spend_step ⟨j, hj⟩ (hcom j hj _h))
    (fun j hj h => by
      rw [liftFun_of_lt hj]
      exact cyc.spend_hold ⟨j, hj⟩ (hcomf j hj h))
    (fun j => liftFun_nonneg cyc.e_nonneg j)
    (fun j hj => by
      rw [liftFun_of_lt hj]
      exact cyc.riskStep ⟨j, hj⟩)
    cyc.init_floors cyc.init_budget T (le_refl T)
  obtain ⟨kb, kbud, krisk, knn, kfl⟩ := key
  -- (b)
  have hsd : ∑ i : Fin T, cyc.dropV i
      = ∑ j ∈ Finset.range T, liftFun cyc.dropV j := liftFun_sum cyc.dropV
  have hss : ∑ i : Fin T, cyc.spendV i
      = ∑ j ∈ Finset.range T, liftFun cyc.spendV j := liftFun_sum cyc.spendV
  have hse : ∑ i : Fin T, cyc.e i
      = ∑ j ∈ Finset.range T, liftFun cyc.e j := liftFun_sum cyc.e
  -- (c)
  have hset : {ω | ∃ i : Fin T, cyc.commit i = true ∧ falseCommit i ω}
      = ⋃ i : Fin T, ctcFalseCommitSet cyc.commit falseCommit i := by
    ext ω
    simp [ctcFalseCommitSet]
  have hper : ∀ i : Fin T,
      μ.real (ctcFalseCommitSet cyc.commit falseCommit i) ≤ δ i := by
    intro i
    refine le_trans (measureReal_mono
      (fun ω ⟨_hc, hf⟩ => hf) (by finiteness)) (hFalse i)
  refine ⟨by linarith [kb, hsd], ?_, by linarith [krisk, hse, hε],
    by rw [hss]; exact kbud, knn, kfl⟩
  rw [hset]
  calc μ.real (⋃ i : Fin T, ctcFalseCommitSet cyc.commit falseCommit i)
      ≤ ∑ i : Fin T,
          μ.real (ctcFalseCommitSet cyc.commit falseCommit i) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin T, δ i := Finset.sum_le_sum fun i _ => hper i
    _ ≤ δtotal := hsumd

end Hagi.Theory.CertifyThenCommit
