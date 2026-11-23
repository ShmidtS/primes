/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.StepGen
import Hagi.Contracts.SparseInferenceCert
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Total compute to quality: descent rate × per-step work

The GOAL's «минимизация вычислений» end-to-end: how many certified
steps does it take to reach quality ε (the descent rate), and what
is the TOTAL certified compute (steps × per-step FLOP). Both
carriers already landed; only the COMPOSITION is new:

* the descent-rate carrier is (`Hagi.Model.CEDescent`): the
  one-step certificate `ceOneHot_next_le`
  `next ≤ cur − η·A + (η·R)²/8`, which at the safe step
  `safeStepSize = 4A/R²` (`ceMajorizer_safeStep_eq`) certifies the
  EXACT drop `d = 2·A²/R²` (`ceOneHot_safeStep_le_residual`).
  CITED IN DOCSTRINGS ONLY — the composition takes the uniform
  drop as a PREMISE over the kernel's `CertStepGen.drop`
  field; no rate constants are invented or re-derived here.
* the per-step FLOP carrier is
  (`Hagi.Contracts.SparseInferenceCert`): the work model
  `denseMatVecWork n = n²`, `lowRankMatVecWork k n = 2kn`,
  `lowrank_op_ratio` — cited verbatim, not re-proved.
* the kernel is (`Hagi.Cert.CertStepGen`): the drop telescope
  `trajectory_telescope_gen` is the engine; this module adds the
  missing BUDGET telescope (the exact ledger identity) and the
  step-count / total-compute / tradeoff / packaging theorems on
  top.

Honest scope:

* DETERMINISTIC descent premise only: the uniform-drop hypothesis
  is the honest interface to the carrier; no adaptivity, no
  SGD noise, no stochastic rates are claimed.
* The (d, W) frontier is EMPIRICAL: whether the compressed
  configuration's descent constant survives (`d ≤ d'` in
  `lowrank_total_compute_le`) is a PREMISE — no claim that
  compression preserves the descent rate; the tradeoff is
  explicit: total(d, W) = (Δ₀/d)·W is minimized over the frontier.
* The step-count minimality premise (`hceil` in
  `total_compute_to_quality`) is honest ceiling arithmetic: only
  `Δ₀ ≤ n·d` follows from descent (a trajectory may overrun); the
  minimal witness n = ⌈Δ₀/d⌉ satisfies BOTH premises.
* Work measured in the entry-read model; no asymptotics, no
  hardware model, no probability; numbers live in the numeric
  `Anchor` lemmas only.
-/

open Hagi.Contracts.SparseInferenceCert

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.ComputeToQuality

variable {S TaskId : Type*}
variable (M : Hagi.Cert.SystemMetrics S TaskId) (obl : Hagi.Cert.StepObligations TaskId)

/-! ## The budget telescope (the fourth channel) -/

/-- **Budget telescope** — the missing fourth telescope
kernel (drop, delta and risk already telescope): the terminal
compute budget is the initial budget minus the EXACT sum of
per-step spends (induction on `CertStepGen.budget_next`; the
identity form, stronger than the pointwise `CertStepGen.budgetBound`).
This is the resource-ledger law the budget pattern demanded
for compute. -/
theorem budget_telescope_gen (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1))) :
    M.budget (t n) = M.budget (t 0)
      - ∑ j ∈ Finset.range n, (steps j).budgetSpend := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := (steps n).budget_next
    rw [e, ih, Finset.sum_range_succ]
    ring

/-! ## Steps to quality (the descent-rate side) -/

/-- **MAIN 1 — steps to quality**: if every certified step drops
the objective by at least `d` (the uniform-drop premise — the
honest interface to the carrier: at the safe step the
certified drop is exactly `2·A²/R²` per `ceOneHot_safeStep_le_
residual`, but NO constant is baked in here), and the initial gap
`Δ₀ = objective (t 0) − ε` fits in `n` drops (`Δ₀ ≤ n·d`), then
after `n` steps the quality floor ε is met: `objective (t n) ≤ ε`.
Pure telescoping — the C294-style bound applied to training steps
(the engine is `trajectory_telescope_gen`; the sum bound is
`Finset.sum_le_sum`). No upper bound on n is claimed or needed. -/
theorem steps_to_quality (deltaLevel : S → ℝ)
    (ε d : ℝ) (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd : ∀ j ∈ Finset.range n, d ≤ (steps j).drop)
    (hgap : M.objective (t 0) - ε ≤ n * d) :
    M.objective (t n) ≤ ε := by
  have htel := Hagi.Cert.trajectory_telescope_gen M obl deltaLevel n t steps
  have hsum : n * d ≤ ∑ j ∈ Finset.range n, (steps j).drop := by
    calc n * d = ∑ _j ∈ Finset.range n, d := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range n, (steps j).drop := Finset.sum_le_sum hd
  linarith

/-! ## Total compute to quality (steps × per-step FLOP) -/

/-- **MAIN 2 — total compute to quality**: the ceiling arithmetic
of steps × per-step FLOP — with every step spending ≤ W of compute
budget and the step count being the MINIMAL witness (the honest
ceiling premise `n·d ≤ Δ₀ + d`, satisfied by n = ⌈Δ₀/d⌉ where Δ₀ =
`objective (t 0) − ε` is the initial gap and d the uniform
certified drop of MAIN 1; minimality does NOT follow from descent
alone — a trajectory may overrun, the probe iteration caught
that), the total certified compute is at most
`(Δ₀ + d)/d · W ≤ (Δ₀/d + 1)·W`: the end-to-end statement of
«минимизация вычислений». -/
theorem total_compute_to_quality (deltaLevel : S → ℝ)
    (ε d W : ℝ) (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hceil : n * d ≤ M.objective (t 0) - ε + d)
    (hW : ∀ j ∈ Finset.range n, (steps j).budgetSpend ≤ W)
    (hd0 : 0 < d) (hW0 : 0 ≤ W) :
    ∑ j ∈ Finset.range n, (steps j).budgetSpend
      ≤ (M.objective (t 0) - ε + d) / d * W := by
  have hn : (n : ℝ) ≤ (M.objective (t 0) - ε + d) / d := by
    rw [le_div_iff₀ hd0]
    linarith
  have hsum : ∑ j ∈ Finset.range n, (steps j).budgetSpend ≤ n * W := by
    calc ∑ j ∈ Finset.range n, (steps j).budgetSpend
          ≤ ∑ _j ∈ Finset.range n, W := Finset.sum_le_sum hW
      _ = n * W := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hstep : (n : ℝ) * W ≤ (M.objective (t 0) - ε + d) / d * W :=
    mul_le_mul_of_nonneg_right hn hW0
  calc ∑ j ∈ Finset.range n, (steps j).budgetSpend ≤ (n : ℝ) * W := hsum
    _ ≤ (M.objective (t 0) - ε + d) / d * W := hstep

/-- The idealized total-compute product `(Δ₀/d)·W`: the budget-to-
quality functional minimized over the empirical (d, W) frontier
(the DEFINITION the tradeoff theorem and the anchors speak about;
noncomputable — ℝ division). -/
noncomputable def totalComputeProduct (Δ d W : ℝ) : ℝ := Δ / d * W

/-- **The sparsity tradeoff, honest premise-form**: if the
COMPRESSED configuration's per-step descent constant is no better
than the dense one (`hdd : d ≤ d'` — a PREMISE; no claim that
compression preserves the descent rate), the gap is nonnegative,
and the rank is low enough for the per-step advantage (`2k ≤ n`,
 `lowrank_op_count_le` condition), then the idealized
low-rank total compute `(Δ₀/d')·2kn` beats the dense `(Δ₀/d)·n²`:
on the (d, W) frontier the cheaper per-step work wins exactly when
the descent constant does not degrade. The work products are CITED
(`denseMatVecWork`, `lowRankMatVecWork`, `lowrank_op_ratio`), the
comparison is the only new content. -/
theorem lowrank_total_compute_le (Δ d d' : ℝ) {k n : ℕ}
    (hΔ : 0 ≤ Δ) (hd : 0 < d) (hd' : 0 < d') (hdd : d ≤ d')
    (hn : 0 < n) (h2k : 2 * k ≤ n) :
    totalComputeProduct Δ d' (lowRankMatVecWork k n : ℝ)
      ≤ totalComputeProduct Δ d (denseMatVecWork n : ℝ) := by
  have hr : (lowRankMatVecWork k n : ℝ)
      = (2 * (k : ℝ) / n) * (denseMatVecWork n : ℝ) :=
    lowrank_op_ratio k n hn
  have hnn : (0 : ℝ) < (n : ℝ) := by positivity
  have hfrac : (2 * (k : ℝ) / (n : ℝ)) ≤ 1 := by
    rw [div_le_one hnn]
    exact_mod_cast h2k
  have key : (2 * (k : ℝ) / (n : ℝ)) / d' ≤ 1 / d := by
    rw [div_le_div_iff₀ hd' hd]
    have h1 : 2 * (k : ℝ) / (n : ℝ) * d ≤ 1 * d :=
      mul_le_mul_of_nonneg_right hfrac hd.le
    linarith
  have hD : (0 : ℝ) ≤ (denseMatVecWork n : ℝ) := Nat.cast_nonneg _
  unfold totalComputeProduct
  rw [hr]
  calc (Δ / d') * ((2 * (k : ℝ) / (n : ℝ)) * (denseMatVecWork n : ℝ))
        = (Δ * (denseMatVecWork n : ℝ)) * ((2 * (k : ℝ) / (n : ℝ)) / d') := by
          field_simp
    _ ≤ (Δ * (denseMatVecWork n : ℝ)) * (1 / d) := by
          exact mul_le_mul_of_nonneg_left key (mul_nonneg hΔ hD)
    _ = Δ / d * (denseMatVecWork n : ℝ) := by field_simp

/-! ## The resource-ledger packaging -/

/-- **MAIN 3 — the compute budget certificate** (the C267-style
budget law for compute): a trajectory of uniform certified drop d
and EXACT per-step compute spend W satisfies the three ledger
obligations simultaneously — the quality floor is met
(`steps_to_quality`), the budget channel closes exactly
(`budget_telescope_gen`: `budget (t n) = budget (t 0) − n·W`, the
nonnegative remainder being the kernel's own `budget_nonneg`), and
the total-compute ledger is the exact sum `Σ spends = n·W`. The
end-to-end import for a consumer: one certificate, three books. -/
theorem compute_budget_certificate (deltaLevel : S → ℝ)
    (ε d W : ℝ) (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd : ∀ j ∈ Finset.range n, d ≤ (steps j).drop)
    (hgap : M.objective (t 0) - ε ≤ n * d)
    (hW : ∀ j ∈ Finset.range n, (steps j).budgetSpend = W) :
    M.objective (t n) ≤ ε
      ∧ M.budget (t n) = M.budget (t 0) - n * W
      ∧ ∑ j ∈ Finset.range n, (steps j).budgetSpend = n * W := by
  refine ⟨steps_to_quality M obl deltaLevel ε d n t steps hd hgap, ?_, ?_⟩
  · rw [budget_telescope_gen M obl deltaLevel n t steps,
      Finset.sum_congr rfl (fun j hj => hW j hj),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · rw [Finset.sum_congr rfl (fun j hj => hW j hj),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Numeric anchors: Δ₀ = 1, d = 0.01, W = 1000 -/

namespace Anchor

/-- The anchor gap closes in exactly 100 certified drops of 1/100:
`Δ₀ = 1`, `d = 1/100` — the premise `hgap` of
`steps_to_quality` instantiated (norm_num). -/
theorem anchor_gap : (1 : ℝ) - (1 : ℝ) / 100 ≤ 100 * ((1 : ℝ) / 100) := by norm_num

/-- The anchor total compute: `totalComputeProduct 1 (1/100) 1000
= 100000` — 100 certified steps at 1000 FLOPs of per-step work:
100000 total certified FLOPs to quality (norm_num). -/
theorem anchor_total : totalComputeProduct 1 ((1 : ℝ) / 100) 1000 = 100000 := by
  unfold totalComputeProduct; norm_num

end Anchor

end Hagi.Contracts.ComputeToQuality
