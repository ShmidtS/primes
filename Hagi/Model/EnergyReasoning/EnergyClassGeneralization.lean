/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.Concentration
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Model.EnergyReasoning.CramContracts

set_option linter.style.header false

/-!
# Finite-class generalization for learned energy models (C315)

P4 frontier item (ranked #3 in `.omc/analysis/period-c298-c312-analysis.md`):
what generalization claim is TRUE and cheaply provable for a learned-energy
solver.  The honest two-tier structure (research: `.tmp/C315/research.md`):

* TIER 1 (correctness, EXACT): accepted outputs are validated by the
  independent `CRAMAcceptedSolution` certificate (givens preserved +
  constraints satisfied, C267/C263).  Correctness does NOT depend on any
  generalization bound — the learned energy is quarantined to efficiency.
* TIER 2 (efficiency, LEARNED): over a FINITE hypothesis class of energy
  tables indexed by a `Fintype ι`, uniform convergence of the [0,1]-bounded
  PL loss holds via the C264 finite-family union composed with the C287
  concentration API (`concRadius`, `concRadius_valid`) — no new
  concentration mathematics.

What is NOT claimed (honesty ledger, research.md §2): no continuous
classes, no Rademacher/VC machinery, no stability, no claim that low PL
loss implies validity (that is exactly the C269 non-separation), no
distributional assumption beyond the explicit independent finite product.

The `[0,1]` bound on the loss `X k` is a PREMISE (the `[0,L]` scale route
exists via `FiniteFamilyConfidence.populationMean_le_empiricalMean_of_scale`).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Probability Hagi.Probability.FiniteFamilyConfidence

/-! ## Tier 2: uniform convergence over a finite energy class -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- C315 MAIN (uniform convergence, finite class): for a FINITE class of
energy tables indexed by `ι` with `[0,1]`-normalized PL losses `X k`, with
probability ≥ `1 − δ` EVERY hypothesis's population PL-loss is within
`concRadius (δ/|ι|) n` of its empirical loss.  This is the C264 finite
family union bound (`finite_family_upper_confidence`) at the C287 radius
`concRadius (δ/|class|) n` (`concRadius_valid`): the class-size penalty
is the standard `log |class|` structural-risk term on a finite class. -/
theorem finite_class_pl_uniform {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) {delta : ℝ} (hd1 : 0 < delta) (hd2 : delta < 1)
    (hcard : 0 < Fintype.card ι) :
    1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X k) ≤ empiricalMean (X k) ω +
        concRadius (delta / (Fintype.card ι : ℝ)) n) := by
  have hc : 0 < (Fintype.card ι : ℝ) := by positivity
  have hc1 : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hcard
  have hlt : delta / (Fintype.card ι : ℝ) < 1 :=
    (div_lt_one₀ hc).mpr (lt_of_lt_of_le hd2 hc1)
  have hdv : concConfidence
        (concRadius (delta / (Fintype.card ι : ℝ)) n) n ≤
      delta / (Fintype.card ι : ℝ) :=
    concRadius_valid (div_pos hd1 hc) hlt hn
  have hrpos : 0 < concRadius (delta / (Fintype.card ι : ℝ)) n := by
    unfold concRadius
    refine Real.sqrt_pos.mpr (div_pos ?_ (by positivity))
    exact Real.log_pos (by
      rw [lt_div_iff₀ (div_pos hd1 hc), one_mul]
      exact hlt)
  have hconf := finite_family_upper_confidence p hp X hX hn _ hrpos
  have hbudget : (Fintype.card ι : ℝ) * concConfidence
      (concRadius (delta / (Fintype.card ι : ℝ)) n) n ≤ delta := by
    have h2 := mul_le_mul_of_nonneg_left hdv hc.le
    rw [mul_div_cancel₀ _ hc.ne'] at h2
    exact h2
  calc 1 - delta ≤ 1 - (Fintype.card ι : ℝ) * concConfidence
        (concRadius (delta / (Fintype.card ι : ℝ)) n) n := by
          refine le_of_eq_of_le rfl ?_
          rw [sub_le_sub_iff_left]
          exact hbudget
    _ ≤ prodPq p (fun ω => ∀ k,
        populationMean p (X k) ≤ empiricalMean (X k) ω +
          concRadius (delta / (Fintype.card ι : ℝ)) n) := by
          exact hconf

/-- C315 margin corollary (finite-class argmax identification): on the
simultaneous two-sided event of `finite_family_abs_error_confidence`
(C264), if the empirical winner `best`'s margin over every other
hypothesis is at least `2 * eps`, then `best` is the TRUE population-best
hypothesis: population loss of `best` ≤ population loss of every `k`.
Standard finite-class identification (the informal "gap > 2·radius"
condition; the non-strict `≤` form here covers it). -/
theorem finite_class_pl_margin_argmax {n : ℕ} {ι : Type} [Fintype ι]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) (best : ι)
    (hmargin : ∀ ω k,
      2 * eps ≤ empiricalMean (X k) ω - empiricalMean (X best) ω) :
    1 - 2 * (Fintype.card ι : ℝ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ k,
        populationMean p (X best) ≤ populationMean p (X k)) := by
  refine le_trans (finite_family_abs_error_confidence p hp X hX hn eps heps) ?_
  apply prodPq_mono p hp
  intro ω hω k
  by_cases hk : k = best
  · subst hk
    exact le_refl _
  · have hb := abs_le.mp (hω best)
    have hkk := abs_le.mp (hω k)
    have hm := hmargin ω k
    have h1 : populationMean p (X best) - empiricalMean (X best) ω ≤ eps := hb.2
    have h2 : empiricalMean (X k) ω - populationMean p (X k) ≤ eps := by
      have := hkk.1
      linarith
    linarith

/-! ## Tier 1: exact correctness through the independent validator -/

section Solver

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- C315 TIER-1 MAIN (exact correctness, energy-free): any ACCEPTED
solution of the learned-energy solver — acceptance goes through the
independent `CRAMAcceptedSolution` certificate (C267), never through the
energy — preserves every given cell BOTH in the certificate and ON THE
BOARD, and satisfies every constraint on the board.  Correctness does not
depend on any generalization bound: the statement mentions neither sample
nor energy, by construction. -/
theorem learned_solver_correctness_exact {B : ι → α → ℝ}
    {K : ι → ι → α → α → ℝ} {C : ι → α → Prop} {s : CRAMState ι α}
    (sol : CRAMAcceptedSolution B K C s) :
    (∀ i a, s.problem.givens i = some a →
        sol.cert.y i = a ∧ s.board i = a) ∧
      ∀ i, C i (s.board i) := by
  constructor
  · intro i a h
    exact ⟨sol.cert.preserves_givens i a h,
      (sol.board_agrees i).symm.trans (sol.cert.preserves_givens i a h)⟩
  · intro i
    have hci := sol.cert.satisfies_constraints i
    exact sol.board_agrees i ▸ hci

/-- C315 QUARANTINE (two-tier separation, failure side): even on the
COMPLEMENT of the uniform-convergence event of `finite_class_pl_uniform`,
every accepted solution is STILL valid.  Generalization debt is confined
to efficiency (how often search succeeds, how tight the optional energy
bound is), never to correctness. -/
theorem accepted_solution_valid_of_generalization_failure
    {n : ℕ} {V : Type} [Fintype V] [Nonempty V] {ι : Type}
    [Fintype ι] [DecidableEq ι] {α : Type} [Fintype α] [DecidableEq α]
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) {delta : ℝ} (hd1 : 0 < delta) (hd2 : delta < 1)
    (hcard : 0 < Fintype.card ι)
    (hfail : ¬ (1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X k) ≤ empiricalMean (X k) ω +
        concRadius (delta / (Fintype.card ι : ℝ)) n)))
    {B : ι → α → ℝ} {K : ι → ι → α → α → ℝ} {C : ι → α → Prop}
    {s : CRAMState ι α}
    (sol : CRAMAcceptedSolution B K C s) :
    (∀ i a, s.problem.givens i = some a →
        sol.cert.y i = a ∧ s.board i = a) ∧
      ∀ i, C i (s.board i) :=
  learned_solver_correctness_exact sol

end Solver

/-! ## Numeric anchor -/

/-- C315 numeric anchor: at `m = 1000` samples, class size `|ι| = 10`,
`δ = 0.05`, the per-class budget is `δ/|ι| = 0.005` and the radius is
`concRadius 0.005 1000 = sqrt (log 200 / 2000) ≈ 0.0515` (float, for
orientation only).  The PROVED bound is the honest loose form
`≤ 1/15 ≈ 0.0667` via `log 200 ≤ 8` (since `200 ≤ 2 ^ 8 ≤ e ^ 8`,
using `2 = 1 + 1 ≤ exp 1`). -/
theorem concRadius_anchor_315 :
    concRadius (0.05 / 10) 1000 ≤ 1 / 15 := by
  have h200 : (1:ℝ) / (0.05 / 10) = 200 := by norm_num
  have hlog : Real.log 200 ≤ 8 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc 200 ≤ (2:ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 :=
          pow_le_pow_left₀ (by norm_num)
            (le_trans (by rw [add_comm]; norm_num) (Real.add_one_le_exp 1)) 8
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hnum : Real.log (1 / (0.05 / 10)) / (2 * (1000 : ℝ)) ≤ (1 / 15) ^ 2 := by
    have hdiv : Real.log 200 / (2 * (1000 : ℝ)) ≤ (1 / 15) ^ 2 := by
      have h8 : (8:ℝ) / (2 * 1000) ≤ (1 / 15) ^ 2 := by norm_num
      calc Real.log 200 / (2 * (1000 : ℝ))
          ≤ 8 / (2 * (1000 : ℝ)) :=
            div_le_div_of_nonneg_right hlog (by norm_num)
        _ ≤ (1 / 15) ^ 2 := h8
    rw [h200]
    exact hdiv
  unfold concRadius
  rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 15)]
  exact Real.sqrt_le_sqrt hnum

end Hagi.Model.EnergyReasoning
