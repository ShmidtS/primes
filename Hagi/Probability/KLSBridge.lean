/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# KLSBridge: dimension-free gradient noise from a Poincaré interface

Source context: the KLS conjecture program (Kannan–Lovász–
Simonovits; the Oct 2026 preprint arXiv:2610.01447v2 claims an
O(1) bound for isotropic log-concave measures — not yet
independently verified, and its constant is not taken here).

**Honest interface, not an imported constant.** We formalize
the *shape* of the result: a Poincaré-type hypothesis on the
data distribution (hpoincare: every direction's variance of
the per-sample gradient projection is bounded by C times the
expected squared sensitivity), an operator-style Jacobian
bound (hop), and we derive, with NO dimension-dependent
factors:

* `gradCovBound`: for every direction a,
  Var[⟪a, g(X)⟫] ≤ C·L²·‖a‖² — i.e. Cov(g) ⪯ C·L²·I in
  quadratic-form sense.
* `uncorrMeanVar`: for B uncorrelated copies, the second
  moment of the average is the average of second moments
  (the cross terms vanish — the varianceHalving mechanism).
* `expQ_varEq`: the second central moment equals the
  expQ-variance.
* `klsBatchNoise`: combining both, the centered batch
  projection satisfies the dimension-free noise bound
  E[(⟪a, ĝ_B⟫ − E⟪a, ĝ_B⟫)²] ≤ C·L²·‖a‖²/B — the batch
  gradient noise: data geometry → gradient variance → batch
  noise, σ² ≲ C·L²/B.
* `klsChebyshev`: P[|F| ≥ t] ≤ V/t² — the σ-link into SafeQP
  robustness.

The log-concavity of real HAGI data is not claimed: the
Poincaré property enters as an explicit hypothesis, exactly
like the empirical `h_emp_` premises elsewhere in HAGI.
-/

namespace Hagi.KLS

open Finset

/-- Expectation under a finite probability vector. -/
def expQ {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, q x * f x

/-- Squared norm of a direction. -/
def sqN {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑ i, (a i) ^ 2

/-- Projection onto a direction. -/
def proj {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, a i * x i

/-- Directional variance of a gradient field. -/
def gradVar {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω] (q : Ω → ℝ)
    (g : Ω → Fin n → ℝ) (a : Fin n → ℝ) : ℝ :=
  expQ q (fun x => (proj a (g x)) ^ 2) - (expQ q (fun x => proj a (g x))) ^ 2

/-- Expectation is monotone. -/
theorem expQ_mono {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    (h0 : ∀ x, 0 ≤ q x) (f g : Ω → ℝ) (h : ∀ x, f x ≤ g x) :
    expQ q f ≤ expQ q g := by
  unfold expQ
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (h0 x)

/-- **The direction-form covariance bound** (Cov ⪯ C·L²·I in
quadratic-form sense): given a Poincaré-type hypothesis on the
data distribution (every direction's projected variance is
bounded by C times the expected squared sensitivity along that
direction) and an operator-style sensitivity bound
((sens a x)² ≤ L²·‖a‖² pointwise), the gradient variance in
every direction is dimension-free: Var[⟪a, g(X)⟫] ≤ C·L²·‖a‖².
The constant C is the interface constant — whatever an
independently verified KLS/Poincaré theorem supplies. -/
theorem gradCovBound {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (g : Ω → Fin n → ℝ) (C L : ℝ) (hC : 0 ≤ C)
    (sens : (Fin n → ℝ) → Ω → ℝ)
    (hpoincare : ∀ a : Fin n → ℝ,
      gradVar q g a ≤ C * expQ q (fun x => (sens a x) ^ 2))
    (hop : ∀ (a : Fin n → ℝ) (x : Ω), (sens a x) ^ 2 ≤ L ^ 2 * sqN a)
    (a : Fin n → ℝ) :
    gradVar q g a ≤ C * L ^ 2 * sqN a := by
  refine le_trans (hpoincare a) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (expQ_mono q hq0 _ _ (fun x => hop a x)) hC) ?_
  have hconst : expQ q (fun _ => L ^ 2 * sqN a) = L ^ 2 * sqN a := by
    unfold expQ
    rw [← Finset.sum_mul, hq1, one_mul]
  rw [hconst, mul_assoc]

/-- **Uncorrelated averaging**: for B pairwise uncorrelated
copies on the same space, the second moment of the average is
the average of the second moments divided by B² (the cross
terms vanish — the varianceHalving mechanism in the
correlation-free setting). -/
theorem uncorrMeanVar {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    {B : ℕ} (h : Fin B → Ω → ℝ)
    (huncorr : ∀ i j, i ≠ j → expQ q (fun x => h i x * h j x) = 0) :
    expQ q (fun x => (∑ i, h i x / B) ^ 2)
      = (∑ i, expQ q (fun x => (h i x) ^ 2)) / B ^ 2 := by
  have hexp : expQ q (fun x => (∑ i, h i x) ^ 2)
      = ∑ i, ∑ j, expQ q (fun x => h i x * h j x) := by
    unfold expQ
    rw [show (∑ x, q x * (∑ i, h i x) ^ 2)
        = ∑ x, ∑ i, ∑ j, q x * (h i x * h j x) from by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.mul_sum],
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  -- kill the off-diagonal terms
  have hdiag : ∑ i, ∑ j, expQ q (fun x => h i x * h j x)
      = ∑ i, expQ q (fun x => (h i x) ^ 2) := by
    have hite : ∀ i j : Fin B, expQ q (fun x => h i x * h j x)
        = if j = i then expQ q (fun x => (h i x) ^ 2) else 0 := by
      intro i j
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        unfold expQ
        exact Finset.sum_congr rfl fun x _ => by ring
      · rw [ite_eq_right hj, huncorr i j (Ne.symm hj)]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hite i j)),
      show (∑ i, ∑ j, (if j = i then expQ q (fun x => (h i x) ^ 2) else 0))
        = ∑ i, expQ q (fun x => (h i x) ^ 2) from by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ j, (if j = i then expQ q (fun x => (h i x) ^ 2) else 0))
            = expQ q (fun x => (h i x) ^ 2) from by
          rw [show (∑ j, (if j = i then expQ q (fun x => (h i x) ^ 2) else 0))
              = ∑ j, (if i = j then expQ q (fun x => (h i x) ^ 2) else 0) from
                Finset.sum_congr rfl (fun j _ => by
                  by_cases hj : j = i
                  · subst hj; rfl
                  · rw [ite_eq_right hj, ite_eq_right (Ne.symm hj)]),
            Fintype.sum_ite_eq]]]
  -- assemble with the division
  have hstep1 : expQ q (fun x => (∑ i, h i x / B) ^ 2)
      = expQ q (fun x => ((∑ i, h i x) ^ 2) / B ^ 2) :=
    Finset.sum_congr rfl fun x _ => by
      show q x * (∑ i, h i x / ↑B) ^ 2 = q x * ((∑ i, h i x) ^ 2 / ↑B ^ 2)
      rw [show (∑ i, h i x / ↑B) = (∑ i, h i x) / ↑B from
            (Finset.sum_div (Finset.univ : Finset (Fin B))
              (fun i => h i x) (↑B)).symm,
        div_pow]
  have hstep2 : expQ q (fun x => ((∑ i, h i x) ^ 2) / B ^ 2)
      = (expQ q (fun x => (∑ i, h i x) ^ 2)) / B ^ 2 := by
    unfold expQ
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hstep1, hstep2, hexp, hdiag]

/-- Variance identity in expectation form: the second central
moment equals the expQ-variance. -/
theorem expQ_varEq {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    (hq1 : ∑ x, q x = 1) (F : Ω → ℝ) :
    expQ q (fun x => (F x - expQ q F) ^ 2)
      = expQ q (fun x => F x ^ 2) - (expQ q F) ^ 2 := by
  set m := expQ q F with hm
  unfold expQ
  have hlin1 : (∑ x, q x * (-2 * m * F x)) = -2 * m * (∑ x, q x * F x) := by
    rw [show (∑ x, q x * (-2 * m * F x)) = ∑ x, (-2 * m) * (q x * F x) from
          Finset.sum_congr rfl fun x _ => by ring,
      ← Finset.mul_sum]
  have hlin2 : (∑ x, q x * m ^ 2) = (∑ x, q x) * m ^ 2 := by
    rw [show (∑ x, q x * m ^ 2) = ∑ x, m ^ 2 * q x from
          Finset.sum_congr rfl fun x _ => by ring,
      ← Finset.mul_sum]
    exact mul_comm _ _
  have hsplit : (∑ x, q x * (F x - m) ^ 2)
      = (∑ x, q x * F x ^ 2) + (-2 * m * (∑ x, q x * F x)
        + (∑ x, q x) * m ^ 2) := by
    rw [show (∑ x, q x * (F x - m) ^ 2)
        = ∑ x, (q x * F x ^ 2 + (q x * (-2 * m * F x) + q x * m ^ 2)) from
          Finset.sum_congr rfl fun x _ => by ring,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hlin1, hlin2]
  have hSm : (∑ x, q x * F x) = m := rfl
  rw [hsplit, hq1, one_mul, hm, hSm]
  ring

/-- **The batch gradient-noise bound** (KLS → gradient
variance → batch noise): given the Poincaré interface and the
operator-style sensitivity bound, and B uncorrelated
per-sample gradient fields, the batch-averaged gradient
projection satisfies the dimension-free noise bound
E[(⟪a, ĝ_B⟫ − E⟪a, ĝ_B⟫)²] ≤ C·L²·‖a‖²/B. Data geometry flows
all the way to the SafeQP noise parameter: σ² ≲ C·L²/B. -/
theorem klsBatchNoise {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (C L : ℝ) (hC : 0 ≤ C)
    (sens : (Fin n → ℝ) → Ω → ℝ)
    (hpoincare : ∀ (g : Ω → Fin n → ℝ) (a : Fin n → ℝ),
      gradVar q g a ≤ C * expQ q (fun x => (sens a x) ^ 2))
    (hop : ∀ (a : Fin n → ℝ) (x : Ω), (sens a x) ^ 2 ≤ L ^ 2 * sqN a)
    {B : ℕ} (hB : 0 < B) (g : Fin B → Ω → Fin n → ℝ) (a : Fin n → ℝ)
    (huncorr : ∀ i j, i ≠ j →
      expQ q (fun x => (proj a (g i x) - expQ q (fun y => proj a (g i y)))
        * (proj a (g j x) - expQ q (fun y => proj a (g j y)))) = 0) :
    expQ q (fun x => (∑ i, proj a (g i x) / B
        - (∑ i, expQ q (fun y => proj a (g i y))) / B) ^ 2)
      ≤ C * L ^ 2 * sqN a / B := by
  set mu : Fin B → ℝ := fun i => expQ q (fun y => proj a (g i y)) with hmu
  set h : Fin B → Ω → ℝ :=
    fun i x => proj a (g i x) - mu i with hh
  -- per-sample second central moment = gradVar, bounded by gradCovBound
  have hvar : ∀ i, expQ q (fun x => (h i x) ^ 2) ≤ C * L ^ 2 * sqN a := by
    intro i
    have heq : expQ q (fun x => (h i x) ^ 2)
        = gradVar q (g i) a := by
      rw [hh, gradVar]
      exact expQ_varEq q hq1 (fun x => proj a (g i x))
    rw [heq]
    exact gradCovBound q hq0 hq1 (g i) C L hC sens
      (fun a' => hpoincare (g i) a') hop a
  -- the target average is the average of the centered deviations
  rw [show expQ q (fun x => (∑ i, proj a (g i x) / B
        - (∑ i, mu i) / B) ^ 2)
      = expQ q (fun x => (∑ i, h i x / B) ^ 2) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    show q x * ((∑ i, proj a (g i x) / B - (∑ i, mu i) / B) ^ 2)
      = q x * ((∑ i, h i x / B) ^ 2)
    rw [hh]
    congr 2
    have e1 : (∑ i, proj a (g i x) / ↑B) = (∑ i, proj a (g i x)) / ↑B :=
      (Finset.sum_div (Finset.univ : Finset (Fin B))
        (fun i => proj a (g i x)) ↑B).symm
    rw [e1, div_sub_div_same, ← Finset.sum_sub_distrib, Finset.sum_div]]
  have hu : ∀ i j, i ≠ j → expQ q (fun x => h i x * h j x) = 0 := by
    intro i j hij
    rw [hh]
    exact huncorr i j hij
  rw [uncorrMeanVar q h hu]
  have hsum : (∑ i, expQ q (fun x => (h i x) ^ 2))
      ≤ ((Finset.univ : Finset (Fin B)).card : ℝ) * (C * L ^ 2 * sqN a) := by
    calc (∑ i, expQ q (fun x => (h i x) ^ 2))
        ≤ ∑ _i ∈ (Finset.univ : Finset (Fin B)), (C * L ^ 2 * sqN a) :=
          Finset.sum_le_sum fun i _ => hvar i
      _ = ((Finset.univ : Finset (Fin B)).card : ℝ) * (C * L ^ 2 * sqN a) := by
          rw [Finset.sum_const]
          simp
  rw [show ((Finset.univ : Finset (Fin B)).card : ℝ) = B from by simp] at hsum
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsum]

/-- **The SafeQP σ-link** (Chebyshev direction bound): if the
centered batch projection has second moment ≤ V, then the
deviation exceeds t in probability at most V/t² — the noise
parameter of a robust SafeQP layer inherits the KLS chain:
σ² ≲ C·L²/B per direction. -/
theorem klsChebyshev {Ω : Type*} [Fintype Ω] (q : Ω → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (V t : ℝ) (ht : 0 < t)
    (F : Ω → ℝ) (hV : expQ q (fun x => F x ^ 2) ≤ V) :
    (∑ x ∈ Finset.univ.filter (fun x => t ≤ |F x|), q x) ≤ V / t ^ 2 := by
  have hsub : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |F x|), q x)
      ≤ (∑ x ∈ Finset.univ.filter (fun x => t ≤ |F x|),
          q x * F x ^ 2 / t ^ 2) := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mem_filter] at hx
    have hF : t ^ 2 ≤ (F x) ^ 2 := by
      have h1 : |t| ≤ |F x| :=
        abs_le.mpr ⟨by nlinarith [ht, abs_nonneg (F x)], hx.2⟩
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ |F x| ^ 2 :=
              sq_le_sq' (by linarith [abs_nonneg t, abs_nonneg (F x)]) h1
        _ = (F x) ^ 2 := sq_abs (F x)
    have hqF : q x * t ^ 2 ≤ q x * (F x) ^ 2 :=
      mul_le_mul_of_nonneg_left hF (hq0 x)
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    field_simp
    linarith
  refine le_trans hsub ?_
  calc (∑ x ∈ Finset.univ.filter (fun x => t ≤ |F x|), q x * F x ^ 2 / t ^ 2)
      ≤ (∑ x, q x * F x ^ 2 / t ^ 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : t ≤ |F x|
        · simp only [hx, ite_true]
          exact le_rfl
        · simp only [hx, ite_false]
          exact div_nonneg (mul_nonneg (hq0 x) (by positivity)) (by positivity)
    _ = (∑ x, q x * F x ^ 2) / t ^ 2 := by
        rw [Finset.sum_div]
    _ ≤ V / t ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_right hV (by positivity)

end Hagi.KLS
