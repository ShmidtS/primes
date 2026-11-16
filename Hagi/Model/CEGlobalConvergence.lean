/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Core.Concat
import Hagi.Model.SoftmaxHead

/-!
# Global convergence for the log-linear CE head under PL

A14 research bridge #6.  The repo's CE descent theory
(`Hagi.Model.CEDescent`, the `BatchCEDescent*` family) gives local
one-step certificates; this module adds the global statement that
was missing: minimizing one-hot cross-entropy over a log-linear
(softmax) head under a Polyak-Łojasiewicz (PL) condition yields a
geometric decay of the loss gap under fixed-step gradient descent.

The two halves are deliberately independent:

* convexity of the log-linear CE in the parameters
  (`ce_loglinear_convex`): `Hagi.ceOneHot t (X *ᵥ θ)` is a
  log-sum-exp of linear functions of `θ` minus a linear functional,
  hence convex.  This is the honesty theorem that makes the PL
  premise plausible for the linear head (`LogitMap.ident` in
  `Hagi.Model.SoftmaxHead`: `headCE .ident t z = Hagi.ceOneHot t z`
  by `headCE_ident`).

* the PL rate (`pl_descent_step`, `ce_global_convergence`): on an
  abstract real inner product space, the descent lemma with
  smoothness constant `L` (premise form, following the repo's
  premise-ledger descent pattern) plus the PL inequality in
  gradient-norm form `2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2` gives
  the one-step contraction with factor `1 - μ / L` and, by
  induction over the gradient-descent iterate, the geometric rate
  `f (plStep^[T] θ₀) - fstar ≤ (1 - μ / L) ^ T * (f θ₀ - fstar)`.
  No convexity is needed for the rate itself: PL + smoothness
  suffice; convexity is the separate statement above.

## Honest limitations (pinned)

* Convexity is proved for the **linear** head only.  The saturating
  head (`LogitMap.tanh`) is non-convex in `θ`; no convexity claim
  is made for it.
* The smoothness constant `L` is an explicit premise; it is not
  derived from the operator norm of `X`.  Likewise the PL premise
  is not discharged for any concrete feature matrix `X` and target
  `t`: no gradient-norm verification of CE exists in this snapshot
  (the derivative itself is `CEGradient.fderiv_ceOneHot_mulVec`).
* Fixed step `1 / L` only; no adaptive step sizes.
* `ce_loglinear_convex` is stated on the plain parameter space
  `Fin d → ℝ`.  Transporting `ConvexOn` to the
  `EuclideanSpace ℝ (Fin d)` carrier of `Hagi.Model.CEGradient` is
  a linear-isometry transport not formalized here.
* The O(1/T) rate without PL (Fejér monotonicity, telescoping,
  averaged iterate) is not formalized here.

Reference search (research notes, `.tmp/C351/research.md`) found no
logsumexp or PL API in the pinned Mathlib commit; the two-point
weighted AM-GM route adapts the normalization pattern of
`lse_mean_le_mean_lse` from `Hagi.Core.Concat`.
-/

set_option relaxedAutoImplicit false

open scoped Matrix InnerProductSpace

namespace Hagi.Model.CEGlobalConvergence

/-! ## Part 1: convexity of the log-linear CE in the parameters -/

section Convexity

variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- Two-point weighted Hölder for the exponential sum: for a weight
`a ∈ [0, 1]`, the sum of `exp (a * z₁ v + (1 - a) * z₂ v)` is
bounded by `S ^ a * T ^ (1 - a)` with `S`, `T` the two exponential
sums.  Per-coordinate weighted AM-GM (`Real.
geom_mean_le_arith_mean2_weighted`) summed over the vocabulary;
the per-child masses are `1` after normalization. -/
theorem holder_exp_sum (a : ℝ) (ha : a ∈ Set.Icc 0 1) (z₁ z₂ : V → ℝ) :
    ∑ v, Real.exp (a * z₁ v + (1 - a) * z₂ v)
      ≤ (∑ v, Real.exp (z₁ v)) ^ a * (∑ v, Real.exp (z₂ v)) ^ (1 - a) := by
  have ha' : 0 ≤ a := ha.1
  have hb' : 0 ≤ 1 - a := by linarith [ha.1, ha.2]
  have hw : a + (1 - a) = 1 := by ring
  have hSpos : 0 < ∑ v, Real.exp (z₁ v) := Hagi.Core.exp_sum_pos z₁
  have hTpos : 0 < ∑ v, Real.exp (z₂ v) := Hagi.Core.exp_sum_pos z₂
  set S : ℝ := ∑ v, Real.exp (z₁ v) with hSdef
  set T : ℝ := ∑ v, Real.exp (z₂ v) with hTdef
  set p : V → ℝ := fun v => Real.exp (z₁ v) / S with hp
  set q : V → ℝ := fun v => Real.exp (z₂ v) / T with hq
  have hSa : 0 < S ^ a := Real.rpow_pos_of_pos hSpos a
  have hTb : 0 < T ^ (1 - a) := Real.rpow_pos_of_pos hTpos (1 - a)
  have hppos : ∀ v, 0 ≤ p v :=
    fun v => div_nonneg (Real.exp_nonneg _) hSpos.le
  have hqpos : ∀ v, 0 ≤ q v :=
    fun v => div_nonneg (Real.exp_nonneg _) hTpos.le
  have hamgm : ∀ v, p v ^ a * q v ^ (1 - a) ≤ a * p v + (1 - a) * q v :=
    fun v => Real.geom_mean_le_arith_mean2_weighted
      ha' hb' (hppos v) (hqpos v) hw
  have hrew : ∀ v,
      Real.exp (a * z₁ v + (1 - a) * z₂ v)
        = S ^ a * T ^ (1 - a) * (p v ^ a * q v ^ (1 - a)) := by
    intro v
    have h1 : Real.exp (a * z₁ v) = (Real.exp (z₁ v)) ^ a := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (z₁ v)) a, Real.log_exp,
        mul_comm]
    have h2 : Real.exp ((1 - a) * z₂ v) = (Real.exp (z₂ v)) ^ (1 - a) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (z₂ v)) (1 - a), Real.log_exp,
        mul_comm]
    rw [Real.exp_add, h1, h2, hp, hq,
      Real.div_rpow (Real.exp_nonneg _) hSpos.le a,
      Real.div_rpow (Real.exp_nonneg _) hTpos.le (1 - a)]
    field_simp
  have hp1 : ∑ v, p v = 1 := by
    show ∑ v, Real.exp (z₁ v) / S = 1
    rw [← Finset.sum_div, hSdef, div_self (ne_of_gt hSpos)]
  have hq1 : ∑ v, q v = 1 := by
    show ∑ v, Real.exp (z₂ v) / T = 1
    rw [← Finset.sum_div, hTdef, div_self (ne_of_gt hTpos)]
  have hmass : ∑ v, (a * p v + (1 - a) * q v) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1]
    ring
  have hsumle : ∑ v, (p v ^ a * q v ^ (1 - a))
      ≤ ∑ v, (a * p v + (1 - a) * q v) :=
    Finset.sum_le_sum (fun v _ => hamgm v)
  rw [Finset.sum_congr rfl (fun v _ => hrew v)]
  calc ∑ v, S ^ a * T ^ (1 - a) * (p v ^ a * q v ^ (1 - a))
      = S ^ a * T ^ (1 - a) * ∑ v, (p v ^ a * q v ^ (1 - a)) := by
        rw [← Finset.mul_sum]
    _ ≤ S ^ a * T ^ (1 - a) * ∑ v, (a * p v + (1 - a) * q v) :=
        mul_le_mul_of_nonneg_left hsumle (mul_nonneg hSa.le hTb.le)
    _ = S ^ a * T ^ (1 - a) * 1 := by rw [hmass]
    _ = S ^ a * T ^ (1 - a) := mul_one _

/-- Global convexity of the log-sum-exp: `Hagi.lse` is `ConvexOn`
the whole logit space.  Generalizes `lse_midpoint_le` (the weight
`1/2` instance) to arbitrary weights via `holder_exp_sum` and
monotonicity of the logarithm. -/
theorem convexOn_lse : ConvexOn ℝ (Set.univ : Set (V → ℝ)) Hagi.lse := by
  refine ⟨convex_univ, fun x _ y _ c d hc hd hcd => ?_⟩
  have hc' : c ∈ Set.Icc 0 1 := ⟨hc, by linarith [hd, hcd]⟩
  have hS : (0 : ℝ) < ∑ v, Real.exp (x v) := Hagi.Core.exp_sum_pos x
  have hT : (0 : ℝ) < ∑ v, Real.exp (y v) := Hagi.Core.exp_sum_pos y
  have hH := holder_exp_sum c hc' x y
  have hcd1 : 1 - c = d := by linarith [hcd]
  rw [hcd1] at hH
  have hfun : ∀ v, (c • x + d • y) v = c * x v + d * y v := by
    intro v
    simp [smul_eq_mul]
  show Real.log (∑ v, Real.exp ((c • x + d • y) v))
      ≤ c * Real.log (∑ v, Real.exp (x v))
        + d * Real.log (∑ v, Real.exp (y v))
  rw [Finset.sum_congr rfl (fun v _ => by rw [hfun])]
  have hrr : c * Real.log (∑ v, Real.exp (x v))
      + d * Real.log (∑ v, Real.exp (y v))
      = Real.log ((∑ v, Real.exp (x v)) ^ c * (∑ v, Real.exp (y v)) ^ d) := by
    rw [← Real.log_rpow hS, ← Real.log_rpow hT,
      Real.log_mul (by positivity) (by positivity)]
  rw [hrr]
  exact Real.log_le_log (Hagi.Core.exp_sum_pos (fun v => c * x v + d * y v)) hH

/-- The log-linear CE head is convex in the parameters: `θ ↦
Hagi.ceOneHot t (X *ᵥ θ)` is convex on the whole parameter space
`Fin d → ℝ`.  This is the linear-head (`LogitMap.ident`)
convexity behind the PL premise; no claim is made for the
saturating head.  A log-sum-exp of linear functions (`convexOn_lse`
composed with `Matrix.mulVecLin`) minus a linear functional. -/
theorem ce_loglinear_convex (X : Matrix V (Fin d) ℝ) (t : V) :
    ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun θ => Hagi.ceOneHot t (X *ᵥ θ)) := by
  have h1 : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun θ : Fin d → ℝ => Hagi.lse (X *ᵥ θ)) := by
    have h := (convexOn_lse (V := V)).comp_linearMap (Matrix.mulVecLin X)
    rwa [Set.preimage_univ] at h
  have h2 : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun θ : Fin d → ℝ => -((X *ᵥ θ) t)) := by
    refine ⟨convex_univ, fun x _ y _ c d _ _ hcd => ?_⟩
    have hmul : (X *ᵥ (c • x + d • y)) t
        = c * (X *ᵥ x) t + d * (X *ᵥ y) t := by
      have hmix : (X *ᵥ (c • x + d • y))
          = c • (X *ᵥ x) + d • (X *ᵥ y) := by
        simp [Matrix.mulVec_add, Matrix.mulVec_smul, smul_eq_mul]
      rw [hmix]
      simp [smul_eq_mul]
    show -(X *ᵥ (c • x + d • y)) t
        ≤ c * (-(X *ᵥ x) t) + d * (-(X *ᵥ y) t)
    rw [hmul, neg_add, ← mul_neg, ← mul_neg]
  have h3 := h1.add h2
  convert h3 using 1
  funext θ
  show Hagi.lse (X *ᵥ θ) - (X *ᵥ θ) t
      = Hagi.lse (X *ᵥ θ) + -((X *ᵥ θ) t)
  rw [sub_eq_add_neg]

end Convexity

/-! ## Part 2: the PL rate on an abstract inner product space -/

section PL

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One gradient-descent step with the canonical smoothness step
size `1 / L`. -/
noncomputable def plStep (grad : E → E) (L : ℝ) : E → E :=
  fun θ => θ - (1 / L) • grad θ

/-- One-step PL descent: under the descent lemma with smoothness
constant `L` (premise form) and the PL inequality in gradient-norm
form `2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2`, a single
`plStep` contracts the loss gap by the factor `1 - μ / L`.  Pure
first-order arithmetic; no convexity is used. -/
theorem pl_descent_step (f : E → ℝ) (grad : E → E) (L μ fstar : ℝ)
    (θ : E) (hL : 0 < L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (h_pl : ∀ x : E, 2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2)
    (h_floor : ∀ x : E, fstar ≤ f x) :
    f (plStep grad L θ) - fstar
      ≤ (1 - μ / L) * (f θ - fstar) := by
  rw [plStep]
  have hstep := h_smooth θ (θ - (1 / L) • grad θ)
  have hin : ⟪grad θ, θ - (1 / L) • grad θ - θ⟫_ℝ
      = -(1 / L) * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hin] at hstep
  have hcoef : L / 2 * ((1 / L) ^ 2 * ‖grad θ‖ ^ 2)
      = ‖grad θ‖ ^ 2 / (2 * L) := by
    field_simp
  have hnorm : ‖θ - (1 / L) • grad θ - θ‖ ^ 2
      = (1 / L) ^ 2 * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    ring
  rw [hnorm, hcoef] at hstep
  have hXY : f θ + -(1 / L) * ‖grad θ‖ ^ 2 + ‖grad θ‖ ^ 2 / (2 * L)
      = f θ - ‖grad θ‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hXY] at hstep
  have hA : 0 ≤ f θ - fstar := sub_nonneg.2 (h_floor θ)
  have hg : 2 * μ * (f θ - fstar) ≤ ‖grad θ‖ ^ 2 := h_pl θ
  have hd : (1 - μ / L) * (f θ - fstar)
      = (f θ - fstar) - μ * (f θ - fstar) / L := by
    ring
  rw [hd]
  have hmu : μ * (f θ - fstar) / L ≤ ‖grad θ‖ ^ 2 / (2 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hg, hL]
  linarith

/-- Global geometric convergence under PL: after `T` steps of
`plStep grad L` the loss gap decays geometrically with factor
`1 - μ / L`.  The premise `h_rate : μ ≤ L` keeps the factor
nonnegative (the contraction reading); PL + smoothness suffice —
convexity is not a premise. -/
theorem ce_global_convergence (f : E → ℝ) (grad : E → E) (L μ fstar : ℝ)
    (hL : 0 < L) (h_rate : μ ≤ L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (h_pl : ∀ x : E, 2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (θ₀ : E) (T : ℕ) :
    f ((plStep grad L)^[T] θ₀) - fstar
      ≤ (1 - μ / L) ^ T * (f θ₀ - fstar) := by
  induction T with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ T ih =>
    have hstep := pl_descent_step f grad L μ fstar
      ((plStep grad L)^[T] θ₀) hL h_smooth h_pl h_floor
    have hnn : 0 ≤ 1 - μ / L := by
      rw [sub_nonneg, div_le_one hL]
      linarith
    rw [Function.iterate_succ_apply', pow_succ]
    calc f (plStep grad L ((plStep grad L)^[T] θ₀)) - fstar
        ≤ (1 - μ / L) * (f ((plStep grad L)^[T] θ₀) - fstar) := hstep
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ T * (f θ₀ - fstar)) :=
          mul_le_mul_of_nonneg_left ih hnn
      _ = (1 - μ / L) ^ T * (1 - μ / L) * (f θ₀ - fstar) := by ring

end PL

end Hagi.Model.CEGlobalConvergence
