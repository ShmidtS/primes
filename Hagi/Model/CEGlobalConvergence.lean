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
* The smoothness premise is DISCHARGED for the linear head:
  `ce_smooth_ident` derives the descent lemma with the row-energy
  constant `ceSmoothL X = \sum v \sum j X v j ^ 2` (C354; the
  single-sample analog of the data-geometry bound
  `(1/n) \sum |phi(x_i)|^2`, unnormalized here).  The sharp
  constant `lambda_max(X^T X)` and an `L <= B^2`-style feature
  bound are not formalized.  The PL premise remains a premise: it
  holds for CE only under additional conditions (realizable logits
  with margin-type separability), not formalized in this snapshot;
  `ce_global_convergence_ident` states the corollary with
  `h_smooth` discharged and PL/floor still explicit.
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


/-! ## Part 1b: smoothness of the log-linear CE in the parameters

The descent lemma for `Hagi.lse` with constant `1`, proved by the
classical 1-D reduction (log-sum-exp Hessian `diag p − ppᵀ ⪯ I`,
cf. Boyd–Vandenberghe, Convex Optimization §9.1): for the line
`s ↦ log ∑ exp (a v + s * b v)` the second derivative is the
`softDef`-variance of `b`, hence in `[0, ∑ b v ^ 2]`; two
applications of the mean value theorem
(`exists_deriv_eq_slope`) yield `lse_descent`.  Composing with
the feature matrix `X` (Cauchy–Schwarz per row,
`Finset.sum_mul_sq_le_sq_mul_sq`) gives the descent lemma for
`θ ↦ ceOneHot t (X *ᵥ θ)` with the row-energy constant `ceSmoothL`.
-/

section Smoothness

variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- Derivative of the exponential normalizer along a line. -/
private theorem hasDerivAt_exp_sum_line (a b : V → ℝ) (s : ℝ) :
    HasDerivAt (fun s => ∑ v, Real.exp (a v + s * b v))
      (∑ v, b v * Real.exp (a v + s * b v)) s := by
  have hEach : ∀ v : V, HasDerivAt
      (fun s => Real.exp (a v + s * b v))
      (b v * Real.exp (a v + s * b v)) s := by
    intro v
    have h1 : HasDerivAt (fun s => a v + s * b v) (b v) s := by
      convert (((hasDerivAt_id s).const_mul (b v)).add_const (a v)) using 1
      · funext x; simp only [id]; ring
      · ring
    have h2 := h1.exp
    convert h2 using 1
    · ring
  convert HasDerivAt.sum (u := Finset.univ)
    (A := fun v (s : ℝ) => Real.exp (a v + s * b v))
    (A' := fun v => b v * Real.exp (a v + s * b v)) (fun v _ => hEach v) using 1
  funext x
  simp only [Finset.sum_apply]

private theorem exp_sum_line_pos (a b : V → ℝ) (s : ℝ) :
    0 < ∑ v, Real.exp (a v + s * b v) :=
  Hagi.Core.exp_sum_pos _

/-- Derivative of the line `s ↦ lse (a + s • b)`. -/
private theorem hasDerivAt_log_exp_sum_line (a b : V → ℝ) (s : ℝ) :
    HasDerivAt (fun s => Real.log (∑ v, Real.exp (a v + s * b v)))
      ((∑ v, b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v)) s :=
  (hasDerivAt_exp_sum_line a b s).log (ne_of_gt (exp_sum_line_pos a b s))

/-- Derivative of the numerator `∑ b v * exp (a v + s * b v)`. -/
private theorem hasDerivAt_bexp_sum_line (a b : V → ℝ) (s : ℝ) :
    HasDerivAt (fun s => ∑ v, b v * Real.exp (a v + s * b v))
      (∑ v, b v * (b v * Real.exp (a v + s * b v))) s := by
  have hEach : ∀ v : V, HasDerivAt
      (fun s => b v * Real.exp (a v + s * b v))
      (b v * (b v * Real.exp (a v + s * b v))) s := by
    intro v
    have h1 : HasDerivAt (fun s => a v + s * b v) (b v) s := by
      convert (((hasDerivAt_id s).const_mul (b v)).add_const (a v)) using 1
      · funext x; simp only [id]; ring
      · ring
    have h2 := (hasDerivAt_const s (b v)).mul h1.exp
    convert h2 using 1
    · ring
  convert HasDerivAt.sum (u := Finset.univ)
    (A := fun v (s : ℝ) => b v * Real.exp (a v + s * b v))
    (A' := fun v => b v * (b v * Real.exp (a v + s * b v)))
    (fun v _ => hEach v) using 1
  funext x
  simp only [Finset.sum_apply]

/-- Second derivative of the line: the `softDef`-variance form
`(N''·N − N'²)/N²`. -/
private theorem hasDerivAt_grad_log_exp_sum_line (a b : V → ℝ) (s : ℝ) :
    HasDerivAt
      (fun s => (∑ v, b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v))
      (((∑ v, b v * b v * Real.exp (a v + s * b v))
          * ∑ v, Real.exp (a v + s * b v)
        - (∑ v, b v * Real.exp (a v + s * b v))^2)
        / (∑ v, Real.exp (a v + s * b v))^2) s := by
  convert (hasDerivAt_bexp_sum_line a b s).div
    (hasDerivAt_exp_sum_line a b s) (ne_of_gt (exp_sum_line_pos a b s)) using 1
  · rw [show (∑ v, b v * (b v * Real.exp (a v + s * b v)))
        = ∑ v, b v * b v * Real.exp (a v + s * b v) from
      Finset.sum_congr rfl (fun v _ => by ring), ← pow_two]

/-- Weighted Cauchy–Schwarz: `(∑ b e)² ≤ (∑ b² e)(∑ e)`. -/
private theorem exp_line_cs (a b : V → ℝ) (s : ℝ) :
    (∑ v, b v * Real.exp (a v + s * b v))^2
      ≤ (∑ v, b v * b v * Real.exp (a v + s * b v))
        * ∑ v, Real.exp (a v + s * b v) :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun v _ => mul_nonneg (mul_self_nonneg (b v)) (Real.exp_nonneg _))
    (fun v _ => Real.exp_nonneg _)
    (fun v _ => by
      have h : (b v * Real.exp (a v + s * b v))^2
          = b v * b v * Real.exp (a v + s * b v)
            * Real.exp (a v + s * b v) := by ring
      rw [h])

/-- Every softmax coordinate is at most one (local copy of
`GatedCEUniformCurvature.softDef_le_one`, kept private to avoid a
module dependency for one line). -/
private theorem softDef_le_one (a : V → ℝ) (v : V) :
    Hagi.Prelude.softDef a v ≤ 1 := by
  have h : Hagi.Prelude.softDef a v
      = Real.exp (a v) / ∑ c, Real.exp (a c) := rfl
  rw [h]
  exact (div_le_one (Hagi.Core.exp_sum_pos a)).2
    (Finset.single_le_sum (f := fun c => Real.exp (a c))
      (fun c _ => Real.exp_nonneg _) (Finset.mem_univ v))

/-- Nonnegativity of the second derivative (variance form). -/
private theorem second_deriv_nonneg (a b : V → ℝ) (s : ℝ) :
    (0:ℝ) ≤ ((∑ v, b v * b v * Real.exp (a v + s * b v))
          * ∑ v, Real.exp (a v + s * b v)
        - (∑ v, b v * Real.exp (a v + s * b v))^2)
        / (∑ v, Real.exp (a v + s * b v))^2 := by
  refine div_nonneg ?_ (sq_nonneg _)
  nlinarith [exp_line_cs a b s]

/-- The second derivative is at most the squared norm of the
direction: variance `≤ ∑ softDef v * b v² ≤ ∑ b v²`. -/
private theorem second_deriv_le (a b : V → ℝ) (s : ℝ) :
    ((∑ v, b v * b v * Real.exp (a v + s * b v))
          * ∑ v, Real.exp (a v + s * b v)
        - (∑ v, b v * Real.exp (a v + s * b v))^2)
        / (∑ v, Real.exp (a v + s * b v))^2
      ≤ ∑ v, b v * b v := by
  have hNpos : (0:ℝ) < ∑ v, Real.exp (a v + s * b v) :=
    exp_sum_line_pos a b s
  have hNsq : (0:ℝ) < (∑ v, Real.exp (a v + s * b v))^2 := by positivity
  have hfrac : ((∑ v, b v * b v * Real.exp (a v + s * b v))
          * ∑ v, Real.exp (a v + s * b v)
        - (∑ v, b v * Real.exp (a v + s * b v))^2)
        / (∑ v, Real.exp (a v + s * b v))^2
      ≤ (∑ v, b v * b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v) := by
    rw [div_le_div_iff₀ hNsq hNpos]
    nlinarith [sq_nonneg (∑ v, b v * Real.exp (a v + s * b v))]
  have h : ∀ v : V, Real.exp (a v + s * b v)
      / ∑ c, Real.exp (a c + s * b c)
      = Hagi.Prelude.softDef (fun w => a w + s * b w) v := fun _ => rfl
  have hnn : (∑ v, b v * b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v)
      = ∑ v, Hagi.Prelude.softDef (fun w => a w + s * b w) v * (b v * b v) := by
    have hrw : ∑ v, Hagi.Prelude.softDef (fun w => a w + s * b w) v * (b v * b v)
        = ∑ v, (b v * b v * Real.exp (a v + s * b v))
          / ∑ c, Real.exp (a c + s * b c) :=
      Finset.sum_congr rfl (fun v _ => by rw [← h v]; ring)
    rw [hrw, Finset.sum_div]
  refine le_trans hfrac ?_
  rw [hnn]
  calc ∑ v, Hagi.Prelude.softDef (fun w => a w + s * b w) v * (b v * b v)
      ≤ ∑ v, 1 * (b v * b v) :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right
          (softDef_le_one (fun w => a w + s * b w) v) (mul_self_nonneg _))
    _ = ∑ v, b v * b v := by simp

/-- Mean-value bound on the line gradient: the derivative of the
line is monotone with Lipschitz constant `∑ b v²`. -/
private theorem grad_line_bounds (a b : V → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
      ≤ (∑ v, b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v)
    ∧ (∑ v, b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v)
      ≤ (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
        + s * ∑ v, b v * b v := by
  rcases eq_or_lt_of_le hs with rfl | hpos
  · constructor <;> simp
  set Gp : ℝ → ℝ := fun s => (∑ v, b v * Real.exp (a v + s * b v))
        / ∑ v, Real.exp (a v + s * b v) with hGp
  have hGp_deriv : ∀ x : ℝ, HasDerivAt Gp
      (((∑ v, b v * b v * Real.exp (a v + x * b v))
          * ∑ v, Real.exp (a v + x * b v)
        - (∑ v, b v * Real.exp (a v + x * b v))^2)
        / (∑ v, Real.exp (a v + x * b v))^2) x :=
    fun x => hasDerivAt_grad_log_exp_sum_line a b x
  have hcont : ContinuousOn Gp (Set.Icc 0 s) := fun x _ =>
    ((hGp_deriv x).continuousAt.continuousWithinAt)
  have hdiff : DifferentiableOn ℝ Gp (Set.Ioo 0 s) := fun x hx =>
    (hGp_deriv x).differentiableAt.differentiableWithinAt
  obtain ⟨η, _, hη⟩ := exists_deriv_eq_slope Gp hpos hcont hdiff
  rw [(hGp_deriv η).deriv] at hη
  have hM := second_deriv_nonneg a b η
  have hM' := second_deriv_le a b η
  have hkey : Gp s - Gp 0 = ((∑ v, b v * b v * Real.exp (a v + η * b v))
          * ∑ v, Real.exp (a v + η * b v)
        - (∑ v, b v * Real.exp (a v + η * b v))^2)
        / (∑ v, Real.exp (a v + η * b v))^2 * s := by
    rw [hη, sub_zero]
    field_simp
  have hG0 : Gp 0 = (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v) := by
    simp only [hGp]
    norm_num
  rw [← hG0]
  constructor <;> nlinarith

/-- **Descent lemma for log-sum-exp** with smoothness constant `1`
(the L2 norm written as an explicit sum):
`lse (a + b) ≤ lse a + ∑ softDef a v * b v + (∑ b v ^ 2) / 2`.
The proof is the classical line-reduction: the second derivative of
`s ↦ lse (a + s • b)` is a `softDef`-variance, bounded by `∑ b v²`;
two mean-value arguments integrate this bound. -/
theorem lse_descent (a b : V → ℝ) :
    Hagi.lse (a + b) ≤ Hagi.lse a
      + ∑ v, Hagi.Prelude.softDef a v * b v
      + (∑ v, b v * b v) / 2 := by
  set G : ℝ → ℝ := fun s => Real.log (∑ v, Real.exp (a v + s * b v)) with hG
  have hGd : ∀ x : ℝ, HasDerivAt G
      ((∑ v, b v * Real.exp (a v + x * b v))
        / ∑ v, Real.exp (a v + x * b v)) x :=
    fun x => hasDerivAt_log_exp_sum_line a b x
  set M : ℝ := ∑ v, b v * b v with hM
  set h : ℝ → ℝ := fun s => G 0 + ((∑ v, b v * Real.exp (a v))
        / ∑ v, Real.exp (a v)) * s + M / 2 * s ^ 2 - G s with hH
  have hhd : ∀ x : ℝ, HasDerivAt h
      ((∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
        + M * x - (∑ v, b v * Real.exp (a v + x * b v))
          / ∑ v, Real.exp (a v + x * b v)) x := by
    intro x
    have hGx := hGd x
    have hcomp := (((hasDerivAt_const x (G 0)).add
      ((hasDerivAt_const x ((∑ v, b v * Real.exp (a v))
        / ∑ v, Real.exp (a v))).mul (hasDerivAt_id x))).add
      ((hasDerivAt_const x (M / 2)).mul
        ((hasDerivAt_id x).pow 2))).sub hGx
    convert hcomp using 1
    · first | (funext z; simp only [id]) | rfl
    · simp only [id]; norm_num; ring
  have hcont : ContinuousOn h (Set.Icc 0 1) := fun x _ =>
    (hhd x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ h (Set.Ioo 0 1) := fun x hx =>
    (hhd x).differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope h (by norm_num) hcont hdiff
  rw [(hhd ξ).deriv] at hξd
  have hb2 : (∑ v, b v * Real.exp (a v + ξ * b v))
        / ∑ v, Real.exp (a v + ξ * b v)
      ≤ (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
        + ξ * ∑ v, b v * b v :=
    (grad_line_bounds a b (le_of_lt hξ.1)).2
  rw [← hM] at hb2
  have h1 : h 1 - h 0
      = (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
        + M * ξ - (∑ v, b v * Real.exp (a v + ξ * b v))
          / ∑ v, Real.exp (a v + ξ * b v) := by
    rw [hξd]; norm_num
  have h0 : h 0 = 0 := by
    simp only [hH]
    norm_num
  rw [h0] at h1
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun v _ => mul_self_nonneg _)
  have hξpos : 0 < ξ := hξ.1
  have hres : h 1 ≥ 0 := by nlinarith
  simp only [hH, one_pow] at hres
  have hGab : G 1 = Hagi.lse (a + b) := by
    simp only [hG]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by simp [Pi.add_apply])
  have hGa : G 0 = Hagi.lse a := by
    simp only [hG]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by simp [Pi.add_apply])
  rw [hGab, hGa] at hres
  have hsoft : (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
      = ∑ v, Hagi.Prelude.softDef a v * b v := by
    have hdef : ∀ v : V, Real.exp (a v) / ∑ c, Real.exp (a c)
        = Hagi.Prelude.softDef a v := fun _ => rfl
    have hrw : ∑ v, Hagi.Prelude.softDef a v * b v
        = ∑ v, Real.exp (a v) * b v / ∑ c, Real.exp (a c) :=
      Finset.sum_congr rfl (fun v _ => by rw [← hdef v]; ring)
    rw [hrw, Finset.sum_div]
    try exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hsoft] at hres
  linarith

end Smoothness

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


/-! ## Part 3: the smoothness premise discharged for the linear head

The descent lemma for `θ ↦ Hagi.ceOneHot t (X *ᵥ θ)` on
`EuclideanSpace ℝ (Fin d)` with the row-energy constant
`ceSmoothL X = ∑ v ∑ j X v j ^ 2` (Frobenius-type: the
single-sample analog of the data-geometry smoothness
`(1/n) ∑ ‖φ(xᵢ)‖²`, unnormalized here).  The gradient functional
matches the derivative direction of
`CEGradient.fderiv_ceOneHot_mulVec` (`Xᵀ (softmax (Xθ) − oneHot t)`).
-/

section IdentSmoothness

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}

/-- The row-energy smoothness constant of the linear head: the sum
of squared row norms of the feature matrix `X`. -/
def ceSmoothL (X : Matrix V (Fin d) ℝ) : ℝ := ∑ v, ∑ j, X v j * X v j

/-- The gradient of `θ ↦ ceOneHot t (X *ᵥ θ)` in parameter space:
`Xᵀ (softmax (Xθ) − oneHot t)`. -/
noncomputable def ceGrad (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => ∑ v, (Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
    - if v = t then 1 else 0) * X v j)

/-- Inner-product bridge: the `ceGrad` inner product is the
softmax-minus-onehot pairing with `X *ᵥ Δ` (the direction of
`CEGradient.fderiv_ceOneHot_mulVec`). -/
theorem ceGrad_inner (X : Matrix V (Fin d) ℝ) (t : V)
    (θ Δ : EuclideanSpace ℝ (Fin d)) :
    ⟪ceGrad X t θ, Δ⟫_ℝ = ∑ v, (Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
      - if v = t then 1 else 0) * (X *ᵥ Δ.ofLp) v := by
  simp only [ceGrad, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun v _ =>
    Finset.sum_congr rfl (fun j _ => by ring))

/-- Row-energy bound on the feature map: `‖X *ᵥ h‖² ≤ ceSmoothL X * ‖h‖²`
(explicit-sum form), by Cauchy–Schwarz per row. -/
theorem feature_map_sq_le (X : Matrix V (Fin d) ℝ)
    (h : EuclideanSpace ℝ (Fin d)) :
    ∑ v, (X *ᵥ h.ofLp) v * (X *ᵥ h.ofLp) v
      ≤ ceSmoothL X * ∑ j, h.ofLp j * h.ofLp j := by
  have hrow : ∀ v : V, (X *ᵥ h.ofLp) v * (X *ᵥ h.ofLp) v
      ≤ (∑ j, X v j * X v j) * ∑ j, h.ofLp j * h.ofLp j := by
    intro v
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun j => X v j) (fun j => h.ofLp j)
    have hexp : (X *ᵥ h.ofLp) v = ∑ j, X v j * h.ofLp j := by
      simp [Matrix.mulVec, dotProduct]
    rw [hexp, show (∑ j, X v j * h.ofLp j) * (∑ j, X v j * h.ofLp j)
        = (∑ j, X v j * h.ofLp j) ^ 2 from by ring]
    have h2 : (∑ j, X v j * X v j) = ∑ j, X v j ^ 2 :=
      Finset.sum_congr rfl (fun j _ => by ring)
    have h3 : ∑ j, h.ofLp j * h.ofLp j = ∑ j, h.ofLp j ^ 2 :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2, h3]
    exact hcs
  calc ∑ v, (X *ᵥ h.ofLp) v * (X *ᵥ h.ofLp) v
      ≤ ∑ v, (∑ j, X v j * X v j) * ∑ j, h.ofLp j * h.ofLp j :=
        Finset.sum_le_sum (fun v _ => hrow v)
    _ = ceSmoothL X * ∑ j, h.ofLp j * h.ofLp j := by
        rw [ceSmoothL, ← Finset.sum_mul]

/-- **The descent lemma for the linear-head CE**: the smoothness
premise of `ce_global_convergence` derived, not assumed — with the
row-energy constant `ceSmoothL X` from the data geometry of `X`. -/
theorem ce_smooth_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (θ θ' : EuclideanSpace ℝ (Fin d)) :
    Hagi.ceOneHot t (X *ᵥ θ'.ofLp)
      ≤ Hagi.ceOneHot t (X *ᵥ θ.ofLp) + ⟪ceGrad X t θ, θ' - θ⟫_ℝ
        + ceSmoothL X / 2 * ‖θ' - θ‖ ^ 2 := by
  have hsplit : ∀ w : EuclideanSpace ℝ (Fin d),
      Hagi.ceOneHot t (X *ᵥ w.ofLp)
        = Hagi.lse (X *ᵥ w.ofLp) - (X *ᵥ w.ofLp) t := fun _ => rfl
  have hadd : X *ᵥ θ'.ofLp = X *ᵥ θ.ofLp + X *ᵥ (θ' - θ).ofLp := by
    have h1 : (θ' - θ).ofLp = θ'.ofLp - θ.ofLp := by
      simp [WithLp.ofLp_sub]
    rw [h1, Matrix.mulVec_sub]
    try ring
  have hlsed := lse_descent (X *ᵥ θ.ofLp) (X *ᵥ (θ' - θ).ofLp)
  rw [← hadd] at hlsed
  -- linear part is exact
  have hlin : (X *ᵥ θ'.ofLp) t = (X *ᵥ θ.ofLp) t + (X *ᵥ (θ' - θ).ofLp) t := by
    rw [hadd, Pi.add_apply]
  -- norm bridge
  have hnorm : ‖θ' - θ‖ ^ 2 = ∑ j, (θ' - θ).ofLp j * (θ' - θ).ofLp j := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- feature-map bound
  have hfeat := feature_map_sq_le X (θ' - θ)
  -- softmax pairing minus the one-hot part equals the gradient pairing
  have hsoftpair : ∑ v, Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
        * (X *ᵥ (θ' - θ).ofLp) v - (X *ᵥ (θ' - θ).ofLp) t
      = ∑ v, (Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
          - if v = t then 1 else 0) * (X *ᵥ (θ' - θ).ofLp) v := by
    have hte : (X *ᵥ (θ' - θ).ofLp) t
        = ∑ v, (if v = t then 1 else 0) * (X *ᵥ (θ' - θ).ofLp) v := by
      simp
    rw [hte, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  -- the smoothness constant absorbs the feature-map norm
  have hsum : (∑ v, (X *ᵥ (θ' - θ).ofLp) v * (X *ᵥ (θ' - θ).ofLp) v) / 2
      ≤ ceSmoothL X / 2 * ∑ j, (θ' - θ).ofLp j * (θ' - θ).ofLp j :=
    by nlinarith [hfeat]
  -- assemble
  rw [hsplit θ', hsplit θ, hlin, ceGrad_inner X t θ (θ' - θ), hnorm]
  linarith [hlsed, hsoftpair, hsum]

/-- The row energy is positive exactly when the feature matrix is
nonzero. -/
theorem ceSmoothL_pos (X : Matrix V (Fin d) ℝ) (hne : X ≠ 0) :
    0 < ceSmoothL X := by
  by_contra hcon
  push_neg at hcon
  have hnn : 0 ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
  have hzero : (∑ v, ∑ j, X v j * X v j : ℝ) = 0 := by
    have := le_antisymm hcon hnn
    exact this
  have hz2 : ∀ v ∈ (Finset.univ : Finset V), ∑ j, X v j * X v j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _))).1 hzero
  have hall : ∀ v j, X v j = 0 := by
    intro v j
    have hv := hz2 v (Finset.mem_univ v)
    have hj2 : X v j * X v j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg _)).1 hv j (Finset.mem_univ j)
    nlinarith [mul_self_nonneg (X v j)]
  apply hne
  ext v j
  simp [hall v j]

set_option maxHeartbeats 4000000 in
/-- **Global convergence for the real log-linear CE head with the
smoothness premise discharged.**  Instantiates `ce_global_convergence`
on `E = EuclideanSpace ℝ (Fin d)` with `f θ = ceOneHot t (X *ᵥ θ)`
and gradient `ceGrad X t` (`Xᵀ (softmax (Xθ) − oneHot t)`): the
descent-lemma premise `h_smooth` is supplied by `ce_smooth_ident`
with the data-geometry constant `ceSmoothL X`.

Honest premise ledger: PL (`h_pl`), the loss floor (`h_floor`), the
optimal value `fstar` and the rate condition `h_rate : μ ≤ L`
remain explicit.  PL for one-hot CE is not automatic: it holds
under realizability/margin-type separability conditions (softmax
must be able to express the target `t`), which are a separate
formalization task.  The degenerate case `X = 0` (constant loss,
`L = 0`, step size `1/L` undefined) is excluded by `hne`. -/
theorem ce_global_convergence_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (μ fstar : ℝ) (hne : X ≠ 0) (h_rate : μ ≤ ceSmoothL X)
    (h_pl : ∀ θ : EuclideanSpace ℝ (Fin d),
      2 * μ * (Hagi.ceOneHot t (X *ᵥ θ.ofLp) - fstar)
        ≤ ‖ceGrad X t θ‖ ^ 2)
    (h_floor : ∀ θ : EuclideanSpace ℝ (Fin d),
      fstar ≤ Hagi.ceOneHot t (X *ᵥ θ.ofLp))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    Hagi.ceOneHot t (X *ᵥ ((plStep (ceGrad X t) (ceSmoothL X))^[T]
        θ₀).ofLp) - fstar
      ≤ (1 - μ / ceSmoothL X) ^ T
        * (Hagi.ceOneHot t (X *ᵥ θ₀.ofLp) - fstar) := by
  refine ce_global_convergence
    (fun θ => Hagi.ceOneHot t (X *ᵥ θ.ofLp)) (ceGrad X t)
    (ceSmoothL X) μ fstar ?_ ?_ ?_ ?_ ?_ θ₀ T <;>
    [exact ceSmoothL_pos X hne; exact h_rate;
     exact fun x y => ce_smooth_ident X t x y; exact h_pl; exact h_floor]

end IdentSmoothness

end Hagi.Model.CEGlobalConvergence
