/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Core.Concat
import Hagi.Model.SoftmaxHead
import Hagi.Model.GatedCEDescent

/-!
# Global convergence for the log-linear CE head under PL

The repo's CE descent theory (`Hagi.Model.CEDescent`, the
`BatchCEDescent*` family) gives local one-step certificates; this
module adds the global statement: minimizing one-hot cross-entropy over a log-linear
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
  constant `ceSmoothL X = \sum v \sum j X v j ^ 2` (the
  single-sample analog of the data-geometry bound
  `(1/n) \sum |phi(x_i)|^2`, unnormalized here).  The sharp
  constant `lambda_max(X^T X)` and an `L <= B^2`-style feature
  bound are not formalized.  The PL premise remains a premise: it
  holds for CE only under additional conditions (realizable logits
  with margin-type separability), not formalized in this snapshot;
  `ce_global_convergence_ident` states the corollary with
  `h_smooth` discharged and PL/floor still explicit. Part 5
  DISCHARGES PL for the ℓ2-REGULARIZED objective (`ceReg`, weight
  decay): strong convexity `λ` ⟹ PL `μ = λ` (`strong_convex_pl`),
  giving `ce_global_convergence_reg` with PL/smoothness derived;
  the unregularized margin-based route is `Hagi.Model.CEMarginPL`
(2-class gap head and multiclass, on a ball).
* Fixed step `1 / L` only; no adaptive step sizes.
* `ce_loglinear_convex` is stated on the plain parameter space
  `Fin d → ℝ`.  Transporting `ConvexOn` to the
  `EuclideanSpace ℝ (Fin d)` carrier of `Hagi.Model.CEGradient` is
  a linear-isometry transport not formalized here.
* The O(1/T) rate WITHOUT PL is formalized here for the linear head
  (`ce_rate_no_pl_ident`): convexity + the derived smoothness give the
  per-step progress `δ ← δ − δ²/(2LR²)` and a nonlinear recursion yields
  `f(θ_T) − f* ≤ 2·L·R²/(T+1)` for every `T ≥ 1` (simultaneously a
  min- and last-iterate bound; the averaged-iterate form is not
  formalized).  Its pinned premises: the loss floor `f*`, ATTAINMENT
  `f(θstar) ≤ f*` (without it the statement is false), and an R-bound
  on ALL iterates' distance to a minimizer (level-set boundedness not
  formalized).

Reference search found no
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
          (GatedCEUniformCurvature.softDef_le_one _ v) (mul_self_nonneg _))
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

set_option maxHeartbeats 400000 in
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
    (E := EuclideanSpace ℝ (Fin d))
    (fun θ => Hagi.ceOneHot t (X *ᵥ θ.ofLp)) (ceGrad X t)
    (ceSmoothL X) μ fstar ?_ ?_ ?_ ?_ ?_ θ₀ T <;>
    [exact ceSmoothL_pos X hne; exact h_rate;
     exact fun x y => ce_smooth_ident X t x y; exact h_pl; exact h_floor]

end IdentSmoothness

/-! ## Part 4: the PL-free O(1/T) sublinear rate

Classical convex + L-smooth gradient descent (step `1/L`), NO
Polyak-Łojasiewicz premise.  Route (cf. Bubeck, *Convex Optimization:
Algorithms and Complexity*, Thm 3.3; Nesterov, *Introductory Lectures*,
§1.2.3): the descent lemma gives `f(x⁺) ≤ f(x) − ‖∇f(x)‖²/(2L)`; first
order convexity plus Cauchy-Schwarz gives the suboptimality gap
`δ ≤ ⟨∇f(x), x − θstar⟩ ≤ ‖∇f(x)‖·R`; hence the nonlinear recursion
`δ_{t+1} ≤ δ_t − δ_t²/(2LR²)`, closed by a division-free nonlinear
telescope (`nonlin_rec_bound`) to `δ_T ≤ 2LR²/(T+1)` for every `T ≥ 1`.

Honesty ledger: the bound holds for EVERY iterate index `t ≥ 1`, so it
is simultaneously the min-iterate and the last-iterate form; the
classical AVERAGED-iterate rate `f(θ̄_T) − f* ≤ LR²/T` (Jensen over the
iterate average) is NOT formalized here.  `h_attains : f θstar ≤ fstar`
is required: `fstar` is otherwise only a floor, and with all iterates
pinned at `θstar` the gap would be an arbitrary constant (the statement
fails).  The R-bound on all iterates (a level-set boundedness
consequence for CE) remains a premise.
-/

section TangentLower

variable {V : Type} [Fintype V] [Nonempty V]

/-- First-order (tangent) lower bound for the log-sum-exp: the linear
underestimator at `a` evaluated at the direction `b`.  Mean value
theorem on the line `s ↦ lse (a + s • b)`: `G 1 − G 0 = G'(η)` for
some `η ∈ (0,1)`, and the monotonicity of the line gradient
(`grad_line_bounds`) gives `G'(0) ≤ G'(η)`.  The first-order form of
`ce_loglinear_convex`'s convexity. -/
theorem lse_tangent_lower (a b : V → ℝ) :
    Hagi.lse a + ∑ v, Hagi.Prelude.softDef a v * b v
      ≤ Hagi.lse (a + b) := by
  set G : ℝ → ℝ := fun s => Real.log (∑ v, Real.exp (a v + s * b v)) with hG
  have hGd : ∀ x : ℝ, HasDerivAt G
      ((∑ v, b v * Real.exp (a v + x * b v))
        / ∑ v, Real.exp (a v + x * b v)) x :=
    fun x => (hasDerivAt_exp_sum_line a b x).log
      (ne_of_gt (exp_sum_line_pos a b x))
  have hcont : ContinuousOn G (Set.Icc 0 1) := fun x _ =>
    (hGd x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (Set.Ioo 0 1) := fun x hx =>
    (hGd x).differentiableAt.differentiableWithinAt
  obtain ⟨η, hη, hηd⟩ := exists_deriv_eq_slope G (by norm_num) hcont hdiff
  rw [(hGd η).deriv] at hηd
  have hmono := grad_line_bounds a b (le_of_lt hη.1)
  have hG1 : G 1 = Hagi.lse (a + b) := by
    simp only [hG]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by simp [Pi.add_apply])
  have hG0 : G 0 = Hagi.lse a := by
    simp only [hG]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by simp [Pi.add_apply])
  have hsoft : (∑ v, b v * Real.exp (a v)) / ∑ v, Real.exp (a v)
      = ∑ v, Hagi.Prelude.softDef a v * b v := by
    have hdef : ∀ v : V, Real.exp (a v) / ∑ c, Real.exp (a c)
        = Hagi.Prelude.softDef a v := fun _ => rfl
    have hrw : ∑ v, Hagi.Prelude.softDef a v * b v
        = ∑ v, Real.exp (a v) * b v / ∑ c, Real.exp (a c) :=
      Finset.sum_congr rfl (fun v _ => by rw [← hdef v]; ring)
    rw [hrw, Finset.sum_div]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hslope : G 1 - G 0
      = (∑ v, b v * Real.exp (a v + η * b v))
        / ∑ v, Real.exp (a v + η * b v) := by
    rw [hηd]
    field_simp
    ring
  linarith [hG1, hG0, hslope, hmono, hsoft]

end TangentLower

section NoPL

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One-step progress under convexity + smoothness (NO PL): a single
`plStep` (step size `1/L`) decreases the loss gap by at least the
square of the gap over `2LR²`.  The descent half is the
`pl_descent_step` computation; the convexity half is the first-order
inequality at the minimizer `θstar` plus Cauchy-Schwarz.  The premise
`h_attains : f θstar ≤ fstar` is REQUIRED (with `h_floor` it pins
`fstar = f θstar`); the `R = 0` reading of the division is the trivial
`δ' ≤ δ` (Lean's `x / 0 = 0`). -/
theorem gd_progress_convex (f : E → ℝ) (grad : E → E) (L fstar R : ℝ)
    (θstar θ : E) (hL : 0 < L) (hR : 0 ≤ R)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (h_convex : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ ≤ f y)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (h_attains : f θstar ≤ fstar)
    (h_dist : ‖θ - θstar‖ ≤ R) :
    f (plStep grad L θ) - fstar
      ≤ (f θ - fstar)
        - (f θ - fstar) ^ 2 / (2 * L * R ^ 2) := by
  -- descent half (the pl_descent_step computation)
  have hstep := h_smooth θ (plStep grad L θ)
  rw [plStep] at hstep
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
  -- convexity half
  have hcvx := h_convex θ θstar
  have hinner : ⟪grad θ, θstar - θ⟫_ℝ = -⟪grad θ, θ - θstar⟫_ℝ := by
    rw [show θstar - θ = -(θ - θstar) from (neg_sub θ θstar).symm,
      inner_neg_right]
  rw [hinner] at hcvx
  have hcs : ⟪grad θ, θ - θstar⟫_ℝ ≤ ‖grad θ‖ * ‖θ - θstar‖ :=
    real_inner_le_norm _ _
  have hdelta : f θ - fstar ≤ ‖grad θ‖ * R := by
    have h1 : f θ - fstar ≤ ⟪grad θ, θ - θstar⟫_ℝ := by
      have h2 := sub_le_sub_right hcvx (f θ)
      linarith [h2, h_attains]
    have h2 : ‖grad θ‖ * ‖θ - θstar‖ ≤ ‖grad θ‖ * R :=
      mul_le_mul_of_nonneg_left h_dist (norm_nonneg _)
    exact le_trans h1 (le_trans hcs h2)
  set δ : ℝ := f θ - fstar with hδ
  have hδnn : 0 ≤ δ := sub_nonneg.2 (h_floor θ)
  have hgnn : (0:ℝ) ≤ ‖grad θ‖ := norm_nonneg _
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · -- R = 0: δ ≤ 0, the division degenerates to 0
    have h0 : δ ≤ 0 := by
      have hm0 : ‖grad θ‖ * 0 = 0 := mul_zero _
      linarith [hdelta, hm0]
    have hzero2 : (2 * L * (0:ℝ) ^ 2) = 0 := by ring
    have hgnn2 : (0:ℝ) ≤ ‖grad θ‖ ^ 2 / (2 * L) :=
      div_nonneg (sq_nonneg _) (by positivity)
    rw [hzero2, div_zero]
    rw [plStep]
    linarith [hstep, h0, hgnn2]
  · have hkey : δ ^ 2 ≤ ‖grad θ‖ ^ 2 * R ^ 2 := by
      nlinarith [hdelta, sq_nonneg δ, sq_nonneg ‖grad θ‖,
        mul_nonneg hgnn hR]
    have h2 : δ ^ 2 / (2 * L * R ^ 2) ≤ ‖grad θ‖ ^ 2 / (2 * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]
    rw [plStep]
    linarith [hstep, h2, hδ]

/-- Nonlinear telescope (division-free form): from the recursion
`a (n+1) ≤ a n − c·(a n)²` with `a ≥ 0` and `c > 0` conclude
`c·(m+2)·a (m+1) ≤ 1`, i.e. `a (m+1) ≤ 1/(c·(m+2))`.  Base by AM-GM
(`x − c·x² ≤ 1/(4c)`); step by the monotonicity of `x ↦ x·(1−c·x)` on
`[0, 1/(2c)]` (case split on `(m+3)·c·a (m+1) ≥ 1`). -/
theorem nonlin_rec_bound {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hnn : ∀ n, 0 ≤ a n)
    (hrec : ∀ n, a (n + 1) ≤ a n - c * (a n) ^ 2) (m : ℕ) :
    c * ((m:ℝ) + 2) * a (m + 1) ≤ 1 := by
  induction m with
  | zero =>
    have h2 := hrec 0
    have hsq : (1 - 2 * c * (a 0)) ^ 2 ≥ 0 := sq_nonneg _
    have hA : (0:ℝ) ≤ a 0 - c * (a 0) ^ 2 := by nlinarith [h2, hnn 1]
    have hA1 : c * a 1 ≤ c * (a 0 - c * (a 0) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hc.le
    have hA2 : 2 * c * (a 0 - c * (a 0) ^ 2) ≤ 1 := by nlinarith [hsq]
    have hA3 : 2 * (c * (a 0 - c * (a 0) ^ 2))
        ≤ 2 * c * (a 0 - c * (a 0) ^ 2) := by nlinarith [hA]
    have hA4 : 2 * c * a 1 ≤ 2 * c * (a 0 - c * (a 0) ^ 2) := by
      nlinarith [hA1]
    have hfin : 2 * c * a 1 ≤ 1 := by nlinarith [hA2, hA3, hA4]
    have hgoal : c * 2 * a (0 + 1) ≤ 1 := by
      have e : c * 2 * a (0 + 1) = 2 * c * a 1 := by ring
      rw [e]
      exact hfin
    simpa using hgoal
  | succ m ih =>
    have hcz : (0:ℝ) ≤ c * a (m + 1) := mul_nonneg hc.le (hnn (m + 1))
    have hrecn := hrec (m + 1)
    have hw : c * a (m + 1 + 1) ≤ c * (a (m + 1) - c * (a (m + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left hrecn hc.le
    have key : c * (((m:ℝ) + 1) + 2) * a (m + 1 + 1)
        ≤ (((m:ℝ) + 1) + 2) * (c * a (m + 1))
          - (((m:ℝ) + 1) + 2) * (c * a (m + 1)) * (c * a (m + 1)) := by
      have m1 : (((m:ℝ) + 1 + 2)) * (c * a (m + 1 + 1))
          ≤ (((m:ℝ) + 1 + 2)) * (c * (a (m + 1) - c * a (m + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      have e : (((m:ℝ) + 1 + 2)) * (c * (a (m + 1) - c * a (m + 1) ^ 2))
          = (((m:ℝ) + 1 + 2)) * (c * a (m + 1))
            - (((m:ℝ) + 1 + 2)) * (c * a (m + 1)) * (c * a (m + 1)) := by
        ring
      have e2 : c * (((m:ℝ) + 1 + 2) * a (m + 1 + 1))
          = (((m:ℝ) + 1 + 2)) * (c * a (m + 1 + 1)) := by ring
      nlinarith [m1, e, e2]
    have hIH : (((m:ℝ) + 1) + 1) * (c * a (m + 1)) ≤ 1 := by
      have e : (((m:ℝ) + 1) + 1) * (c * a (m + 1))
          = c * ((m:ℝ) + 2) * a (m + 1) := by ring
      rw [e]
      exact ih
    rcases lt_or_ge 1 ((((m:ℝ) + 1) + 2) * (c * a (m + 1))) with hA' | hB
    · -- 1 < u: the u·(c·a) product dominates the c·a term
      have hA : (1:ℝ) ≤ (((m:ℝ) + 1 + 2)) * (c * a (m + 1)) :=
        le_of_lt hA'
      have step : (((m:ℝ) + 1 + 2)) * (c * a (m + 1))
          - (((m:ℝ) + 1 + 2)) * (c * a (m + 1)) * (c * a (m + 1)) ≤ 1 := by
        have e3 : (((m:ℝ) + 1 + 2)) * (c * a (m + 1)) - (c * a (m + 1))
            = (((m:ℝ) + 1) + 1) * (c * a (m + 1)) := by ring
        nlinarith [hA, hIH, hcz, e3]
      show c * (((m + 1 : ℕ) : ℝ) + 2) * a (m + 1 + 1) ≤ 1
      rw [show ((m + 1 : ℕ) : ℝ) = (m:ℝ) + 1 from by norm_num]
      linarith [key, step]
    · -- u ≤ 1: the product term is nonnegative
      have step : (((m:ℝ) + 1 + 2)) * (c * a (m + 1))
          - (((m:ℝ) + 1 + 2)) * (c * a (m + 1)) * (c * a (m + 1)) ≤ 1 := by
        nlinarith [hB, hcz]
      show c * (((m + 1 : ℕ) : ℝ) + 2) * a (m + 1 + 1) ≤ 1
      rw [show ((m + 1 : ℕ) : ℝ) = (m:ℝ) + 1 from by norm_num]
      linarith [key, step]

/-- **Sublinear O(1/T) rate WITHOUT PL**: for convex + L-smooth `f`,
gradient descent with step `1/L` satisfies
`f (θ_T) − fstar ≤ 2·L·R²/(T+1)` for every `T ≥ 1`, where `R` bounds
the distance of EVERY iterate (including `θ₀`) to a minimizer
`θstar` attaining `fstar` (`h_attains`).  No PL, no strong
convexity.  The bound holds for every iterate index, so it is both the
min-iterate and the last-iterate form; the averaged-iterate form is
not formalized. -/
theorem ce_rate_no_pl (f : E → ℝ) (grad : E → E) (L fstar R : ℝ)
    (hL : 0 < L) (hR : 0 ≤ R)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (h_convex : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ ≤ f y)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (θstar θ₀ : E) (h_attains : f θstar ≤ fstar)
    (h_dist : ∀ t : ℕ,
      ‖(plStep grad L)^[t] θ₀ - θstar‖ ≤ R)
    (T : ℕ) (hT : 0 < T) :
    f ((plStep grad L)^[T] θ₀) - fstar
      ≤ 2 * L * R ^ 2 / (T + 1) := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · -- R = 0: convexity + attainment force zero gap at every iterate
    have hzero : ∀ t : ℕ,
        f ((plStep grad L)^[t] θ₀) - fstar ≤ 0 := by
      intro t
      have hcvx := h_convex ((plStep grad L)^[t] θ₀) θstar
      have hd0 : ‖(plStep grad L)^[t] θ₀ - θstar‖ ≤ 0 := h_dist t
      have hinner : ⟪grad ((plStep grad L)^[t] θ₀),
          θstar - (plStep grad L)^[t] θ₀⟫_ℝ = 0 := by
        have hnorm0 : (plStep grad L)^[t] θ₀ - θstar = 0 :=
          norm_le_zero_iff.mp hd0
        have hsub : θstar - (plStep grad L)^[t] θ₀
            = -((plStep grad L)^[t] θ₀ - θstar) := (neg_sub _ _).symm
        rw [hsub, inner_neg_right, hnorm0, inner_zero_right, neg_zero]
      rw [hinner] at hcvx
      linarith
    have hrw : 2 * L * (0:ℝ) ^ 2 / (T + 1) = 0 := by
      rw [div_eq_zero_iff]
      exact Or.inl (by ring)
    rw [hrw]
    exact hzero T
  · -- R > 0: nonlinear recursion with c = 1/(2LR²)
    set c : ℝ := 1 / (2 * L * R ^ 2) with hc
    have hcpos : 0 < c := by
      rw [hc]
      exact div_pos (by positivity) (by positivity)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hT)
    have hprog : ∀ n : ℕ,
        f ((plStep grad L)^[n + 1] θ₀) - fstar
        ≤ (f ((plStep grad L)^[n] θ₀) - fstar)
          - (f ((plStep grad L)^[n] θ₀) - fstar) ^ 2 / (2 * L * R ^ 2) := by
      intro n
      have h := gd_progress_convex f grad L fstar R θstar
        ((plStep grad L)^[n] θ₀) hL hR
        h_smooth h_convex h_floor h_attains (h_dist n)
      rwa [Function.iterate_succ_apply']
    have hnn : ∀ n, 0 ≤ f ((plStep grad L)^[n] θ₀) - fstar :=
      fun n => sub_nonneg.2 (h_floor _)
    have hrec : ∀ n, (fun t => f ((plStep grad L)^[t] θ₀) - fstar) (n + 1)
        ≤ (fun t => f ((plStep grad L)^[t] θ₀) - fstar) n
        - c * (fun t => f ((plStep grad L)^[t] θ₀) - fstar) n ^ 2 := by
      intro n
      have hconv : ∀ z : ℝ, c * z = z / (2 * L * R ^ 2) := by
        intro z; rw [hc]; field_simp
      have hp := hprog n
      show f ((plStep grad L)^[n + 1] θ₀) - fstar ≤ _ - c * _
      rw [hconv _]
      exact hp
    have hbound := nonlin_rec_bound hcpos hnn hrec m
    have hpos : (0:ℝ) < c * ((m:ℝ) + 2) :=
      mul_pos hcpos (by positivity)
    have hfinal : f ((plStep grad L)^[m + 1] θ₀) - fstar
        ≤ 1 / (c * ((m:ℝ) + 2)) := by
      rw [le_div_iff₀ hpos]
      have he : (f ((plStep grad L)^[m + 1] θ₀) - fstar) * (c * ((m:ℝ) + 2))
          = c * ((m:ℝ) + 2)
            * (f ((plStep grad L)^[m + 1] θ₀) - fstar) := by ring
      rw [he]
      exact hbound
    have hrw : 1 / (c * ((m:ℝ) + 2)) = 2 * L * R ^ 2 / ((m:ℝ) + 1 + 1) := by
      have h1 : c * ((m:ℝ) + 2) = ((m:ℝ) + 2) / (2 * L * R ^ 2) := by
        rw [hc]; field_simp
      rw [h1, one_div_div]
      congr 1
      ring
    rw [hrw] at hfinal
    rw [show ((m + 1 : ℕ) : ℝ) + 1 = (m:ℝ) + 1 + 1 from by norm_num]
    exact hfinal

end NoPL

/-! ## Part 4b: the PL-free rate instantiated on the linear head -/

section IdentNoPL

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}

/-- First-order convexity of the ident-head CE, DISCHARGED (not a
premise): the tangent underestimator at `θ` evaluated at `θ'`.
`lse_tangent_lower` plus the exact linear `- (X·) t` part; the
gradient pairing via `ceGrad_inner`.  The first-order form of
`ce_loglinear_convex`, on the `EuclideanSpace` carrier. -/
theorem ce_convex_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (θ θ' : EuclideanSpace ℝ (Fin d)) :
    Hagi.ceOneHot t (X *ᵥ θ.ofLp)
      + ⟪ceGrad X t θ, θ' - θ⟫_ℝ
      ≤ Hagi.ceOneHot t (X *ᵥ θ'.ofLp) := by
  have hsplit : ∀ w : EuclideanSpace ℝ (Fin d),
      Hagi.ceOneHot t (X *ᵥ w.ofLp)
        = Hagi.lse (X *ᵥ w.ofLp) - (X *ᵥ w.ofLp) t := fun _ => rfl
  have hadd : X *ᵥ θ'.ofLp = X *ᵥ θ.ofLp + X *ᵥ (θ' - θ).ofLp := by
    have h1 : (θ' - θ).ofLp = θ'.ofLp - θ.ofLp := by
      simp [WithLp.ofLp_sub]
    rw [h1, Matrix.mulVec_sub]
    try ring
  have hlow := lse_tangent_lower (X *ᵥ θ.ofLp) (X *ᵥ (θ' - θ).ofLp)
  rw [← hadd] at hlow
  have hlin : (X *ᵥ θ'.ofLp) t
      = (X *ᵥ θ.ofLp) t + (X *ᵥ (θ' - θ).ofLp) t := by
    rw [hadd, Pi.add_apply]
  have hsoftpair : ∑ v, Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
        * (X *ᵥ (θ' - θ).ofLp) v - (X *ᵥ (θ' - θ).ofLp) t
      = ∑ v, (Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
          - if v = t then 1 else 0) * (X *ᵥ (θ' - θ).ofLp) v := by
    have hte : (X *ᵥ (θ' - θ).ofLp) t
        = ∑ v, (if v = t then 1 else 0) * (X *ᵥ (θ' - θ).ofLp) v := by
      simp
    rw [hte, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hinner := ceGrad_inner X t θ (θ' - θ)
  rw [hsplit θ', hsplit θ, hlin]
  linarith [hlow, hsoftpair, hinner]

set_option maxHeartbeats 400000 in
/-- **PL-free sublinear rate for the real log-linear CE head.**  No PL
premise: convexity is supplied by `ce_convex_ident` (derived) and
smoothness by `ce_smooth_ident` (`L = ceSmoothL X`), giving
`f (θ_T) − fstar ≤ 2·ceSmoothL X·R²/(T+1)` for every `T ≥ 1`.

Honest premise ledger: the loss floor (`h_floor`), attainment
(`h_attains` : `f θstar ≤ fstar`), and the R-bound over all iterates
(`h_dist`) remain explicit.  Level-set boundedness of the CE (which
would discharge `R`/`h_dist` for a suitable sublevel set) and
existence of a minimizer are separate formalization tasks.  `X ≠ 0`
excludes the degenerate constant-loss case (`L = 0`). -/
theorem ce_rate_no_pl_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (fstar R : ℝ) (hne : X ≠ 0) (hR : 0 ≤ R)
    (h_floor : ∀ θ : EuclideanSpace ℝ (Fin d),
      fstar ≤ Hagi.ceOneHot t (X *ᵥ θ.ofLp))
    (θstar θ₀ : EuclideanSpace ℝ (Fin d))
    (h_attains : Hagi.ceOneHot t (X *ᵥ θstar.ofLp) ≤ fstar)
    (h_dist : ∀ n : ℕ,
      ‖((plStep (ceGrad X t) (ceSmoothL X))^[n] θ₀) - θstar‖ ≤ R)
    (T : ℕ) (hT : 0 < T) :
    Hagi.ceOneHot t (X *ᵥ ((plStep (ceGrad X t) (ceSmoothL X))^[T]
      θ₀).ofLp) - fstar
      ≤ 2 * ceSmoothL X * R ^ 2 / (T + 1) := by
  have main := ce_rate_no_pl
    (E := EuclideanSpace ℝ (Fin d))
    (fun θ => Hagi.ceOneHot t (X *ᵥ θ.ofLp))
    (ceGrad X t) (ceSmoothL X) fstar R
    (ceSmoothL_pos X hne) hR
    (fun x y => ce_smooth_ident X t x y)
    (fun x y => ce_convex_ident X t x y) h_floor θstar θ₀ h_attains
    h_dist T hT
  exact main

end IdentNoPL

/-! ## Part 5: PL discharged via regularization

The PL premise of `ce_global_convergence_ident` (Part 3) is NOT
derivable for the unregularized CE: even with realizable data the
loss is not strongly convex and PL in gradient-norm form fails in
general.  The honest tractable route is `ℓ2`-REGULARIZATION: the
regularized objective `ceReg = ceOneHot t (Xθ) + (λ/2)‖θ‖²` is
λ-strongly convex (the convex CE tangent of `ce_convex_ident` plus
the quadratic identity), and first-order strong convexity PLUS
attainment of `fstar` yields the PL inequality with `μ = λ` by
completing the square — this is `strong_convex_pl`.  No smoothness
is needed for the PL derivation itself; the descent lemma for
`ceReg` with `L = ceSmoothL X + λ` (`ceReg_smooth_ident`) is the
CE bound plus the exact quadratic shift.  The corollary
`ce_global_convergence_reg` instantiates the rate machine for
the REAL regularized model: geometric factor
`1 − λ/(ceSmoothL X + λ)` with only `λ > 0`, the floor `fstar`, and
attainment (`h_att`, the pattern) explicit — PL and smoothness
are fully discharged. -/

section StrongConvexPL

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Norm-square additivity identity: `‖x+y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`
on a real inner product space. -/
private theorem norm_add_sq' (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ^ 2 = ⟪x + y, x + y⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
  rw [h1, inner_add_left, inner_add_right, inner_add_right,
    real_inner_comm y x, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

/-- **Strong convexity implies PL** (gradient-norm form, `μ = λ`):
from the first-order strong-convexity inequality and ATTAINMENT of
`fstar` at `θstar`, the PL inequality `2λ(f x − fstar) ≤ ‖grad x‖²`
follows by completing the square in the direction `θstar − x`.
No smoothness is used.  Attainment is REQUIRED: with `fstar` merely
a floor the statement is false (`fstar` could lie far below `f`). -/
theorem strong_convex_pl (f : E → ℝ) (grad : E → E) (lam fstar : ℝ)
    (hlam : 0 < lam)
    (h_sconvex : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ
      + lam / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (θstar : E) (h_att : f θstar ≤ fstar) (x : E) :
    2 * lam * (f x - fstar) ≤ ‖grad x‖ ^ 2 := by
  have hstep := h_sconvex x θstar
  -- square completion: -‖g‖² ≤ 2λ(⟪g, d⟫ + λ/2‖d‖²)
  have hsc : -(‖grad x‖ ^ 2)
      ≤ 2 * lam * (⟪grad x, θstar - x⟫_ℝ + lam / 2 * ‖θstar - x‖ ^ 2) := by
    have hexp := norm_add_sq' (θstar - x) ((1 / lam) • grad x)
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_pow] at hexp
    have hnn : (0:ℝ) ≤ ‖(θstar - x) + (1 / lam) • grad x‖ ^ 2 :=
      sq_nonneg _
    have heq : lam * lam * (‖(θstar - x) + (1 / lam) • grad x‖ ^ 2)
        = ‖grad x‖ ^ 2 + 2 * lam * ⟪θstar - x, grad x⟫_ℝ
          + lam * lam * ‖θstar - x‖ ^ 2 := by
      rw [hexp]
      field_simp
      ring
    rw [real_inner_comm (θstar - x) (grad x)]
    nlinarith [hnn, heq]
  nlinarith [hstep, hsc, h_att, hlam]

end StrongConvexPL

section IdentReg

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact quadratic shift: `λ/2‖x‖² + λ⟪x,δ⟫ + λ/2‖δ‖² = λ/2‖x+δ‖²`
(an identity; used for BOTH the strong-convexity lower bound and
the smoothness upper bound of the regularizer). -/
private theorem quad_shift (lam : ℝ) (x δ : E) :
    lam / 2 * ‖x‖ ^ 2 + lam * ⟪x, δ⟫_ℝ + lam / 2 * ‖δ‖ ^ 2
      = lam / 2 * ‖x + δ‖ ^ 2 := by
  have h := norm_add_sq' x δ
  rw [h]
  ring

/-- The ℓ2-regularized log-linear CE objective:
`ceOneHot t (X *ᵥ θ) + (λ/2)‖θ‖²` (weight decay). -/
noncomputable def ceReg {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Hagi.ceOneHot t (X *ᵥ θ.ofLp) + lam / 2 * ‖θ‖ ^ 2

/-- The gradient of the regularized objective:
`ceGrad X t θ + λ • θ`. -/
noncomputable def ceGradReg {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ceGrad X t θ + lam • θ

/-- First-order strong convexity of the regularized objective:
`ceReg` is λ-strongly convex in the first-order sense (the convex
CE tangent `ce_convex_ident` plus the exact quadratic shift). -/
theorem ceReg_strong_convex_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (lam : ℝ) (θ θ' : EuclideanSpace ℝ (Fin d)) :
    ceReg X t lam θ + ⟪ceGradReg X t lam θ, θ' - θ⟫_ℝ
      + lam / 2 * ‖θ' - θ‖ ^ 2
      ≤ ceReg X t lam θ' := by
  have hcvx := ce_convex_ident X t θ θ'
  have hq : lam / 2 * ‖θ‖ ^ 2 + lam * ⟪θ, θ' - θ⟫_ℝ
      + lam / 2 * ‖θ' - θ‖ ^ 2 = lam / 2 * ‖θ'‖ ^ 2 := by
    have h := quad_shift lam θ (θ' - θ)
    rwa [show θ + (θ' - θ) = θ' by abel] at h
  have hin : ⟪ceGradReg X t lam θ, θ' - θ⟫_ℝ
      = ⟪ceGrad X t θ, θ' - θ⟫_ℝ + lam * ⟪θ, θ' - θ⟫_ℝ := by
    rw [ceGradReg, inner_add_left, real_inner_smul_left]
  simp only [ceReg, hin]
  linarith [hcvx, hq]

/-- **Descent lemma for the regularized objective** with the
constant `ceSmoothL X + λ`: the CE bound plus the exact
quadratic shift. -/
theorem ceReg_smooth_ident (X : Matrix V (Fin d) ℝ) (t : V)
    (lam : ℝ) (θ θ' : EuclideanSpace ℝ (Fin d)) :
    ceReg X t lam θ' ≤ ceReg X t lam θ + ⟪ceGradReg X t lam θ, θ' - θ⟫_ℝ
      + (ceSmoothL X + lam) / 2 * ‖θ' - θ‖ ^ 2 := by
  have hsm := ce_smooth_ident X t θ θ'
  have hq : lam / 2 * ‖θ'‖ ^ 2
      = lam / 2 * ‖θ‖ ^ 2 + lam * ⟪θ, θ' - θ⟫_ℝ
      + lam / 2 * ‖θ' - θ‖ ^ 2 := by
    have h := quad_shift lam θ (θ' - θ)
    rwa [show θ + (θ' - θ) = θ' by abel, eq_comm] at h
  have hin : ⟪ceGradReg X t lam θ, θ' - θ⟫_ℝ
      = ⟪ceGrad X t θ, θ' - θ⟫_ℝ + lam * ⟪θ, θ' - θ⟫_ℝ := by
    rw [ceGradReg, inner_add_left, real_inner_smul_left]
  have hcoef : (ceSmoothL X + lam) / 2 * ‖θ' - θ‖ ^ 2
      = ceSmoothL X / 2 * ‖θ' - θ‖ ^ 2 + lam / 2 * ‖θ' - θ‖ ^ 2 := by
    ring
  simp only [ceReg, hin, hcoef]
  linarith [hsm, hq]

/-- **Global geometric convergence for the REAL ℓ2-regularized
log-linear CE head — PL fully discharged.**  Instantiates
rate machine `ce_global_convergence` with `f = ceReg`, gradient
`ceGradReg`, `L = ceSmoothL X + λ` and `μ = λ`: the smoothness and
PL premises are DERIVED (`ceReg_smooth_ident`, `ceReg_strong_convex_ident`
+ `strong_convex_pl`), not assumed.

Honest premise ledger: `hlam : 0 < λ` (the regularization strength;
the PL constant is exactly `λ`, contributed by the regularizer
alone), the loss floor `h_floor`, and ATTAINMENT `h_att : ceReg θstar
≤ fstar` (with `h_floor` it pins `fstar = ceReg θstar`) remain
explicit; the minimizer is supplied by `ceReg_attains` below.  Unlike
Part 3, `X = 0`
is allowed (`L = λ > 0`). -/
theorem ce_global_convergence_reg (X : Matrix V (Fin d) ℝ) (t : V)
    (lam fstar : ℝ) (hlam : 0 < lam)
    (h_floor : ∀ θ : EuclideanSpace ℝ (Fin d), fstar ≤ ceReg X t lam θ)
    (θstar θ₀ : EuclideanSpace ℝ (Fin d))
    (h_att : ceReg X t lam θstar ≤ fstar) (T : ℕ) :
    ceReg X t lam
        ((plStep (ceGradReg X t lam) (ceSmoothL X + lam))^[T] θ₀) - fstar
      ≤ (1 - lam / (ceSmoothL X + lam)) ^ T
        * (ceReg X t lam θ₀ - fstar) := by
  have hLnn : (0:ℝ) ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
  have hLpos : (0:ℝ) < ceSmoothL X + lam := by nlinarith
  exact ce_global_convergence (ceReg X t lam) (ceGradReg X t lam)
    (ceSmoothL X + lam) lam fstar hLpos (by nlinarith)
    (fun x y => ceReg_smooth_ident X t lam x y)
    (fun x => strong_convex_pl (ceReg X t lam) (ceGradReg X t lam)
      lam fstar hlam (fun a b => ceReg_strong_convex_ident X t lam a b)
      θstar h_att x)
    h_floor θ₀ T

/-! ### Attainment: the last analytic premise discharged

The ℓ2-regularized objective is COERCIVE (`ceReg_coerce`: CE ≥ 0, so
`ceReg ≥ (λ/2)‖θ‖²`) and continuous (`ceReg_continuous`), hence on
the finite-dimensional parameter space it attains its minimum
(`ceReg_attains`).  This discharges the attainment premise of
`ce_global_convergence_reg` and yields the fully closed endgame
`ce_global_convergence_reg_closed` whose only analytic premise is
`0 < λ`.

Pinned (honest negative): the UNREGULARIZED head
(`ce_rate_no_pl`) keeps `h_attains` as a premise by mathematical
necessity — bare CE is not coercive (e.g. `X = 0` gives a constant
objective); the margin/realizability route stays open. -/

/-- Continuity of log-sum-exp: `lse z = log (∑ v, exp (z v))`, the
sum being strictly positive since `V` is nonempty and each `exp`
is positive. -/
private theorem continuous_lse : Continuous (Hagi.Core.lse : (V → ℝ) → ℝ) := by
  have hsum : Continuous (fun z : V → ℝ => ∑ v, Real.exp (z v)) := by
    apply continuous_finsetSum
    intro v _
    exact Real.continuous_exp.comp (continuous_apply v)
  refine hsum.log fun z => ne_of_gt ?_
  exact Finset.sum_pos (fun v _ => Real.exp_pos (z v)) Finset.univ_nonempty

/-- One-hot cross-entropy is continuous in the logits: `lse` minus a
coordinate functional. -/
private theorem continuous_ceOneHot (t : V) :
    Continuous (Hagi.ceOneHot t : (V → ℝ) → ℝ) :=
  continuous_lse.sub (continuous_apply t)

/-- The linear feature map `θ ↦ X *ᵥ θ.ofLp` is continuous: each
output coordinate is a finite sum of scaled parameter coordinates
(`PiLp.continuous_apply`). -/
private theorem continuous_mulVec_ofLp (X : Matrix V (Fin d) ℝ) :
    Continuous (fun w : EuclideanSpace ℝ (Fin d) => X *ᵥ w.ofLp) := by
  have hsum : ∀ v : V,
      Continuous (fun w : EuclideanSpace ℝ (Fin d) => ∑ j, X v j * w.ofLp j) := by
    intro v
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j)
  refine continuous_pi fun v => (hsum v).congr fun w => ?_
  simp only [Matrix.mulVec, dotProduct]

/-- The ℓ2-regularized objective is continuous (CE through the linear
feature map, plus the continuous quadratic penalty). -/
theorem ceReg_continuous (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ) :
    Continuous (fun w : EuclideanSpace ℝ (Fin d) => ceReg X t lam w) := by
  have hquad : Continuous
      (fun w : EuclideanSpace ℝ (Fin d) => lam / 2 * ‖w‖ ^ 2) := by
    fun_prop
  unfold ceReg
  exact ((continuous_ceOneHot t).comp (continuous_mulVec_ofLp X)).add hquad

/-- **Coercivity bound** for the regularized objective: since one-hot
CE is nonnegative (`Hagi.Model.CEHeldout.ceOneHot_nonneg`), the
regularizer alone gives `ceReg ≥ (λ/2)‖θ‖²`; for `λ > 0` the
objective diverges along `‖θ‖ → ∞`. -/
theorem ceReg_coerce (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 ≤ lam) (θ : EuclideanSpace ℝ (Fin d)) :
    lam / 2 * ‖θ‖ ^ 2 ≤ ceReg X t lam θ := by
  have hnn := Hagi.Model.CEHeldout.ceOneHot_nonneg t (X *ᵥ θ.ofLp)
  unfold ceReg
  linarith

/-- **Attainment**: for `λ > 0` the regularized objective attains its
global minimum.  Route: the sublevel set `{θ | ceReg θ ≤ ceReg 0}` is
closed (continuity) and bounded (coercivity: `‖θ‖ ≤ √(2·ceReg 0/λ)`),
hence compact in the finite-dimensional `EuclideanSpace`; the extreme
value theorem `IsCompact.exists_isMinOn` gives the minimizer, and any
point outside the sublevel has value strictly above `ceReg 0 ≥ ceReg
θstar`. -/
theorem ceReg_attains (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ θstar : EuclideanSpace ℝ (Fin d), ∀ θ,
      ceReg X t lam θstar ≤ ceReg X t lam θ := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := ceReg X t lam
  have hcont : Continuous f := ceReg_continuous X t lam
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ {θ | f θ ≤ f 0} :=
    Set.mem_ofPred.2 le_rfl
  have hclosed : IsClosed {θ : EuclideanSpace ℝ (Fin d) | f θ ≤ f 0} :=
    isClosed_le hcont continuous_const
  have hbdd : Bornology.IsBounded {θ : EuclideanSpace ℝ (Fin d) | f θ ≤ f 0} := by
    have hsub : {θ : EuclideanSpace ℝ (Fin d) | f θ ≤ f 0} ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt (2 * f 0 / lam) + 1) := by
      intro θ hθ
      have hle : lam / 2 * ‖θ‖ ^ 2 ≤ f 0 :=
        (ceReg_coerce X t lam hlam.le θ).trans hθ
      have hf0 : (0:ℝ) ≤ f 0 := by
        have h := ceReg_coerce X t lam hlam.le 0
        simpa using h
      have hnorm : ‖θ‖ ≤ Real.sqrt (2 * f 0 / lam) := by
        refine (Real.le_sqrt (norm_nonneg θ)
          (div_nonneg (by nlinarith [hf0]) hlam.le)).2 ?_
        rw [le_div_iff₀ hlam]
        nlinarith [hle, sq_nonneg ‖θ‖]
      have hpos : (0:ℝ) < Real.sqrt (2 * f 0 / lam) + 1 := by positivity
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact Metric.isBounded_ball.subset hsub
  have hcomp : IsCompact {θ : EuclideanSpace ℝ (Fin d) | f θ ≤ f 0} :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbdd⟩
  obtain ⟨θstar, hmem, hmin⟩ :=
    hcomp.exists_isMinOn ⟨0, h0⟩ hcont.continuousOn
  refine ⟨θstar, fun θ => ?_⟩
  by_cases hθ : θ ∈ {θ : EuclideanSpace ℝ (Fin d) | f θ ≤ f 0}
  · exact hmin hθ
  · have hlt : f 0 < f θ := by
      by_contra hc
      exact hθ (not_lt.1 hc)
    exact (hmin h0).trans hlt.le

/-- **ENDGAME — geometric convergence for the real ℓ2-regularized
log-linear CE head with every analytic premise discharged.**
Instantiates `ce_global_convergence_reg` with `fstar := ceReg θstar`,
where `θstar` is supplied by `ceReg_attains` (attainment gives BOTH
the floor `h_floor` and the attainment `h_att`).

Honest premise ledger: the ONLY analytic premise is `hlam : 0 < lam`
(the regularization strength).  No `h_floor`, no `h_att`, no explicit
`θstar` binder (it is existential inside).  Data `X`, target `t`,
start `θ₀` and horizon `T` are explicit.  `X = 0` is admissible (the
objective degenerates to `(λ/2)‖θ‖²` with minimizer `0` and `L = λ`).
The unregularized rate keeps its `h_attains` premise by
mathematical necessity (bare CE is not coercive). -/
theorem ce_global_convergence_reg_closed (X : Matrix V (Fin d) ℝ) (t : V)
    (lam : ℝ) (hlam : 0 < lam)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∃ θstar : EuclideanSpace ℝ (Fin d),
      ceReg X t lam
          ((plStep (ceGradReg X t lam) (ceSmoothL X + lam))^[T] θ₀)
        - ceReg X t lam θstar
      ≤ (1 - lam / (ceSmoothL X + lam)) ^ T
        * (ceReg X t lam θ₀ - ceReg X t lam θstar) := by
  obtain ⟨θstar, hmin⟩ := ceReg_attains X t lam hlam
  exact ⟨θstar, ce_global_convergence_reg X t lam (ceReg X t lam θstar) hlam
    (fun _ => hmin _) θstar θ₀ (le_refl _) T⟩

end IdentReg

end Hagi.Model.CEGlobalConvergence

