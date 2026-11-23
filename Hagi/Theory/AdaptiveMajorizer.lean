/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.PoEBound
import Hagi.Model.CEDescent
import Hagi.Theory.CEChain
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The variance-adaptive cross-entropy majorizer (tight Bennett canon)

The range
majorizer `Hagi.Energy.lse_shift_upper` bounds the lse shift by
`r ^ 2 / 8`, which uses only the RANGE of the logit displacement and
ignores the variance under the target distribution.  Near the end of
training the soft target concentrates (one-hot limit), the variance
of the displacement under `smax x` collapses, but the range does not
— certified steps stay unjustifiably small (THEORY_ALIGNMENT pain).

CANON (tight): with the exact Bennett multiplier
`kappa r = (Real.exp r - 1 - r) / r ^ 2`,

`log (∑ v, exp (y v)) ≤ log (∑ v, exp (x v)) + ⟨smax x, y − x⟩
  + kappa r * varWeight (smax x) (y − x)`

with `1/2 ≤ kappa r ≤ Real.exp r` on `r > 0` (`kappa_ge_half`,
`kappa_le_expR`; monotone `kappa_mono`).  Every WEAK theorem of this
module (the family with the multiplier `Real.exp r` and the
weaker hypothesis `0 ≤ r` in place of `0 < r`) is a one-step
CONSEQUENCE of its tight twin via `kappa_le_expR` plus the
degenerate `r = 0` case (constant displacement, zero variance) —
no parallel proofs are maintained.

The mechanism is deliberately series-free (the series route hung on
`hasSum_nat_add_iff` whnf in a previous session, route 1):

- `kappa_mono` via `exp_aux_N_nonneg`: `N t = e ^ t * (t − 2) + t + 2`
  has `N 0 = N' 0 = 0`, `N'' t = t * e ^ t ≥ 0` — Lagrange MVT twice;
- positive side: Taylor–Lagrange of order two for `exp` via TWO
  applications of Lagrange's MVT (`exp_split_mvt`);
- negative side: the algebraic identity
  `(1 − u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) = 1 + u ^ 4 / 4`
  on top of `Real.quadratic_le_exp_of_nonneg`.

## Main results (tight canon; weak twins follow)

- `varMgf_le_tight` — the variance-sensitive CGF (Bennett) bound
  `log (∑ q v * exp (g v)) ≤ μ + kappa R * varWeight q g` for
  centered-at-μ weightings with range at most `R > 0`; weak
  `varMgf_le` (`Real.exp R`, `0 ≤ R`) is its consequence.
- `lse_shift_upper_var_tight` — the adaptive twin of
  `Hagi.Energy.lse_shift_upper`; weak `lse_shift_upper_var` follows.
- `ceOneHot_next_le_adaptive_tight` — the CE step majorizer with
  curvature `ceAdaptiveCurvTight`, valid for step sizes `η ∈ [0, 1]`
  (the cap is honest: the Bennett curvature `kappa (η * R)` is NOT
  uniform in `η`, so the `UniversalSafeStep` all-η law cannot hold
  with a Bennett-type constant; `kappa_mono` dominates `kappa (η * R)`
  by `kappa R` for `η ≤ 1`); weak `ceOneHot_next_le_adaptive`
  (`Real.exp R` multiplier) is its consequence.
- `adaptive_descent` / `ce_adaptive_descent_tight` (and the weak
  `ce_adaptive_descent`) — the safe step `η* = A / (2 * C)` with drop
  `A ^ 2 / (4 * C)` whenever `A / (2 * C) ≤ 1` (quadratic
  minimization, `universal_descent` algebra at bounded η).
- `ce_adaptive_drop_dominates_tight` (and the weak twin) — under
  `varWeight ≤ R ^ 2 / (8 * kappa R)` the adaptive drop dominates
  the range drop `2 * A ^ 2 / R ^ 2` of `singleSampleStep`.
- `ceOneHot_next_le_linear_of_zero_var_tight` (and the weak twin) —
  at concentrated targets (zero variance) the curvature term
  vanishes and the majorizer is exactly linear for every `η ≤ 1`.

## Honesty pin

The adaptive bound is NOT uniformly better than the range bound:
Popoviciu allows `varWeight ≤ R ^ 2 / 4` while the domination
threshold (tight) is `R ^ 2 / (8 * kappa R)`, which shrinks as `R`
grows.  For diffuse targets and large ranges the range majorizer
wins; for concentrated targets (the training-end regime this module
targets) the adaptive one wins.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.AdaptiveMajorizer

open Finset Real

/-! ## The weighted variance functional -/

/-- Weighted variance of `f` under weights `q` (finite sums, no
measure theory): `varWeight q f = ∑ v, q v * (f v − ∑ w, q w * f w) ^ 2`. -/

noncomputable def varWeight {V : Type} [Fintype V] (q f : V → ℝ) : ℝ :=
  ∑ v, q v * (f v - ∑ w, q w * f w) ^ 2

/-- The weighted variance is nonnegative for nonnegative weights. -/

theorem varWeight_nonneg {V : Type} [Fintype V] {q : V → ℝ}
    (hq : ∀ v, 0 ≤ q v) (f : V → ℝ) :
    0 ≤ varWeight q f := by
  unfold varWeight
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (hq v) (sq_nonneg _))

/-- Variance is quadratic: the variance of a rescaled function
`η • f` under the same weights is `η ^ 2 *` the variance of `f`. -/

theorem varWeight_scale {V : Type} [Fintype V] (q : V → ℝ)
    (f : V → ℝ) (η : ℝ) :
    varWeight q (fun v => η * f v) = η ^ 2 * varWeight q f := by
  classical
  have hexp : ∑ w, q w * (η * f w) = η * ∑ w, q w * f w := by
    have h1 : ∑ w, q w * (η * f w) = ∑ w, η * (q w * f w) :=
      Finset.sum_congr rfl (fun w _ => by ring)
    have h2 : ∑ w, η * (q w * f w) = η * ∑ w, q w * f w :=
      (Finset.mul_sum Finset.univ (fun w => q w * f w) η).symm
    rw [h1, h2]
  unfold varWeight
  simp only [hexp]
  show ∑ v, q v * (η * f v - η * ∑ w, q w * f w) ^ 2
      = η ^ 2 * ∑ v, q v * (f v - ∑ w, q w * f w) ^ 2
  have h3 : ∑ v, q v * (η * f v - η * ∑ w, q w * f w) ^ 2
      = ∑ v, η ^ 2 * (q v * (f v - ∑ w, q w * f w) ^ 2) :=
    Finset.sum_congr rfl (fun v _ => by ring)
  have h4 : ∑ v, η ^ 2 * (q v * (f v - ∑ w, q w * f w) ^ 2)
      = η ^ 2 * ∑ v, q v * (f v - ∑ w, q w * f w) ^ 2 :=
    (Finset.mul_sum Finset.univ
      (fun v => q v * (f v - ∑ w, q w * f w) ^ 2) (η ^ 2)).symm
  rw [h3, h4]

/-! ## The pointwise quadratic majorant of `exp` (series-free) -/

/-- Taylor–Lagrange of order two for `exp` via two applications of
Lagrange's MVT: `exp y = 1 + y + y * ξ1 * exp ξ2` with
`0 < ξ2 < ξ1 < y`. -/

theorem exp_split_mvt {y : ℝ} (hy : 0 < y) :
    ∃ ξ1 ξ2 : ℝ, 0 < ξ1 ∧ ξ1 < y ∧ 0 < ξ2 ∧ ξ2 < ξ1 ∧
      Real.exp y = 1 + y + y * ξ1 * Real.exp ξ2 := by
  obtain ⟨ξ1, hξ1, h1⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hy
    (continuous_exp.continuousOn) (fun x _ => (Real.hasDerivAt_exp x))
  obtain ⟨ξ2, hξ2, h2⟩ := exists_hasDerivAt_eq_slope Real.exp Real.exp hξ1.1
    (continuous_exp.continuousOn) (fun x _ => (Real.hasDerivAt_exp x))
  refine ⟨ξ1, ξ2, hξ1.1, hξ1.2, hξ2.1, hξ2.2, ?_⟩
  simp only [Real.exp_zero] at h1 h2
  field_simp at h1
  have key1 : Real.exp y = 1 + y * Real.exp ξ1 := by linarith
  have hξ1pos : (0:ℝ) < ξ1 := hξ1.1
  have key2 : Real.exp ξ1 = 1 + ξ1 * Real.exp ξ2 := by
    rw [h2]
    field_simp
    ring
  rw [key1, key2]
  ring

/-- Negative-side quadratic majorant
`exp y ≤ 1 + y + y ^ 2 / 2` for `y ≤ 0`, via the algebraic identity
`(1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) = 1 + u ^ 4 / 4` on top
of `Real.quadratic_le_exp_of_nonneg`. -/

theorem exp_quad_neg {y : ℝ} (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  have hu : 0 ≤ -y := by linarith
  have hlow := Real.quadratic_le_exp_of_nonneg hu
  have hpos : 0 < 1 + -y + (-y) ^ 2 / 2 := by
    have hsq := sq_nonneg (-y)
    nlinarith
  have hprod : (1 - -y + (-y) ^ 2 / 2) * (1 + -y + (-y) ^ 2 / 2)
      = 1 + (-y) ^ 4 / 4 := by ring
  have hinv : (1 + -y + (-y) ^ 2 / 2)⁻¹ ≤ 1 - -y + (-y) ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos, hprod]
    nlinarith
  have hexpinv : Real.exp y = (Real.exp (-y))⁻¹ := by
    rw [← Real.exp_neg]
    simp
  have hq : 0 < Real.exp (-y) := Real.exp_pos _
  calc Real.exp y = (Real.exp (-y))⁻¹ := hexpinv
    _ ≤ (1 + -y + (-y) ^ 2 / 2)⁻¹ :=
        (inv_le_inv₀ hq hpos).mpr hlow
    _ ≤ 1 - -y + (-y) ^ 2 / 2 := hinv
    _ = 1 + y + y ^ 2 / 2 := by ring

/-! ## The tight Bennett multiplier `kappa`

The exact Bennett constant `kappa R = (Real.exp R - 1 - R) / R ^ 2`
and its comparison laws — the CANON of the module; every weak
`Real.exp R` statement below is a consequence of these.  Series-free
mechanism: `kappa_mono` via `exp_aux_N_nonneg` (`N 0 = N' 0 = 0`,
`N'' t = t * e ^ t ≥ 0`, two MVT applications), and the pointwise
majorants via `exp_split_mvt` / `Real.quadratic_le_exp_of_nonneg`. -/

/-- The tight Bennett variance multiplier
`kappa R = (Real.exp R - 1 - R) / R ^ 2` (note `kappa 0 = 0` by Lean's
division; all theorems below assume `0 < R`). -/

noncomputable def kappa (R : ℝ) : ℝ := (Real.exp R - 1 - R) / R ^ 2

/-- The auxiliary polynomial-exponential `N x = e ^ x * (x - 2) + x + 2`
is nonnegative on `[0, ∞)`: `N 0 = N' 0 = 0` and `N'' x = x * e ^ x ≥ 0`,
via two Lagrange MVT applications (series-free). -/

theorem exp_aux_N_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp x * (x - 2) + x + 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => Real.exp t * (t - 2) + t + 2)
      (Real.exp t * (t - 1) + 1) t := by
    intro t
    have hd : HasDerivAt (fun t => t - 2) 1 t := by
      simpa using (hasDerivAt_id t).sub_const 2
    have h1 : HasDerivAt (fun t => Real.exp t * (t - 2))
        (Real.exp t * (t - 1)) t := by
      refine ((hasDerivAt_exp t).mul hd).congr_deriv ?_
      ring
    refine ((h1.add (hasDerivAt_id t)).add_const 2).congr_deriv ?_
    ring
  have hderiv2 : ∀ t : ℝ,
      HasDerivAt (fun t => Real.exp t * (t - 1) + 1) (t * Real.exp t) t := by
    intro t
    have hd : HasDerivAt (fun t => t - 1) 1 t := by
      simpa using (hasDerivAt_id t).sub_const 1
    have h1 : HasDerivAt (fun t => Real.exp t * (t - 1))
        (t * Real.exp t) t := by
      refine ((hasDerivAt_exp t).mul hd).congr_deriv ?_
      ring
    exact (h1.add_const 1).congr_deriv (by ring)
  obtain ⟨ξ1, hξ1, h1⟩ := exists_hasDerivAt_eq_slope
    (fun t => Real.exp t * (t - 2) + t + 2)
    (fun t => Real.exp t * (t - 1) + 1) hx'
    (by fun_prop) (fun t _ => hderiv t)
  obtain ⟨ξ2, hξ2, h2⟩ := exists_hasDerivAt_eq_slope
    (fun t => Real.exp t * (t - 1) + 1)
    (fun t => t * Real.exp t) hξ1.1
    (by fun_prop) (fun t _ => hderiv2 t)
  norm_num [Real.exp_zero] at h1 h2
  have he2 : 0 ≤ ξ2 * Real.exp ξ2 := mul_nonneg hξ2.1.le (Real.exp_nonneg _)
  have hpos : 0 < ξ1 := hξ1.1
  have hg : 0 ≤ Real.exp ξ1 * (ξ1 - 1) + 1 := by
    have hthis := h2
    field_simp at hthis ⊢
    nlinarith [he2]
  have hNx : Real.exp x * (x - 2) + x + 2
      = x * (Real.exp ξ1 * (ξ1 - 1) + 1) := by
    rw [h1]
    field_simp
  nlinarith

/-- The derivative of `h t = (e ^ t - 1 - t) / t ^ 2` is
`t * N t / t ^ 4`. -/

private theorem kappa_deriv_aux (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => (Real.exp t - 1 - t) / t ^ 2)
      (x * (Real.exp x * (x - 2) + x + 2) / x ^ 4) x := by
  have hnum : HasDerivAt (fun t => Real.exp t - 1 - t) (Real.exp x - 1) x :=
    (((hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)).congr_deriv
      (by ring)
  have hden : HasDerivAt (fun t => t ^ 2) (2 * x) x :=
    ((hasDerivAt_id x).pow 2).congr_deriv (by simp)
  have hdiv := hnum.div hden (pow_ne_zero 2 hx)
  refine hdiv.congr_deriv ?_
  field_simp
  ring

/-- **Monotonicity of the Bennett multiplier**: `kappa` is monotone on
`(0, ∞)` (third MVT on `h t = (e ^ t - 1 - t) / t ^ 2`, derivative
sign from `exp_aux_N_nonneg`). -/

theorem kappa_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    kappa a ≤ kappa b := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · rfl
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope
    (fun t => (Real.exp t - 1 - t) / t ^ 2)
    (fun t => t * (Real.exp t * (t - 2) + t + 2) / t ^ 4) hab'
    (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => pow_ne_zero 2 (by
        have h1 : a ≤ t := ht.1
        linarith)))
    (fun t ht => kappa_deriv_aux t (by
      obtain ⟨h1, h2⟩ := ht
      linarith))
  have hξ0 : 0 < ξ := lt_trans ha hξ.1
  have hNpos : 0 ≤ ξ * (Real.exp ξ * (ξ - 2) + ξ + 2) :=
    mul_nonneg hξ0.le (exp_aux_N_nonneg hξ0.le)
  have hne : (b:ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab'.ne)
  have key := (div_eq_iff hne).mp h.symm
  have hpos : (0:ℝ) ≤ ξ * (Real.exp ξ * (ξ - 2) + ξ + 2) / ξ ^ 4 * (b - a) :=
    mul_nonneg (div_nonneg hNpos (by positivity))
      (sub_nonneg.mpr (le_of_lt hab'))
  unfold kappa
  linarith [key, hpos]

/-- `kappa R ≥ 1/2` for `R > 0` (Taylor: `e ^ R ≥ 1 + R + R ^ 2 / 2`). -/

theorem kappa_ge_half {R : ℝ} (hR : 0 < R) :
    1 / 2 ≤ kappa R := by
  have h := Real.quadratic_le_exp_of_nonneg hR.le
  unfold kappa
  rw [le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
  nlinarith

/-- `kappa R > 0` for `R > 0`. -/

theorem kappa_pos {R : ℝ} (hR : 0 < R) : 0 < kappa R :=
  lt_of_lt_of_le (by norm_num) (kappa_ge_half hR)

/-- **The comparison theorem**: the tight Bennett multiplier always
dominates-loses to the weakened multiplier `Real.exp R`, for
every `R > 0` (via `1 - R ≤ e ^ (-R)`, i.e. `e ^ R - 1 ≤ R * e ^ R`). -/

theorem kappa_le_expR {R : ℝ} (hR : 0 < R) :
    kappa R ≤ Real.exp R := by
  have hneg := Real.one_sub_le_exp_neg R
  have hexp : 0 < Real.exp R := Real.exp_pos _
  have key : Real.exp R * (1 - R) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hneg hexp.le
    rw [Real.exp_neg, inv_mul_cancel₀ (ne_of_gt hexp)] at hmul
    linarith
  unfold kappa
  rw [div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
  nlinarith

/-- **The tight positive-side quadratic majorant**: for `y ∈ [0, R]`
with `R > 0`, `e ^ y ≤ 1 + y + kappa R * y ^ 2` (monotonicity of
`kappa` against `kappa y`). -/

theorem exp_quad_pos_tight {y R : ℝ} (hR : 0 < R) (hy0 : 0 ≤ y)
    (hyR : y ≤ R) :
    Real.exp y ≤ 1 + y + kappa R * y ^ 2 := by
  rcases eq_or_lt_of_le hy0 with rfl | hy'
  · simp
  have hmono := kappa_mono hy' hyR
  have hmul : kappa y * y ^ 2 ≤ kappa R * y ^ 2 :=
    mul_le_mul_of_nonneg_right hmono (sq_nonneg y)
  unfold kappa at hmul ⊢
  field_simp at hmul ⊢
  linarith

/-- **The tight two-sided quadratic majorant**: on `|y| ≤ R` with
`R > 0`, `e ^ y ≤ 1 + y + kappa R * y ^ 2` (negative side: the `y ^ 2 / 2`
of `exp_quad_neg` dominated by `kappa R ≥ 1/2`). -/

theorem exp_quad_bound_tight {y R : ℝ} (hR : 0 < R) (hyR : |y| ≤ R) :
    Real.exp y ≤ 1 + y + kappa R * y ^ 2 := by
  by_cases hy0 : 0 ≤ y
  · exact exp_quad_pos_tight hR hy0 (by rw [abs_of_nonneg hy0] at hyR; exact hyR)
  · have hhalf : y ^ 2 / 2 ≤ kappa R * y ^ 2 := by
      have h1 : (1:ℝ) / 2 ≤ kappa R := kappa_ge_half hR
      have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
      calc y ^ 2 / 2 = (1 / 2) * y ^ 2 := by ring
        _ ≤ kappa R * y ^ 2 := mul_le_mul_of_nonneg_right h1 hy2
    have hyle : y ≤ 0 := by linarith
    have hn := exp_quad_neg hyle
    nlinarith

/-- Zero range kills the variance: if `g u - g v ≤ 0` for all `u, v`
(then `g` is constant), `varWeight q g = 0`. -/

theorem varWeight_eq_zero_of_range_le_zero {V : Type} [Fintype V]
    [Nonempty V] (q : V → ℝ) (hq1 : ∑ v, q v = 1)
    (g : V → ℝ) (hr : ∀ u v, g u - g v ≤ 0) :
    varWeight q g = 0 := by
  obtain ⟨w⟩ : Nonempty V := ‹_›
  have hconst : ∀ v, g v = g w := by
    intro v
    have h1 : g v ≤ g w := by linarith [hr v w]
    have h2 : g w ≤ g v := by linarith [hr w v]
    linarith
  have hμ : ∑ v, q v * g v = g w := by
    have hterm : ∀ v, q v * g v = q v * g w := fun v => by rw [hconst v]
    have hsum : ∑ v, q v * g v = ∑ v, q v * g w :=
      Finset.sum_congr rfl (fun v _ => hterm v)
    rw [hsum, ← Finset.sum_mul, hq1, one_mul]
  unfold varWeight
  rw [hμ]
  simp [hconst]

/-! ## The weak twins: corollaries of the tight canon

Each weak statement (multiplier `Real.exp R`, hypothesis `0 ≤ R`)
follows from its tight twin by `kappa_le_expR` plus the degenerate
`R = 0` case (constant function, zero variance).  Kept as public
one-step consequences; no parallel proofs. -/

/-- Positive-side quadratic majorant with the weakened multiplier
`Real.exp R`: corollary of the tight `exp_quad_pos_tight` via the
comparison theorem `kappa_le_expR` (the statement, now a tight
consequence). -/
theorem exp_quad_pos {y R : ℝ} (_hR : 0 ≤ R) (hy0 : 0 ≤ y)
    (hyR : y ≤ R) :
    Real.exp y ≤ 1 + y + Real.exp R * y ^ 2 := by
  rcases eq_or_lt_of_le _hR with hR0 | hR'
  · rw [← hR0] at hyR ⊢
    have hy : y = 0 := le_antisymm hyR hy0
    subst hy
    simp
  · have h := exp_quad_pos_tight hR' hy0 hyR
    have hk := kappa_le_expR hR'
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith


/-- The two-sided pointwise quadratic majorant with the weakened
multiplier `Real.exp R`: corollary of the tight
`exp_quad_bound_tight` via `kappa_le_expR` (at `R = 0` both sides
collapse to `y = 0`). -/
theorem exp_quad_bound {y R : ℝ} (hR : 0 ≤ R) (hyR : |y| ≤ R) :
    Real.exp y ≤ 1 + y + Real.exp R * y ^ 2 := by
  rcases eq_or_lt_of_le hR with hR0 | hR'
  · rw [← hR0] at hyR
    have hy : y = 0 := by
      have h := abs_le.mp hyR
      linarith [h.1, h.2]
    subst hy
    simp
  · have h := exp_quad_bound_tight hR' hyR
    have hk := kappa_le_expR hR'
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    nlinarith


/-! ## The variance-sensitive CGF bound (tight canon, weak follows) -/

/-- The variance-sensitive CGF bound with the TIGHT Bennett
multiplier `kappa R = (e ^ R - 1 - R) / R ^ 2`: for
weights `q` of total mass one and a function `g` of range at most
`R > 0`, the log-mgf is bounded by the mean plus `kappa R` times the
`q`-variance. Dominates `varMgf_le` by `kappa_le_expR`. -/

theorem varMgf_le_tight {V : Type} [Fintype V] [Nonempty V] (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (g : V → ℝ) {R : ℝ} (hR : 0 < R)
    (hr : ∀ u v, g u - g v ≤ R) :
    Real.log (∑ v, q v * Real.exp (g v))
      ≤ (∑ v, q v * g v) + kappa R * varWeight q g := by
  set μ : ℝ := ∑ v, q v * g v with hμdef
  -- the centered function has q-expectation zero
  have hcenter : ∑ v, q v * (g v - μ) = 0 := by
    have h1 : ∑ v, q v * (g v - μ)
        = ∑ v, (q v * g v - q v * μ) :=
      Finset.sum_congr rfl (fun v _ => by ring)
    have h2 : ∑ v, (q v * g v - q v * μ)
        = (∑ v, q v * g v) - (μ * ∑ v, q v) := by
      have hs : ∑ v, (q v * g v - q v * μ)
          = (∑ v, q v * g v) - ∑ v, q v * μ :=
        Finset.sum_sub_distrib _ _
      have hm : ∑ v, q v * μ = μ * ∑ v, q v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v _ => by ring)
      rw [hs, hm]
    rw [h1, h2, hq1, mul_one, ← hμdef]
    ring
  -- the centered function is confined to [-R, R]
  have hconf : ∀ u, |g u - μ| ≤ R := by
    intro u
    have hup : g u - μ ≤ R := by
      have hstep : ∀ v, q v * (g u - μ) ≤ q v * ((g v - μ) + R) := by
        intro v
        have huv : g u - g v ≤ R := hr u v
        exact mul_le_mul_of_nonneg_left (by simp only [hμdef]; linarith)
          (hq0 v)
      have hsum : ∑ v, q v * (g u - μ)
          ≤ ∑ v, q v * ((g v - μ) + R) :=
        Finset.sum_le_sum (fun v _ => hstep v)
      have hleft : ∑ v, q v * (g u - μ) = (g u - μ) * ∑ v, q v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v _ => by ring)
      have hright : ∑ v, q v * ((g v - μ) + R)
          = (∑ v, q v * (g v - μ)) + R * ∑ v, q v := by
        have hsplit : ∑ v, q v * ((g v - μ) + R)
            = ∑ v, (q v * (g v - μ) + q v * R) :=
          Finset.sum_congr rfl (fun v _ => by ring)
        have hsa : ∑ v, (q v * (g v - μ) + q v * R)
            = (∑ v, q v * (g v - μ)) + ∑ v, q v * R :=
          Finset.sum_add_distrib
        have hm : ∑ v, q v * R = R * ∑ v, q v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun v _ => by ring)
        rw [hsplit, hsa, hm]
      rw [hleft, hright, hq1, mul_one, hcenter] at hsum
      linarith
    have hdown : -R ≤ g u - μ := by
      have hstep : ∀ v, q v * (g v - μ) ≤ q v * ((g u - μ) + R) := by
        intro v
        have hvu : g v - g u ≤ R := hr v u
        exact mul_le_mul_of_nonneg_left (by simp only [hμdef]; linarith)
          (hq0 v)
      have hsum : ∑ v, q v * (g v - μ)
          ≤ ∑ v, q v * ((g u - μ) + R) :=
        Finset.sum_le_sum (fun v _ => hstep v)
      have hright : ∑ v, q v * ((g u - μ) + R)
          = (∑ v, q v * (g u - μ)) + R * ∑ v, q v := by
        have hsplit : ∑ v, q v * ((g u - μ) + R)
            = ∑ v, (q v * (g u - μ) + q v * R) :=
          Finset.sum_congr rfl (fun v _ => by ring)
        have hsa : ∑ v, (q v * (g u - μ) + q v * R)
            = (∑ v, q v * (g u - μ)) + ∑ v, q v * R :=
          Finset.sum_add_distrib
        have hm : ∑ v, q v * R = R * ∑ v, q v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun v _ => by ring)
        rw [hsplit, hsa, hm]
      have hleft : ∑ v, q v * (g u - μ) = (g u - μ) * ∑ v, q v := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v _ => by ring)
      rw [hright, hleft, hq1, mul_one] at hsum
      rw [hcenter] at hsum
      linarith
    exact abs_le.mpr ⟨hdown, hup⟩
  -- pointwise tight majorant, summed with weights q
  have hsum : ∑ v, q v * Real.exp (g v - μ)
      ≤ ∑ v, q v * (1 + (g v - μ) + kappa R * (g v - μ) ^ 2) :=
    Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left (exp_quad_bound_tight hR (hconf v)) (hq0 v))
  have hvw : varWeight q g = ∑ v, q v * (g v - μ) ^ 2 := by
    unfold varWeight
    rw [← hμdef]
  have hopen : ∑ v, q v * (1 + (g v - μ) + kappa R * (g v - μ) ^ 2)
      = 1 + kappa R * varWeight q g := by
    have hsplit : ∑ v, q v * (1 + (g v - μ) + kappa R * (g v - μ) ^ 2)
        = (∑ v, q v) + (∑ v, q v * (g v - μ))
          + kappa R * ∑ v, q v * (g v - μ) ^ 2 := by
      have ha : ∑ v, q v * (1 + (g v - μ) + kappa R * (g v - μ) ^ 2)
          = ∑ v, (q v + q v * (g v - μ)
            + kappa R * (q v * (g v - μ) ^ 2)) :=
        Finset.sum_congr rfl (fun v _ => by ring)
      have hsa : ∑ v, (q v + q v * (g v - μ)
          + kappa R * (q v * (g v - μ) ^ 2))
          = (∑ v, q v) + (∑ v, q v * (g v - μ))
            + ∑ v, kappa R * (q v * (g v - μ) ^ 2) := by
        have h1 : ∑ v, (q v + q v * (g v - μ)
            + kappa R * (q v * (g v - μ) ^ 2))
            = (∑ v, (q v + q v * (g v - μ)))
              + ∑ v, kappa R * (q v * (g v - μ) ^ 2) :=
          Finset.sum_add_distrib
        have h2 : (∑ v, (q v + q v * (g v - μ)))
            = (∑ v, q v) + (∑ v, q v * (g v - μ)) :=
          Finset.sum_add_distrib
        rw [h1, h2]
      have hm : ∑ v, kappa R * (q v * (g v - μ) ^ 2)
          = kappa R * ∑ v, q v * (g v - μ) ^ 2 :=
        (Finset.mul_sum Finset.univ
          (fun v => q v * (g v - μ) ^ 2) (kappa R)).symm
      rw [ha, hsa, hm]
    rw [hsplit, hq1, hcenter, hvw]
    ring
  rw [hopen] at hsum
  -- the centered mgf is at least one
  have hvw0 : 0 ≤ varWeight q g := varWeight_nonneg hq0 g
  have hE : 0 ≤ kappa R := (kappa_pos hR).le
  have hlinsum : ∑ v, q v * (1 + (g v - μ))
      = 1 + ∑ v, q v * (g v - μ) := by
    have hsplit : ∑ v, q v * (1 + (g v - μ))
        = ∑ v, (q v + q v * (g v - μ)) :=
      Finset.sum_congr rfl (fun v _ => by ring)
    have hsa : ∑ v, (q v + q v * (g v - μ))
        = (∑ v, q v) + ∑ v, q v * (g v - μ) :=
      Finset.sum_add_distrib
    rw [hsplit, hsa, hq1]
  have hlowS : ∑ v, q v * (1 + (g v - μ))
      ≤ ∑ v, q v * Real.exp (g v - μ) :=
    Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left
        (by have := Real.add_one_le_exp (g v - μ); linarith) (hq0 v))
  have hS1 : (1:ℝ) ≤ ∑ v, q v * Real.exp (g v - μ) := by
    have h1 : (1:ℝ) + ∑ v, q v * (g v - μ)
        ≤ ∑ v, q v * Real.exp (g v - μ) := by
      rw [← hlinsum]
      exact hlowS
    rw [hcenter, add_zero] at h1
    exact h1
  have hSpos : 0 < ∑ v, q v * Real.exp (g v - μ) := by linarith
  -- log of the centered mgf is bounded by the variance term
  have hlogS : Real.log (∑ v, q v * Real.exp (g v - μ))
      ≤ kappa R * varWeight q g := by
    refine le_trans (Real.log_le_log hSpos hsum) ?_
    have h1 : 0 < 1 + kappa R * varWeight q g := by
      have hmul := mul_nonneg hE hvw0
      nlinarith
    have h2 := Real.log_le_sub_one_of_pos h1
    linarith
  -- shift the mean out of the exponential
  have hshift : ∑ v, q v * Real.exp (g v)
      = Real.exp μ * ∑ v, q v * Real.exp (g v - μ) := by
    have hterm : ∀ v, q v * Real.exp (g v)
        = Real.exp μ * (q v * Real.exp (g v - μ)) := by
      intro v
      rw [Real.exp_sub]
      field_simp
    rw [Finset.mul_sum Finset.univ
      (fun v => q v * Real.exp (g v - μ)) (Real.exp μ)]
    exact Finset.sum_congr rfl (fun v _ => hterm v)
  rw [hshift, Real.log_mul (Real.exp_ne_zero μ) (ne_of_gt hSpos),
    Real.log_exp]
  linarith

/-- The variance-sensitive CGF bound (Bennett with the weakened
multiplier `Real.exp R`): for weights `q` with total mass one and a
function `g` of range at most `R ≥ 0`, the log-mgf at `g` is bounded
by the mean plus `Real.exp R` times the `q`-variance of `g`.
Corollary of the tight `varMgf_le_tight` via `kappa_le_expR`; the
degenerate `R = 0` case is the constant-`g` equality. -/

theorem varMgf_le {V : Type} [Fintype V] [Nonempty V] (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (g : V → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hr : ∀ u v, g u - g v ≤ R) :
    Real.log (∑ v, q v * Real.exp (g v))
      ≤ (∑ v, q v * g v) + Real.exp R * varWeight q g := by
  rcases eq_or_lt_of_le hR with hR0 | hR'
  · -- R = 0: g is constant, variance zero, log-mgf = mean
    have hg : ∀ u v, g u - g v ≤ 0 := by
      intro u v
      have h2 := hr u v
      rw [← hR0] at h2
      linarith
    have hvw : varWeight q g = 0 :=
      varWeight_eq_zero_of_range_le_zero q hq1 g hg
    obtain ⟨w⟩ : Nonempty V := ‹_›
    have hconst : ∀ v, g v = g w := by
      intro v
      have h1 : g v - g w ≤ 0 := hg v w
      have h2 : g w - g v ≤ 0 := hg w v
      linarith
    have hsume : ∑ v, q v * Real.exp (g v) = Real.exp (g w) := by
      have hc : ∑ v, q v * Real.exp (g v)
          = ∑ v, q v * Real.exp (g w) :=
        Finset.sum_congr rfl (fun v _ => by rw [hconst v])
      rw [hc, ← Finset.sum_mul, hq1, one_mul]
    have hsumg : ∑ v, q v * g v = g w := by
      have hc : ∑ v, q v * g v = ∑ v, q v * g w :=
        Finset.sum_congr rfl (fun v _ => by rw [hconst v])
      rw [hc, ← Finset.sum_mul, hq1, one_mul]
    rw [hvw, hsume, hsumg]
    simp
  · -- R > 0: the tight twin dominates coefficient-wise
    have h := varMgf_le_tight q hq0 hq1 g hR' hr
    have hk := kappa_le_expR hR'
    have hvw0 : 0 ≤ varWeight q g := varWeight_nonneg hq0 g
    nlinarith


/-- **The variance-adaptive lse bound with the tight Bennett
multiplier**: the tight twin of `lse_shift_upper_var` (and of
`Hagi.Energy.lse_shift_upper`); dominates both by `kappa_le_expR`. -/

theorem lse_shift_upper_var_tight {V : Type} [Fintype V] [Nonempty V]
    (x y : V → ℝ) (r : ℝ) (hr0 : 0 < r)
    (hr : ∀ u v, (y u - x u) - (y v - x v) ≤ r) :
    Real.log (∑ v, Real.exp (y v)) ≤ Real.log (∑ v, Real.exp (x v))
      + ∑ v, Hagi.Energy.smax x v * (y v - x v)
      + kappa r * varWeight (Hagi.Energy.smax x) (fun v => y v - x v) := by
  have hZx := Hagi.Energy.sum_exp_pos x
  have hZy := Hagi.Energy.sum_exp_pos y
  have hmgf := varMgf_le_tight (Hagi.Energy.smax x)
    (fun v => Hagi.Energy.smax_nonneg x v) (Hagi.Energy.smax_sum_one x)
    (fun v => y v - x v) hr0 hr
  have hE : ∑ v, Hagi.Energy.smax x v * Real.exp ((fun v => y v - x v) v)
      = (∑ v, Real.exp (y v)) / (∑ v, Real.exp (x v)) := by
    rw [Hagi.Energy.sum_smax_exp (x := x) (fun v => y v - x v)]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by
      congr 1
      ring)
  simp only [hE] at hmgf
  rw [Real.log_div (ne_of_gt hZy) (ne_of_gt hZx)] at hmgf
  have hμ : ∑ v, Hagi.Energy.smax x v * (y v - x v)
      = ∑ v, Hagi.Energy.smax x v * ((fun v => y v - x v) v) := rfl
  rw [hμ] at hmgf ⊢
  linarith

/-! ## The adaptive lse majorant -/

/-- **The variance-adaptive lse bound**: the adaptive twin of
`Hagi.Energy.lse_shift_upper`.  The deviation `lse(y) − lse(x)`
exceeds the first-order term by at most
`Real.exp r * varWeight (smax x) (y − x)` whenever the range of
`y − x` is dominated by `r`.  At concentrated `smax x` (one-hot
limit) the variance term collapses while `r ^ 2 / 8` does not. -/

theorem lse_shift_upper_var {V : Type} [Fintype V] [Nonempty V]
    (x y : V → ℝ) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ u v, (y u - x u) - (y v - x v) ≤ r) :
    Real.log (∑ v, Real.exp (y v)) ≤ Real.log (∑ v, Real.exp (x v))
      + ∑ v, Hagi.Energy.smax x v * (y v - x v)
      + Real.exp r * varWeight (Hagi.Energy.smax x) (fun v => y v - x v) := by
  have hZx := Hagi.Energy.sum_exp_pos x
  have hZy := Hagi.Energy.sum_exp_pos y
  have hmgf := varMgf_le (Hagi.Energy.smax x)
    (fun v => Hagi.Energy.smax_nonneg x v) (Hagi.Energy.smax_sum_one x)
    (fun v => y v - x v) hr0 hr
  have hE : ∑ v, Hagi.Energy.smax x v * Real.exp ((fun v => y v - x v) v)
      = (∑ v, Real.exp (y v)) / (∑ v, Real.exp (x v)) := by
    rw [Hagi.Energy.sum_smax_exp (x := x) (fun v => y v - x v)]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => by
      congr 1
      ring)
  simp only [hE] at hmgf
  rw [Real.log_div (ne_of_gt hZy) (ne_of_gt hZx)] at hmgf
  have hμ : ∑ v, Hagi.Energy.smax x v * (y v - x v)
      = ∑ v, Hagi.Energy.smax x v * ((fun v => y v - x v) v) := rfl
  rw [hμ] at hmgf ⊢
  linarith

/-! ## The CE consumer: adaptive safe step -/

variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- **The adaptive safe step (bounded-η form)**: a quadratic
majorizer valid for all `η ∈ [0, 1]` yields the certified drop
`A ^ 2 / (4 * C)` at `η* = A / (2 * C)` whenever `η* ≤ 1` — the
`universal_descent` algebra at bounded step size. -/

theorem adaptive_descent {L : ℝ} (next : ℝ → ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 < C)
    (hmq : ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      next η ≤ L - η * A + η ^ 2 * C)
    (hstar : A / (2 * C) ≤ 1) :
    next (A / (2 * C)) ≤ L - A ^ 2 / (4 * C) := by
  have hη0 : 0 ≤ A / (2 * C) := div_nonneg hA (by positivity)
  have h := hmq _ hη0 hstar
  have hkey : A / (2 * C) * A - (A / (2 * C)) ^ 2 * C
      = A ^ 2 / (4 * C) := by
    field_simp
    ring
  linarith

/-- The adaptive curvature of the single-sample CE step: the
weakened Bennett multiplier `Real.exp R` at the one-unit logit
range `R = ceStepRange`, times the variance of the directional
logit displacement under the current soft target
`smax (ceLogits X θ)`. Weakened form (`Real.exp R` for the
multiplier); the tight Bennett canon is `ceAdaptiveCurvTight` with
`κ R = (Real.exp R - 1 - R) / R ^ 2`, which dominates this one by
`kappa_le_expR`. -/

noncomputable def ceAdaptiveCurv (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  Real.exp (Hagi.Model.ceStepRange X θ t)
    * varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)

/-- The tight adaptive curvature of the single-sample CE step: the
Bennett multiplier `kappa` at the one-unit logit range, times the
variance of the directional logit displacement under the soft
target. Dominates `ceAdaptiveCurv` coefficient-wise by
`kappa_le_expR`. -/

noncomputable def ceAdaptiveCurvTight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  kappa (Hagi.Model.ceStepRange X θ t)
    * varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)

/-- **The tight adaptive CE step majorizer**: for every step size
`η ∈ [0, 1]` the cross-entropy after the step is bounded with the
Bennett curvature `ceAdaptiveCurvTight`. At `η = 0` or zero step
range the curvature term vanishes (a constant displacement has zero
variance, so the majorizer is exactly linear); at `η > 0` and positive range the proof uses
`kappa_mono` in place of the `exp` monotonicity.  This theorem is
the CANON; the weak `ceOneHot_next_le_adaptive` is its
consequence. -/

theorem ceOneHot_next_le_adaptive_tight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η)
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - η * Hagi.Model.ceAlignment X θ t
        + η ^ 2 * ceAdaptiveCurvTight X θ t := by
  rcases eq_or_lt_of_le hη0 with rfl | hη'
  · -- eta = 0: the step is the identity; the bound is an equality
    have hstep : Hagi.Model.ceNextLogits X θ t 0 = Hagi.Model.ceLogits X θ := by
      funext v
      rw [Hagi.Model.ceNextLogits_apply X θ t 0 v]
      ring
    rw [hstep]
    simp
  have hR : 0 ≤ Hagi.Model.ceStepRange X θ t :=
    Hagi.Model.ceStepRange_nonneg X θ t
  rcases eq_or_lt_of_le hR with hR0 | hR'
  · -- zero step range: the displacement is constant, variance zero
    have hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      = 0 := by
      refine varWeight_eq_zero_of_range_le_zero _
        (Hagi.Energy.smax_sum_one _) _ ?_
      intro u v
      have hr := Hagi.Model.ce_displacement_range X θ t hη0
      rw [← hR0] at hr
      have hu : Hagi.Model.ceNextLogits X θ t η u
          - Hagi.Model.ceLogits X θ u
          = η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) u := by
        rw [Hagi.Model.ceNextLogits_apply X θ t η u]
        ring
      have hv : Hagi.Model.ceNextLogits X θ t η v
          - Hagi.Model.ceLogits X θ v
          = η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v := by
        rw [Hagi.Model.ceNextLogits_apply X θ t η v]
        ring
      have hcomb : (Hagi.Model.ceNextLogits X θ t η u - Hagi.Model.ceLogits X θ u)
          - (Hagi.Model.ceNextLogits X θ t η v - Hagi.Model.ceLogits X θ v)
          = η * (Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) u
              - Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) := by
        rw [hu, hv]
        ring
      have hruv := hr u v
      nlinarith [hruv, hcomb, hη']
    have hcurv0 : ceAdaptiveCurvTight X θ t = 0 := by
      unfold ceAdaptiveCurvTight
      unfold kappa
      rw [← hR0]
      simp
    rw [hcurv0, mul_zero, add_zero]
    -- linear bound inline (no dependency on the weak family): the
    -- weak lse twin at r = η * R = 0 with the variance collapsed
    rw [Hagi.Energy.smax_eq_softDef (Hagi.Model.ceLogits X θ)] at hvar
    have hlse0 := lse_shift_upper_var (Hagi.Model.ceLogits X θ)
      (Hagi.Model.ceNextLogits X θ t η) (η * Hagi.Model.ceStepRange X θ t)
      (mul_nonneg hη0 hR) (Hagi.Model.ce_displacement_range X θ t hη0)
    have hlin := Hagi.Model.ce_first_order_eq X θ t η
    have ht := Hagi.Model.ceNextLogits_apply X θ t η t
    classical
    have honehot : ∑ v, (if v = t then (1 : ℝ) else 0)
        * (Hagi.Model.ceNextLogits X θ t η v - Hagi.Model.ceLogits X θ v)
        = Hagi.Model.ceNextLogits X θ t η t - Hagi.Model.ceLogits X θ t := by
      simp
    simp only [Hagi.Model.ceResidual, sub_mul, Finset.sum_sub_distrib] at hlin
    rw [honehot, ht] at hlin
    rw [Hagi.Energy.smax_eq_softDef (Hagi.Model.ceLogits X θ)] at hlse0
    have hsoft : ∑ v, Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ) v
        * (Hagi.Model.ceNextLogits X θ t η v - Hagi.Model.ceLogits X θ v)
        = -η * Hagi.Model.ceAlignment X θ t
          + η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) t := by
      linarith
    rw [hsoft] at hlse0
    have happly : ∀ v, Hagi.Model.ceNextLogits X θ t η v
        - Hagi.Model.ceLogits X θ v
        = η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v := by
      intro v
      rw [Hagi.Model.ceNextLogits_apply X θ t η v]
      ring
    have hscale : varWeight
        (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceNextLogits X θ t η v
          - Hagi.Model.ceLogits X θ v)
        = η ^ 2 * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
            (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) := by
      have hvar2 := varWeight_scale
        (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) η
      have hfun : (fun v => η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
          = (fun v => Hagi.Model.ceNextLogits X θ t η v
              - Hagi.Model.ceLogits X θ v) := by
        funext v
        rw [happly v]
      rw [← hfun]
      exact hvar2
    rw [hscale, hvar, mul_zero, mul_zero, add_zero] at hlse0
    unfold Hagi.ceOneHot Hagi.Core.lse
    rw [ht]
    linarith
  have hlse := lse_shift_upper_var_tight (Hagi.Model.ceLogits X θ)
    (Hagi.Model.ceNextLogits X θ t η) (η * Hagi.Model.ceStepRange X θ t)
    (mul_pos hη' hR') (Hagi.Model.ce_displacement_range X θ t hη0)
  have hlin := Hagi.Model.ce_first_order_eq X θ t η
  have ht := Hagi.Model.ceNextLogits_apply X θ t η t
  classical
  have honehot : ∑ v, (if v = t then (1 : ℝ) else 0)
      * (Hagi.Model.ceNextLogits X θ t η v - Hagi.Model.ceLogits X θ v)
      = Hagi.Model.ceNextLogits X θ t η t - Hagi.Model.ceLogits X θ t := by
    simp
  simp only [Hagi.Model.ceResidual, sub_mul, Finset.sum_sub_distrib] at hlin
  rw [honehot, ht] at hlin
  rw [Hagi.Energy.smax_eq_softDef (Hagi.Model.ceLogits X θ)] at hlse
  have hsoft : ∑ v, Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ) v
      * (Hagi.Model.ceNextLogits X θ t η v - Hagi.Model.ceLogits X θ v)
      = -η * Hagi.Model.ceAlignment X θ t
        + η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) t := by
    linarith
  have happly : ∀ v, Hagi.Model.ceNextLogits X θ t η v
      - Hagi.Model.ceLogits X θ v
      = η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v := by
    intro v
    rw [Hagi.Model.ceNextLogits_apply X θ t η v]
    ring
  rw [hsoft] at hlse
  -- the variance of the eta-scaled displacement (softDef weights)
  have hscale : varWeight
      (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
      (fun v => Hagi.Model.ceNextLogits X θ t η v
        - Hagi.Model.ceLogits X θ v)
      = η ^ 2 * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
          (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) := by
    have hvar' := varWeight_scale
      (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
      (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) η
    have hfun : (fun v => η * Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
        = (fun v => Hagi.Model.ceNextLogits X θ t η v
            - Hagi.Model.ceLogits X θ v) := by
      funext v
      rw [happly v]
    rw [← hfun]
    exact hvar'
  rw [hscale] at hlse
  -- kappa (eta * R) ≤ kappa R by kappa_mono
  have hkap : kappa (η * Hagi.Model.ceStepRange X θ t)
      ≤ kappa (Hagi.Model.ceStepRange X θ t) :=
    kappa_mono (mul_pos hη' hR')
      (by nlinarith [mul_le_mul_of_nonneg_right hη1 hR])
  have hvD0 : 0 ≤ varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
      (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) := by
    have h := varWeight_nonneg
      (fun v => Hagi.Energy.smax_nonneg (Hagi.Model.ceLogits X θ) v)
      (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
    rw [Hagi.Energy.smax_eq_softDef (Hagi.Model.ceLogits X θ)] at h
    exact h
  -- reassociate and dominate kappa (eta * R) by kappa R
  have hswap : kappa (η * Hagi.Model.ceStepRange X θ t)
      * (η ^ 2 * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
          (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v))
      = η ^ 2 * (kappa (η * Hagi.Model.ceStepRange X θ t)
          * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
            (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)) := by
    ring
  rw [hswap] at hlse
  have hmono2 : η ^ 2 * (kappa (η * Hagi.Model.ceStepRange X θ t)
          * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
            (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v))
      ≤ η ^ 2 * (kappa (Hagi.Model.ceStepRange X θ t)
          * varWeight (Hagi.Prelude.softDef (Hagi.Model.ceLogits X θ))
            (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hkap hvD0) (sq_nonneg η)
  unfold Hagi.ceOneHot Hagi.Core.lse
  rw [ht]
  unfold ceAdaptiveCurvTight
  rw [Hagi.Energy.smax_eq_softDef (Hagi.Model.ceLogits X θ)]
  linarith [hlse, hmono2]

/-- The adaptive CE step majorizer with the weakened multiplier
`Real.exp R` (the statement): for every step size `η ∈ [0, 1]`,
the cross-entropy after the step is bounded by the current one minus
`η * A` plus `η ^ 2 *` the weakened adaptive curvature
`ceAdaptiveCurv`.  Corollary of the tight
`ceOneHot_next_le_adaptive_tight` via the coefficient bridge
`kappa R ≤ Real.exp R` (`kappa_le_expR`); the unit cap on `η` is
honest (see the tight twin). -/

theorem ceOneHot_next_le_adaptive (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η)
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - η * Hagi.Model.ceAlignment X θ t
        + η ^ 2 * ceAdaptiveCurv X θ t := by
  have h := ceOneHot_next_le_adaptive_tight X θ t hη0 hη1
  have hR : 0 ≤ Hagi.Model.ceStepRange X θ t :=
    Hagi.Model.ceStepRange_nonneg X θ t
  have hcurv : ceAdaptiveCurvTight X θ t ≤ ceAdaptiveCurv X θ t := by
    rcases eq_or_lt_of_le hR with hR0 | hR'
    · unfold ceAdaptiveCurvTight ceAdaptiveCurv kappa
      rw [← hR0]
      have hv : 0 ≤ varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
          (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v) :=
        varWeight_nonneg
          (fun v => Hagi.Energy.smax_nonneg (Hagi.Model.ceLogits X θ) v) _
      simp
      exact hv
    · unfold ceAdaptiveCurvTight ceAdaptiveCurv
      exact mul_le_mul_of_nonneg_right (kappa_le_expR hR')
        (varWeight_nonneg
          (fun v => Hagi.Energy.smax_nonneg (Hagi.Model.ceLogits X θ) v) _)
  nlinarith [sq_nonneg η, hcurv]


/-- The CE adaptive safe step: at positive adaptive curvature with
the safe step size within the unit cap, the cross-entropy drops by
at least `A ^ 2 / (4 * C)` with `C = ceAdaptiveCurv`. -/

theorem ce_adaptive_descent (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : 0 < ceAdaptiveCurv X θ t)
    (hA : 0 ≤ Hagi.Model.ceAlignment X θ t)
    (hstar : Hagi.Model.ceAlignment X θ t / (2 * ceAdaptiveCurv X θ t)
      ≤ 1) :
    Hagi.ceOneHot t
        (Hagi.Model.ceNextLogits X θ t
          (Hagi.Model.ceAlignment X θ t / (2 * ceAdaptiveCurv X θ t)))
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - Hagi.Model.ceAlignment X θ t ^ 2
          / (4 * ceAdaptiveCurv X θ t) :=
  adaptive_descent
    (fun η => Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η))
    (Hagi.Model.ceAlignment X θ t) (ceAdaptiveCurv X θ t)
    hA hC (fun _η h0 h1 => ceOneHot_next_le_adaptive X θ t h0 h1) hstar

/-- The tight CE adaptive safe step: at positive tight curvature with
the safe step size within the unit cap, the cross-entropy drops by at
least `A ^ 2 / (4 * C)` with `C = ceAdaptiveCurvTight`. -/

theorem ce_adaptive_descent_tight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : 0 < ceAdaptiveCurvTight X θ t)
    (hA : 0 ≤ Hagi.Model.ceAlignment X θ t)
    (hstar : Hagi.Model.ceAlignment X θ t / (2 * ceAdaptiveCurvTight X θ t)
      ≤ 1) :
    Hagi.ceOneHot t
        (Hagi.Model.ceNextLogits X θ t
          (Hagi.Model.ceAlignment X θ t / (2 * ceAdaptiveCurvTight X θ t)))
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - Hagi.Model.ceAlignment X θ t ^ 2
          / (4 * ceAdaptiveCurvTight X θ t) :=
  adaptive_descent
    (fun η => Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η))
    (Hagi.Model.ceAlignment X θ t) (ceAdaptiveCurvTight X θ t)
    hA hC (fun _η h0 h1 => ceOneHot_next_le_adaptive_tight X θ t h0 h1) hstar

/-! ## Dominance over the range bound -/

omit [Nonempty V] in

/-- Curvature dominance: if the directional variance under the soft
target is at most `R ^ 2 / (8 * Real.exp R)`, the adaptive curvature
is at most the Hoeffding curvature `R ^ 2 / 8` of `singleSampleStep`. -/

theorem ce_adaptive_curv_le_range (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * Real.exp (Hagi.Model.ceStepRange X θ t))) :
    ceAdaptiveCurv X θ t ≤ Hagi.Model.ceStepRange X θ t ^ 2 / 8 := by
  have hE : 0 < Real.exp (Hagi.Model.ceStepRange X θ t) :=
    Real.exp_pos _
  have h1 : Real.exp (Hagi.Model.ceStepRange X θ t)
      * varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
          (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ Real.exp (Hagi.Model.ceStepRange X θ t)
        * (Hagi.Model.ceStepRange X θ t ^ 2
          / (8 * Real.exp (Hagi.Model.ceStepRange X θ t))) :=
    mul_le_mul_of_nonneg_left hvar hE.le
  have h2 : Real.exp (Hagi.Model.ceStepRange X θ t)
      * (Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * Real.exp (Hagi.Model.ceStepRange X θ t)))
      = Hagi.Model.ceStepRange X θ t ^ 2 / 8 := by
    field_simp
  unfold ceAdaptiveCurv
  linarith

/-- **Drop dominance (the utility theorem)**: under the variance
threshold of `ce_adaptive_curv_le_range`, at positive alignment and
positive adaptive curvature, the adaptive certified drop
`A ^ 2 / (4 * C)` dominates the range certified drop
`universalDrop (singleSampleStep X t) θ = 2 * A ^ 2 / R ^ 2` of the
`singleSampleStep` instance.  Honest caveat: the hypothesis is a
REAL constraint — by Popoviciu the variance can reach `R ^ 2 / 4`,
above the threshold `R ^ 2 / (8 * Real.exp R)`, so for diffuse
targets and large ranges the range bound wins (see module pin). -/

theorem ce_adaptive_drop_dominates (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hR : Hagi.Model.ceStepRange X θ t ≠ 0)
    (_hA : 0 < Hagi.Model.ceAlignment X θ t)
    (hC : 0 < ceAdaptiveCurv X θ t)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * Real.exp (Hagi.Model.ceStepRange X θ t))) :
    Hagi.Theory.CEChain.universalDrop
        (Hagi.Theory.CEChain.singleSampleStep X t) θ
      ≤ Hagi.Model.ceAlignment X θ t ^ 2
          / (4 * ceAdaptiveCurv X θ t) := by
  have hcurv := ce_adaptive_curv_le_range X θ t hvar
  have hident := Hagi.Theory.CEChain.singleSample_drop_ident X θ t hR
  have hA2 : 0 ≤ Hagi.Model.ceAlignment X θ t ^ 2 := sq_nonneg _
  rw [hident]
  rw [div_le_div_iff₀ (by positivity :
      (0:ℝ) < Hagi.Model.ceStepRange X θ t ^ 2)
    (by positivity : (0:ℝ) < 4 * ceAdaptiveCurv X θ t)]
  nlinarith [hcurv, hA2]

omit [Nonempty V] in

/-- Tight curvature dominance: if the directional variance under the
soft target is at most `R ^ 2 / (8 * kappa R)`, the tight adaptive
curvature is at most the Hoeffding curvature `R ^ 2 / 8` — a WEAKER
variance threshold than `ce_adaptive_curv_le_range` (since
`kappa R ≤ e ^ R`, `kappa_le_expR`). -/

theorem ce_adaptive_curv_le_range_tight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * kappa (Hagi.Model.ceStepRange X θ t))) :
    ceAdaptiveCurvTight X θ t ≤ Hagi.Model.ceStepRange X θ t ^ 2 / 8 := by
  have hR : 0 ≤ Hagi.Model.ceStepRange X θ t :=
    Hagi.Model.ceStepRange_nonneg X θ t
  rcases eq_or_lt_of_le hR with hR0 | hR'
  · unfold ceAdaptiveCurvTight
    unfold kappa
    rw [← hR0]
    simp
  have hE : 0 < kappa (Hagi.Model.ceStepRange X θ t) := kappa_pos hR'
  have h1 : kappa (Hagi.Model.ceStepRange X θ t)
      * varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
          (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ kappa (Hagi.Model.ceStepRange X θ t)
        * (Hagi.Model.ceStepRange X θ t ^ 2
          / (8 * kappa (Hagi.Model.ceStepRange X θ t))) :=
    mul_le_mul_of_nonneg_left hvar hE.le
  have h2 : kappa (Hagi.Model.ceStepRange X θ t)
      * (Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * kappa (Hagi.Model.ceStepRange X θ t)))
      = Hagi.Model.ceStepRange X θ t ^ 2 / 8 := by
    field_simp
  unfold ceAdaptiveCurvTight
  linarith

/-- **Tight drop dominance**: under the (weaker) variance threshold of
`ce_adaptive_curv_le_range_tight`, the tight certified drop
`A ^ 2 / (4 * C)` dominates the range certified drop
`2 * A ^ 2 / R ^ 2` of `singleSampleStep`. -/

theorem ce_adaptive_drop_dominates_tight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hR : Hagi.Model.ceStepRange X θ t ≠ 0)
    (_hA : 0 < Hagi.Model.ceAlignment X θ t)
    (hC : 0 < ceAdaptiveCurvTight X θ t)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      ≤ Hagi.Model.ceStepRange X θ t ^ 2
        / (8 * kappa (Hagi.Model.ceStepRange X θ t))) :
    Hagi.Theory.CEChain.universalDrop
        (Hagi.Theory.CEChain.singleSampleStep X t) θ
      ≤ Hagi.Model.ceAlignment X θ t ^ 2
          / (4 * ceAdaptiveCurvTight X θ t) := by
  have hcurv := ce_adaptive_curv_le_range_tight X θ t hvar
  have hident := Hagi.Theory.CEChain.singleSample_drop_ident X θ t hR
  have hA2 : 0 ≤ Hagi.Model.ceAlignment X θ t ^ 2 := sq_nonneg _
  rw [hident]
  rw [div_le_div_iff₀ (by positivity :
      (0:ℝ) < Hagi.Model.ceStepRange X θ t ^ 2)
    (by positivity : (0:ℝ) < 4 * ceAdaptiveCurvTight X θ t)]
  nlinarith [hcurv, hA2]

/-! ## The concentrated-target limit -/

/-- **Zero variance kills the curvature**: if the directional logit
displacement has zero variance under the soft target (the
concentrated, one-hot-limit regime of THEORY_ALIGNMENT), the
majorizer is exactly linear for every `η ≤ 1` — the certified
descent has no curvature penalty at all. -/

theorem ceOneHot_next_le_linear_of_zero_var (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      = 0) :
    Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η)
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - η * Hagi.Model.ceAlignment X θ t := by
  have h := ceOneHot_next_le_adaptive X θ t hη0 hη1
  unfold ceAdaptiveCurv at h
  rw [hvar, mul_zero, mul_zero, add_zero] at h
  exact h

/-- **Zero variance kills the tight curvature** (tight twin of
`ceOneHot_next_le_linear_of_zero_var`). -/

theorem ceOneHot_next_le_linear_of_zero_var_tight (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hvar : varWeight (Hagi.Energy.smax (Hagi.Model.ceLogits X θ))
        (fun v => Hagi.Model.ceLogits X (Hagi.Model.ceDirection X θ t) v)
      = 0) :
    Hagi.ceOneHot t (Hagi.Model.ceNextLogits X θ t η)
      ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
        - η * Hagi.Model.ceAlignment X θ t := by
  have h := ceOneHot_next_le_adaptive_tight X θ t hη0 hη1
  unfold ceAdaptiveCurvTight at h
  rw [hvar, mul_zero, mul_zero, add_zero] at h
  exact h

end Hagi.Theory.AdaptiveMajorizer
