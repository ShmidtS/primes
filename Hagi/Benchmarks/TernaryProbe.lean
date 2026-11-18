/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Pretraining.ProbeError
import Hagi.Runtime.TernaryExact

/-!
# TernaryProbe — saturation-aware cubic probes with bounded steps

The actual saturating quantizer `Runtime.qTern` has a global
pointwise error cap: half a grid level in range, or the signed
saturation overshoot out of range. For the selected cubic energy,
that cap yields a deterministic measurement budget and hence a
`probeCost` bound. Clipping the global optimizer to `(0, σmax]`
minimizes only this computed upper bound for fixed `level` and
`σmax`; it does not optimize arbitrary losses, the quantization
level, bit width, memory, or runtime floating-point behavior.
-/

namespace Hagi.Unified

open Real InnerProductSpace
open Hagi.Pretraining

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Global pointwise cap for the actual saturating ternary quantizer:
`level / 2` in range and `|value| - level` out of range. -/
noncomputable def ternaryRoundCap (level value : ℝ) : ℝ :=
  max (level / 2) (|value| - level)

/-- The actual `qTern` error is universally bounded by its computed
rounding/saturation cap; no in-range premise is required. -/
theorem ternaryRoundCap_abs_error_le (level value : ℝ) (hlevel : 0 < level) :
    |qTern level value - value| ≤ ternaryRoundCap level value := by
  rw [abs_sub_comm]
  unfold ternaryRoundCap
  by_cases hrange : ternInRange level value
  · exact (Hagi.Runtime.qTern_error_in level value hlevel hrange).trans
      (le_max_left _ _)
  · rw [Hagi.Runtime.qTern_error_out level value hlevel hrange]
    exact le_max_right _ _

/-- Computed measurement-error budget for a cubic endpoint shifted by
at most `σmax`. It includes both rounding and energy-dependent
saturation, rather than imposing an empirical error cap. -/
noncomputable def ternaryCubicStepBudget
    (c : ℝ) (a v x : X) (σmax level : ℝ) : ℝ :=
  level / 2 + (|c| / 6) * (|⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax) ^ 3

/-- A ternary-quantized shifted cubic endpoint has error at most the
computed step budget. Both signs of `t` are covered by `|t| ≤ σmax`. -/
theorem ternaryCubicShift_abs_error_le_stepBudget
    (c : ℝ) (a v x : X) (level σmax t : ℝ)
    (hlevel : 0 < level) (hmax : 0 < σmax) (ht : |t| ≤ σmax) :
    |qTern level (probeCubicEnergy c a v (x + t • v)) -
        probeCubicEnergy c a v (x + t • v)| ≤
      ternaryCubicStepBudget c a v x σmax level := by
  have hshift : x + t • v - a = (x - a) + t • v := by
    abel
  have henergy : probeCubicEnergy c a v (x + t • v) =
      (c / 6) * (⟪x - a, v⟫_ℝ + t * ‖v‖ ^ 2) ^ 3 := by
    simp only [probeCubicEnergy]
    rw [hshift, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have habs : |⟪x - a, v⟫_ℝ + t * ‖v‖ ^ 2| ≤
      |⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax := by
    calc
      |⟪x - a, v⟫_ℝ + t * ‖v‖ ^ 2| ≤
          |⟪x - a, v⟫_ℝ| + |t * ‖v‖ ^ 2| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le ⟪x - a, v⟫_ℝ (t * ‖v‖ ^ 2)
      _ = |⟪x - a, v⟫_ℝ| + |t| * ‖v‖ ^ 2 := by
        rw [abs_mul, abs_pow, abs_of_nonneg (norm_nonneg v)]
      _ ≤ |⟪x - a, v⟫_ℝ| + σmax * ‖v‖ ^ 2 :=
        add_le_add (le_refl _)
          (mul_le_mul ht (le_refl (‖v‖ ^ 2)) (sq_nonneg ‖v‖) hmax.le)
      _ = |⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax := by ring
  have henergyBound : |probeCubicEnergy c a v (x + t • v)| ≤
      (|c| / 6) * (|⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax) ^ 3 := by
    rw [henergy, abs_mul, abs_div, abs_pow]
    norm_num
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) habs 3)
      (by positivity)
  calc
    |qTern level (probeCubicEnergy c a v (x + t • v)) -
        probeCubicEnergy c a v (x + t • v)| ≤
      ternaryRoundCap level (probeCubicEnergy c a v (x + t • v)) :=
        ternaryRoundCap_abs_error_le _ _ hlevel
    _ ≤ level / 2 + |probeCubicEnergy c a v (x + t • v)| := by
      unfold ternaryRoundCap
      exact max_le (le_add_of_nonneg_right (abs_nonneg _))
        (by linarith [abs_nonneg (probeCubicEnergy c a v (x + t • v))])
    _ ≤ ternaryCubicStepBudget c a v x σmax level := by
      unfold ternaryCubicStepBudget
      exact add_le_add (le_refl _) henergyBound

/-- Central cubic probe after separately applying the actual
saturating ternary quantizer at both endpoints. Subtraction and
division remain exact operations on `ℝ`. -/
noncomputable def ternaryCentralCubicProbe
    (c : ℝ) (a v x : X) (σ level : ℝ) : ℝ :=
  (qTern level (probeCubicEnergy c a v (x + σ • v)) -
    qTern level (probeCubicEnergy c a v (x - σ • v))) / (2 * σ)

/-- Saturation-aware cost bound for the actual ternary central probe.
The two endpoint errors are the exact signed `qTern F - F` values and
are bounded using shifts `σ` and `-σ`. -/
theorem ternaryCentralCubicProbe_cost_bound
    (c : ℝ) (a v x : X) (σ σmax level : ℝ)
    (hlevel : 0 < level) (hmax : 0 < σmax) (hσ : 0 < σ)
    (hσmax : σ ≤ σmax) :
    |ternaryCentralCubicProbe c a v x σ level -
        ⟪probeCubicGrad c a v x, v⟫_ℝ| ≤
      probeCost ((|c| / 6) * ‖v‖ ^ 6)
        (ternaryCubicStepBudget c a v x σmax level) σ := by
  have hδ : 0 < ternaryCubicStepBudget c a v x σmax level := by
    unfold ternaryCubicStepBudget
    have hbase : 0 ≤ |⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax :=
      add_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) hmax.le)
    have hcube : 0 ≤ (|c| / 6) *
        (|⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax) ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hbase 3)
    linarith
  have hp : |qTern level (probeCubicEnergy c a v (x + σ • v)) -
      probeCubicEnergy c a v (x + σ • v)| ≤
      ternaryCubicStepBudget c a v x σmax level := by
    apply ternaryCubicShift_abs_error_le_stepBudget c a v x level σmax σ
      hlevel hmax
    rwa [abs_of_pos hσ]
  have hminus : x + (-σ) • v = x - σ • v := by
    rw [neg_smul, sub_eq_add_neg]
  have hm : |qTern level (probeCubicEnergy c a v (x - σ • v)) -
      probeCubicEnergy c a v (x - σ • v)| ≤
      ternaryCubicStepBudget c a v x σmax level := by
    have h := ternaryCubicShift_abs_error_le_stepBudget c a v x level σmax (-σ)
      hlevel hmax (by rw [abs_neg, abs_of_pos hσ]; exact hσmax)
    rwa [hminus] at h
  have heq : ternaryCentralCubicProbe c a v x σ level =
      noisyCentralCubicProbe c a v x σ
        (qTern level (probeCubicEnergy c a v (x + σ • v)) -
          probeCubicEnergy c a v (x + σ • v))
        (qTern level (probeCubicEnergy c a v (x - σ • v)) -
          probeCubicEnergy c a v (x - σ • v)) := by
    unfold ternaryCentralCubicProbe noisyCentralCubicProbe
    ring
  rw [heq]
  exact noisyCentralCubicProbe_cost_bound c a v x _ _ _ hδ.le hσ hp hm

/-- On the bounded positive region, the clipped root minimizes the
computed upper bound for fixed `level` and `σmax`. The comparison on
the right is `probeCost`, not the other step's actual error; this is
not a claim about arbitrary losses or full architecture/memory
optimization. -/
theorem ternaryCentralCubicProbe_optimal_bound
    (c : ℝ) (a v x : X) (σmax level σ : ℝ)
    (hc : c ≠ 0) (hv : v ≠ 0) (hlevel : 0 < level)
    (hmax : 0 < σmax) (hσ : 0 < σ) (hσmax : σ ≤ σmax) :
    |ternaryCentralCubicProbe c a v x
          (boundedProbeOptimalStep ((|c| / 6) * ‖v‖ ^ 6)
            (ternaryCubicStepBudget c a v x σmax level) σmax) level -
        ⟪probeCubicGrad c a v x, v⟫_ℝ| ≤
      probeCost ((|c| / 6) * ‖v‖ ^ 6)
        (ternaryCubicStepBudget c a v x σmax level) σ := by
  have hA : 0 < (|c| / 6) * ‖v‖ ^ 6 := by
    have hcabs : 0 < |c| := abs_pos.mpr hc
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hδ : 0 < ternaryCubicStepBudget c a v x σmax level := by
    unfold ternaryCubicStepBudget
    have hbase : 0 ≤ |⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax :=
      add_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg _) hmax.le)
    have hcube : 0 ≤ (|c| / 6) *
        (|⟪x - a, v⟫_ℝ| + ‖v‖ ^ 2 * σmax) ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hbase 3)
    linarith
  have hstar : 0 < boundedProbeOptimalStep ((|c| / 6) * ‖v‖ ^ 6)
      (ternaryCubicStepBudget c a v x σmax level) σmax :=
    boundedProbeOptimalStep_pos _ _ _ hA hδ hmax
  have hstarMax : boundedProbeOptimalStep ((|c| / 6) * ‖v‖ ^ 6)
      (ternaryCubicStepBudget c a v x σmax level) σmax ≤ σmax := by
    exact min_le_right _ _
  exact (ternaryCentralCubicProbe_cost_bound c a v x _ σmax level
    hlevel hmax hstar hstarMax).trans
      (probeCost_le_boundedOptimal _ _ σmax σ hA hδ hmax hσ hσmax)

end Hagi.Unified
