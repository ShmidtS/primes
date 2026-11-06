/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Pretraining.Dust
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic

/-!
# An exact finite Rademacher noise carrier

`Dust` supplies the sign and finite Boolean cube. This module gives the
cube the actual fair Bernoulli product measure from Mathlib, then proves
the fixed-minibatch SafeQP noise premises for `signR (ω j) • u_i`.
The independence is only across `j`, for each fixed expert and direction;
it is not asserted across experts or time. Unit vectors give `σ = 1`.
-/

namespace Hagi.Pretraining

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal

/-- The fair Bernoulli measure on the two Boolean outcomes. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    ⟨1 / 2, by norm_num [unitInterval]⟩

/-- The independent fair Bernoulli product on `HC m`. -/
noncomputable def rademacherLaw (m : ℕ) : Measure (HC m) :=
  Measure.pi (fun _ : Fin m => fairBoolMeasure)

private instance fairBoolMeasure_isProbabilityMeasure :
    IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

instance rademacherLaw_isProbabilityMeasure (m : ℕ) :
    IsProbabilityMeasure (rademacherLaw m) := by
  unfold rademacherLaw
  infer_instance

/-- Coordinate noise for an expert with vector `u i`. -/
def rademacherNoise {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (i : K)
    (j : Fin m) (ω : HC m) : X :=
  signR (ω j) • u i

private lemma signR_measurable : Measurable signR := by
  unfold signR
  fun_prop

/-- The projection is measurable for every fixed direction. This uses
only real-valued scalar multiplication, so no measurable-space structure
on the otherwise arbitrary inner-product carrier is needed. -/
theorem rademacher_projection_measurable {K X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (u : K → X) (d : X) (i : K) (j : Fin m) :
    Measurable (fun ω => ⟪rademacherNoise u i j ω, d⟫_ℝ) := by
  have h : Measurable (fun ω : HC m =>
      signR (ω j) * ⟪u i, d⟫_ℝ) :=
    (signR_measurable.comp (measurable_pi_apply j)).mul_const _
  simpa only [rademacherNoise, real_inner_smul_left] using h

/-- Each fair sign has exact zero expectation. -/
theorem rademacher_expect_sign (j : Fin m) :
    ∫ ω : HC m, signR (ω j) ∂rademacherLaw m = 0 := by
  calc
    ∫ ω : HC m, signR (ω j) ∂rademacherLaw m
        = ∫ b : Bool, signR b ∂fairBoolMeasure := by
          unfold rademacherLaw
          exact MeasureTheory.integral_comp_eval
            signR_measurable.aestronglyMeasurable
    _ = 0 := by
      rw [fairBoolMeasure, ProbabilityTheory.integral_bernoulliMeasure]
      norm_num [signR]

/-- Projection has exact zero mean for every expert and direction. -/
theorem rademacher_projection_mean {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (d : X) (i : K) (j : Fin m) :
    ∫ ω, ⟪rademacherNoise u i j ω, d⟫_ℝ ∂rademacherLaw m = 0 := by
  simp only [rademacherNoise, real_inner_smul_left]
  rw [integral_mul_const, rademacher_expect_sign j, zero_mul]

/-- The coordinate projections are independent across `j`; this uses
exactly the fixed-`i`, fixed-direction form of the SafeQP premises. -/
theorem rademacher_projection_independent {K X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (u : K → X) (d : X) (i : K) :
    iIndepFun (fun j : Fin m =>
      fun ω => ⟪rademacherNoise u i j ω, d⟫_ℝ) (rademacherLaw m) := by
  have hbase : iIndepFun (fun j : Fin m => fun ω : HC m => ω j)
      (rademacherLaw m) := by
    unfold rademacherLaw
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin m => fairBoolMeasure)
      (X := fun _ : Fin m => fun b : Bool => b)
      (fun _ => measurable_id.aemeasurable)
  have hcomp := hbase.comp
    (fun _ b => signR b * ⟪u i, d⟫_ℝ)
    (fun _ => signR_measurable.mul_const _)
  simpa only [Function.comp_def, rademacherNoise, real_inner_smul_left]
    using hcomp

/-- Unit directions give the exact noise bound `σ = 1`. -/
theorem rademacherNoise_norm_le_one {K X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (u : K → X) (hu : ∀ i, ‖u i‖ = 1)
    (i : K) (j : Fin m) (ω : HC m) :
    ‖rademacherNoise u i j ω‖ ≤ 1 := by
  cases h : ω j <;> simp [rademacherNoise, h, signR, hu]

end Hagi.Pretraining
