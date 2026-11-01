import Hagi.Unified.SignEFQuad

/-!
# Пошаговая оценка резидуала знакового EF

Первый кирпень ограниченности резидуала: остаток
сжатия (несланданное) за один шаг ограничен квадратом
удвоенной l-один нормы входа — без гипотез.
-/

namespace Hagi.Unified.EFResidual

open Hagi.Unified.SignEFQuad
open Hagi.Unified.SignStepCert
open Hagi.Unified.SignDescent
open Hagi.Unified.DescentCore
open Hagi.Step.SignSGD

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Знак принадлежит единичному сегменту. -/
theorem sgn1_abs_le_one (y : ℝ) : |sgn1 y| ≤ 1 := by
  unfold sgn1
  rcases lt_trichotomy y 0 with h | h | h
  · rw [if_pos h]
    norm_num
  · rw [if_neg (by linarith), if_pos h]
    norm_num
  · rw [if_neg (by linarith), if_neg (by linarith)]
    norm_num

/-- Покоординатная оценка остатка: модуль несollandанного
не превосходит модуль входа плюс масштаб. -/
theorem residual_coord_le (v : k → ℝ) (i : k) :
    |v i - signComp v i| ≤ |v i| + signScale v := by
  have hsnn : (0:ℝ) ≤ signScale v := by
    unfold signScale
    apply div_nonneg <;> positivity
  have hsplit : v i - signComp v i
      = v i + (-(signScale v * sgn1 (v i))) := by
    unfold signComp
    ring
  rw [hsplit]
  have hA := abs_add_le (v i)
    (-(signScale v * sgn1 (v i)))
  have h2 : |-(signScale v * sgn1 (v i))|
      ≤ signScale v := by
    rw [abs_neg, abs_mul, abs_of_nonneg hsnn]
    calc signScale v * |sgn1 (v i)|
        ≤ signScale v * 1 :=
      mul_le_mul_of_nonneg_left (sgn1_abs_le_one _) hsnn
      _ = signScale v := mul_one _
  have h1 : |v i| ≤ |v i| := le_refl _
  linarith

/-- l-один оценка остатка: сумма модулей несollandанного
не превосходит удвоенной l-один нормы входа. -/
theorem residual_l1_le (v : k → ℝ) :
    ∑ i, |v i - signComp v i| ≤ 2 * ∑ i, |v i| := by
  have hcard : (Fintype.card k : ℝ) ≠ 0 := by positivity
  have hsum : ∑ i, (|v i| + signScale v)
      = ∑ i, |v i| + (Fintype.card k : ℝ) * signScale v := by
    rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hscale : (Fintype.card k : ℝ) * signScale v
      = ∑ i, |v i| := by
    unfold signScale
    field_simp
  have hle : ∑ i, |v i - signComp v i|
      ≤ ∑ i, (|v i| + signScale v) :=
    Finset.sum_le_sum fun i _ => residual_coord_le v i
  rw [hsum, hscale] at hle
  linarith

/-- Квадраты ограничены квадратом суммы модулей. -/
theorem sumsq_le_sq_l1 (r : k → ℝ) :
    nrm2 r ≤ (∑ i, |r i|)^2 := by
  unfold nrm2
  have hdiag : ∀ i, (r i)^2 ≤ ∑ j, |r i| * |r j| := by
    intro i
    have hle : (r i)^2 = |r i| * |r i| := by
      rw [abs_mul_abs_self, pow_two]
    rw [hle]
    exact Finset.single_le_sum (f := fun j => |r i| * |r j|)
      (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hsumsq : ∑ i, (r i)^2 ≤ ∑ i, ∑ j, |r i| * |r j| :=
    Finset.sum_le_sum fun i _ => hdiag i
  have hprod : ∑ i, ∑ j, |r i| * |r j|
      = (∑ i, |r i|) * (∑ i, |r i|) := by
    rw [Finset.sum_mul_sum]
  linarith

/-- ГЛАВНАЯ: пошаговый остаток сжатия ограничен квадратом
удвоенной l-один нормы входа — без единой гипотезы. -/
theorem ef_residual_step_bound (v : k → ℝ) :
    nrm2 (v - signComp v) ≤ (2 * ∑ i, |v i|)^2 := by
  have h1 := sumsq_le_sq_l1 (fun i => v i - signComp v i)
  have h2 := residual_l1_le v
  show nrm2 (fun i => v i - signComp v i)
    ≤ (2 * ∑ i, |v i|)^2
  have hB : (0:ℝ) ≤ ∑ i, |v i - signComp v i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hC : (0:ℝ) ≤ 2 * ∑ i, |v i| := by positivity
  have hsq : (∑ i, |v i - signComp v i|)^2
      ≤ (2 * ∑ i, |v i|)^2 :=
    (sq_le_sq₀ hB hC).mpr h2
  exact le_trans h1 hsq

end Hagi.Unified.EFResidual
