import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# FOOF — Fast Online Objective Function: мост Mesa/FOOF (цикл 9)

Mesa-слой (arXiv:2610.03858): точное решение регуляризованной
задачи наименьших квадратов по всей истории

  min_W  ½ Σ_τ ‖v_τ − W x_τ‖² + (λ/2)‖W‖²_F,   W : d×d

с входными столбцами X = [x_τ] (d×T) и выходными V = [v_τ] (d×T)
имеет аналитическое решение W* = V Xᵀ (X Xᵀ + λI)⁻¹ —
квазиньютоновский шаг: невязка умножается на обратную
регуляризованную ковариацию входов (отбеливание).

Доказано строго:
- `foof_normal_eq`: W* удовлетворяет нормальному уравнению
  W* (XXᵀ + λI) = V Xᵀ;
- `foof_step_identity`: W* = W₀ − (W₀X − V)Xᵀ C⁻¹ — оптимум
  получается из текущих весов ОДНИМ отбеленным шагом по невязке
  (второпорядковое прекондиционирование без итераций).

Не заявляем: положительную определённость C при λ>0
(спектральная теорема — отдельная работа), онлайн-рекурренты.
-/

open Finset Matrix

namespace Hagi.Learning.FOOF

variable {d T : ℕ}

/-- Регуляризованная ковариация входов: X Xᵀ + λI. -/
def regCov (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  X * Xᵀ + Matrix.diagonal fun _ => lam

/-- Аналитическое решение Mesa/FOOF:
W* = V Xᵀ (XXᵀ + λI)⁻¹. -/
noncomputable def foofW (V X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  V * Xᵀ * (regCov X lam)⁻¹

/-- НОРМАЛЬНОЕ УРАВНЕНИЕ: W* (XXᵀ + λI) = V Xᵀ. -/
theorem foof_normal_eq (V X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ)
    (hinv : IsUnit (regCov X lam).det) :
    foofW V X lam * regCov X lam = V * Xᵀ :=
  nonsing_inv_mul_cancel_right _ _ hinv

/-- FOOF-ШАГ (честная форма): приращение к оптимуму из текущих
весов — отбелённая невязка минус регуляризационный член:
W* − W₀ = (V − W₀X)XᵀC⁻¹ − λ·W₀C⁻¹, C = XXᵀ + λI.
При λ → 0 шаг — чистое second-order отбеливание невязки. -/
theorem foof_step_identity (W0 : Matrix (Fin d) (Fin d) ℝ)
    (V X : Matrix (Fin d) (Fin T) ℝ)
    (lam : ℝ) (hinv : IsUnit (regCov X lam).det) :
    foofW V X lam - W0
      = (V - W0 * X) * Xᵀ * (regCov X lam)⁻¹
        - lam • (W0 * (regCov X lam)⁻¹) := by
  have hdiag : W0 * Matrix.diagonal (fun _ => lam) = lam • W0 := by
    show W0 * Matrix.diagonal (fun _ => lam)
      = Matrix.of fun i j => lam * W0 i j
    ext i j
    simp only [Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply,
      Matrix.one_apply, mul_ite, mul_zero, mul_one, Matrix.smul_apply,
      smul_eq_mul]
    by_cases h : i = j <;> simp [h, mul_comm]
  have key : W0 * regCov X lam = W0 * (X * Xᵀ) + lam • W0 := by
    unfold regCov
    rw [Matrix.mul_add, hdiag]
  unfold foofW
  have hW : W0 * regCov X lam * (regCov X lam)⁻¹ = W0 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv,
      Matrix.mul_one]
  -- RHS: (V Xᵀ − W₀XXᵀ)C⁻¹ − λW₀C⁻¹ = VXᵀC⁻¹ − (W₀XXᵀC⁻¹ + λW₀C⁻¹)
  -- W₀ = W₀CC⁻¹ = (W₀XXᵀ + λW₀)C⁻¹ = W₀XXᵀC⁻¹ + λW₀C⁻¹
  have hsplit : W0 * (X * Xᵀ) * (regCov X lam)⁻¹
      + lam • (W0 * (regCov X lam)⁻¹) = W0 := by
    have h1 : W0 * (X * Xᵀ) * (regCov X lam)⁻¹
        + lam • (W0 * (regCov X lam)⁻¹)
        = (W0 * (X * Xᵀ) + lam • W0) * (regCov X lam)⁻¹ := by
      rw [Matrix.add_mul, smul_mul_assoc]
    rw [h1, ← key, hW]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc W0 X Xᵀ]
  nth_rewrite 1 [← hsplit]
  abel

end Hagi.Learning.FOOF
