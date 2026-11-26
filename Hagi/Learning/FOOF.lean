import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header false

/-!
# FOOF — Fast Online Objective Function: мост Mesa/FOOF

Mesa-слой (arXiv:2610.03858): точное решение регуляризованной
задачи наименьших квадратов по всей истории

  min_W  ½ Σ_τ ‖v_τ − W x_τ‖² + (λ/2)‖W‖²_F,   W : d×d

с входными столбцами X = [x_τ] (d×T) и выходными V = [v_τ] (d×T)
имеет аналитическое решение W* = V Xᵀ (X Xᵀ + λI)⁻¹ —
квазиньютоновский шаг: невязка умножается на обратную
регуляризованную ковариацию входов (отбеливание).

- `foof_normal_eq`: W* удовлетворяет нормальному уравнению
  W* (XXᵀ + λI) = V Xᵀ;
- `foof_step_identity`: W* = W₀ − (W₀X − V)Xᵀ C⁻¹ — оптимум
  получается из текущих весов ОДНИМ отбеленным шагом по невязке
  (второпорядковое прекондиционирование без итераций).

Не заявляем: онлайн-рекурренты.
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

/-- Нормальное уравнение: W* (XXᵀ + λI) = V Xᵀ. -/
theorem foof_normal_eq (V X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ)
    (hinv : IsUnit (regCov X lam).det) :
    foofW V X lam * regCov X lam = V * Xᵀ :=
  nonsing_inv_mul_cancel_right _ _ hinv

/-- FOOF-шаг: приращение к оптимуму из текущих
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

set_option linter.style.header false

/-!
# RegCovPD — положительная определённость XXᵀ + λI

При λ > 0 регуляризованная
ковариация C = XXᵀ + λI строго положительно определена
(следовательно det C > 0 и C обратима) через тождество:

  v ⬝ᵥ (C *ᵥ v) = ‖Xᵀ *ᵥ v‖² + λ·‖v‖² > 0  (v ≠ 0, λ > 0).
-/

open Finset Matrix Hagi.Learning.FOOF

namespace Hagi.Learning.RegCovPD

variable {d T : ℕ}

/-- Квадратичная форма ковариации: точное тождество. -/
theorem regCov_quad (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) (v : Fin d → ℝ) :
    dotProduct v ((regCov X lam) *ᵥ v)
      = (∑ i : Fin T, (∑ j : Fin d, X j i * v j) ^ 2)
        + lam * ∑ j, v j ^ 2 := by
  have h1 : dotProduct v ((X * Xᵀ) *ᵥ v)
      = ∑ t : Fin T, (∑ i : Fin d, X i t * v i) ^ 2 := by
    rw [dot_mulVec_eq_sum_sum (v := v) (A := X * Xᵀ) (w := v)]
    have hexpand : ∀ (i j : Fin d),
        (X * Xᵀ) i j = ∑ t : Fin T, X i t * X j t := by
      intro i j
      rfl
    simp only [hexpand, Finset.mul_sum, Finset.sum_mul]
    have hinner : ∀ (k : Fin d),
        ∑ (j : Fin d), ∑ (s : Fin T), v j * (X j s * X k s) * v k
          = ∑ (s : Fin T), ∑ (j : Fin d), v j * (X j s * X k s) * v k :=
      fun k => Finset.sum_comm
    have hswap : ∑ (k : Fin d), ∑ (j : Fin d), ∑ (s : Fin T),
        v j * (X j s * X k s) * v k
          = ∑ (s : Fin T), ∑ (k : Fin d), ∑ (j : Fin d),
              v j * (X j s * X k s) * v k := by
      rw [Finset.sum_congr rfl (fun k _ => hinner k), Finset.sum_comm]
    rw [hswap]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hpull : ∀ (k : Fin d), ∑ (j : Fin d), v j * (X j s * X k s) * v k
        = (∑ j : Fin d, v j * X j s) * (X k s * v k) := by
      intro k
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl (fun k _ => hpull k), ← Finset.mul_sum, sq]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : dotProduct v ((Matrix.diagonal fun _ => lam) *ᵥ v)
      = lam * ∑ j, v j ^ 2 := by
    have hmvec : (Matrix.diagonal fun _ => lam) *ᵥ v
        = fun j => lam * v j := by
      funext j
      have hsum : (∑ j_1 : Fin d, (if j = j_1 then lam else 0) * v j_1)
          = lam * v j := by simp
      show (∑ j_1 : Fin d, (if j = j_1 then lam else 0) * v j_1)
        = lam * v j
      exact hsum
    rw [hmvec, dotProduct]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      show v i * (lam * v i) = (v i * v i) * lam by ring),
      ← Finset.sum_mul, mul_comm, ← Finset.sum_congr rfl (fun j _ => (sq (v j)).symm)]
  unfold regCov
  rw [Matrix.add_mulVec, dotProduct_add, h1, h2]


/-! ### Строгая положительность и обратимость -/

/-- Квадратичная форма строго положительна при λ > 0 и v ≠ 0. -/
theorem regCov_quad_pos (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ)
    (hlam : 0 < lam) {v : Fin d → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v ((regCov X lam) *ᵥ v) := by
  rw [regCov_quad]
  have hsq : ∀ i : Fin T, (0:ℝ) ≤ (∑ j : Fin d, X j i * v j) ^ 2 :=
    fun i => sq_nonneg _
  have hv2 : 0 < ∑ j : Fin d, v j ^ 2 := by
    have hterm : ∀ j : Fin d, (0:ℝ) ≤ v j ^ 2 := fun j => sq_nonneg _
    obtain ⟨j, hj⟩ : ∃ j : Fin d, v j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (funext hcon)
    exact Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨j, Finset.mem_univ j, by positivity⟩
  have h1 : (0:ℝ) ≤ ∑ i : Fin T, (∑ j : Fin d, X j i * v j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc (0:ℝ) < 0 + lam * ∑ j : Fin d, v j ^ 2 := by
        rw [zero_add]; exact mul_pos hlam hv2
    _ ≤ ∑ i : Fin T, (∑ j : Fin d, X j i * v j) ^ 2
          + lam * ∑ j : Fin d, v j ^ 2 := by
          exact add_le_add_left h1 _

/-- Симметричность regCov. -/
theorem regCov_transpose (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) :
    (regCov X lam)ᵀ = regCov X lam := by
  unfold regCov
  rw [Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose]

/-- RegCov положительно определена при λ > 0. -/
theorem regCov_posDef [DecidableEq (Fin d)]
    (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) (hlam : 0 < lam) :
    (regCov X lam).PosDef :=
  Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨regCov_transpose X lam, fun v hv =>
      regCov_quad_pos X lam hlam hv⟩


/-- При λ > 0 матрица C = XXᵀ+λI обратима (det > 0 по
положительной определённости): предпосылка `hinv` в
`foof_normal_eq` и `foof_step_identity`. -/
theorem regCov_det_unit [DecidableEq (Fin d)]
    (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (regCov X lam).det := by
  have hpos : 0 < (regCov X lam).det := (regCov_posDef X lam hlam).det_pos
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos)

end Hagi.Learning.RegCovPD

set_option linter.style.header false

/-!
# FOOFUnique — единственность решения Mesa/FOOF

Если оба W₁ и W₂ удовлетворяют нормальному уравнению
W·(XXᵀ+λI) = VXᵀ и C = XXᵀ+λI обратима (`regCov_det_unit`
при λ>0), то W₁ = W₂: оптимум регуляризованной задачи
наименьших квадратов единственен.
-/

open Finset Matrix

namespace Hagi.Learning.FOOFUnique

open Hagi.Learning.FOOF Hagi.Learning.RegCovPD

variable {d T : ℕ}

/-- Единственность: нормальное уравнение имеет не более одного
решения при обратимой C. -/
theorem foof_normal_unique (V X : Matrix (Fin d) (Fin T) ℝ)
    (lam : ℝ) (hinv : IsUnit (regCov X lam).det)
    (W1 W2 : Matrix (Fin d) (Fin d) ℝ)
    (h1 : W1 * regCov X lam = V * Xᵀ)
    (h2 : W2 * regCov X lam = V * Xᵀ) :
    W1 = W2 := by
  have hdiff : (W1 - W2) * regCov X lam = 0 := by
    rw [Matrix.sub_mul, h1, h2, sub_self]
  have hcanc : W1 - W2 = 0 := by
    have hkey : W1 - W2
        = (W1 - W2) * regCov X lam * (regCov X lam)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv,
        Matrix.mul_one]
    rw [hdiff, zero_mul] at hkey
    exact hkey
  exact eq_of_sub_eq_zero hcanc

/-- `foofW` — единственное решение нормального уравнения при
обратимой C. -/
theorem foofW_unique (V X : Matrix (Fin d) (Fin T) ℝ)
    (lam : ℝ) (hinv : IsUnit (regCov X lam).det)
    (W : Matrix (Fin d) (Fin d) ℝ)
    (hW : W * regCov X lam = V * Xᵀ) :
    W = foofW V X lam :=
  (foof_normal_unique V X lam hinv W (foofW V X lam) hW
    (foof_normal_eq V X lam hinv))

end Hagi.Learning.FOOFUnique
