import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Hagi.Learning.FOOF

set_option linter.style.header false

/-!
# RegCovPD — положительная определённость XXᵀ + λI (цикл 10)

Замыкает посылку обратимости FOOF: при λ > 0 регуляризованная
ковариация C = XXᵀ + λI строго положительно определена
(следовательно det C > 0 и C обратима) — без спектральной
теоремы, через прямое коши-подобное тождество:

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


/-- ЗАМЫКАНИЕ ПОСЫЛКИ FOOF: при λ > 0 матрица C = XXᵀ+λI
обратима (det > 0 по положительной определённости) —
предпосылка hinv в foof_normal_eq/foof_step_identity теперь
ТЕОРЕМА, а не гипотеза. -/
theorem regCov_det_unit [DecidableEq (Fin d)]
    (X : Matrix (Fin d) (Fin T) ℝ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (regCov X lam).det := by
  have hpos : 0 < (regCov X lam).det := (regCov_posDef X lam hlam).det_pos
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos)

end Hagi.Learning.RegCovPD
