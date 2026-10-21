/-
GDN2: оператор обновления памяти Gated DeltaNet-2 (MemT-1.0,
arXiv:2610.26825) и границы его нормы.

Внешняя формализация (план MemT × HAGI, P0/P2): точная математика
обновления M̃' = (I − UᵀU)·D·M̃ + Uᵀ·(ω ⊙ V) с честной границей
нормы шага через подмультипликативную строчно-суммарную норму.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Hagi.Optimization.InexactContraction

open Finset Matrix
namespace Hagi.External.MemT
variable {d k v : Type*} [Fintype d] [Fintype k] [Fintype v]
  [DecidableEq d] [DecidableEq k] [DecidableEq v]

/-- Строчно-суммарная норма (операторная ℓ₁ по строкам) для
прямоугольных матриц. -/
noncomputable def rowSumNorm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem rowSumNorm_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ rowSumNorm A := by
  rw [rowSumNorm]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Подмультипликативность строчно-суммарной нормы. -/
theorem rowSumNorm_mul_le {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    rowSumNorm (A * B) ≤ rowSumNorm A * rowSumNorm B := by
  classical
  -- шаг 1: почленная граница через |ab| = |a||b| и треугольник
  have key : ∀ (i : m) (j : p),
      |(A * B) i j| ≤ ∑ l, |A i l| * |B l j| := by
    intro i j
    rw [Matrix.mul_apply]
    calc |∑ l, A i l * B l j|
        ≤ ∑ l, |A i l * B l j| := Finset.abs_sum_le_sum_abs _ Finset.univ
      _ = ∑ l, |A i l| * |B l j| := by
          congr 1 with l; rw [abs_mul]
  -- шаг 2: суммируем по j, тянем |A i l| наружу
  have hrow : ∀ (i : m), ∑ j, |(A * B) i j|
      ≤ (∑ l, |A i l|) * rowSumNorm B := by
    intro i
    calc ∑ j, |(A * B) i j|
        ≤ ∑ j, ∑ l, |A i l| * |B l j| :=
          Finset.sum_le_sum fun j _ => key i j
      _ = ∑ l, |A i l| * (∑ j, |B l j|) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      _ ≤ (∑ l, |A i l|) * rowSumNorm B := by
          have hle : ∀ (l : n), ∑ j, |B l j| ≤ rowSumNorm B := by
            intro l
            rw [rowSumNorm]
            have heq : ∑ j, |B l j| = ∑ l' ∈ ({l} : Finset n), ∑ j, |B l' j| := by
              rw [Finset.sum_singleton]
            rw [heq]
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (fun l' _ => Finset.mem_univ l') ?_
            intro l' _ _
            exact Finset.sum_nonneg fun j _ => abs_nonneg (B l' j)
          calc ∑ l, |A i l| * (∑ j, |B l j|)
              ≤ ∑ l, |A i l| * rowSumNorm B :=
                Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (abs_nonneg _)
            _ = (∑ l, |A i l|) * rowSumNorm B := (Finset.sum_mul _ _ _).symm
  -- шаг 3: суммируем по i
  calc rowSumNorm (A * B)
      = ∑ i, ∑ j, |(A * B) i j| := rfl
    _ ≤ ∑ i, (∑ l, |A i l|) * rowSumNorm B :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ l, |A i l|) * rowSumNorm B := (Finset.sum_mul _ _ _).symm
    _ = rowSumNorm A * rowSumNorm B := by
        rw [rowSumNorm, rowSumNorm]


/-- Субаддитивность строчно-суммарной нормы. -/
theorem rowSumNorm_add_le {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix m n ℝ) :
    rowSumNorm (A + B) ≤ rowSumNorm A + rowSumNorm B := by
  rw [rowSumNorm, rowSumNorm, rowSumNorm]
  have key : ∀ (i : m) (j : n), |A i j + B i j| ≤ |A i j| + |B i j| :=
    fun i j => (abs_add_le _ _)
  calc ∑ i, ∑ j, |(A + B) i j|
      ≤ ∑ i, ∑ j, (|A i j| + |B i j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          simp only [Matrix.add_apply]; exact key i j
    _ = (∑ i, ∑ j, |A i j|) + (∑ i, ∑ j, |B i j|) := by
          simp [Finset.sum_add_distrib]
/-! ### Оператор обновления Gated DeltaNet-2 (MemT-1.0) -/

/-- Шаг Gated DeltaNet-2 (MemT-1.0, arXiv:2610.26825):
M̃' = (I − Uᵀ·U)·D·M̃ + Uᵀ·(ω ⊙ V): проекционная ассимиляция
нового содержимого с затуханием старого. -/
noncomputable def gdn2Update (U : Matrix k d ℝ) (D : Matrix d d ℝ)
    (ω : k → ℝ) (V : Matrix k v ℝ) (M : Matrix d v ℝ) :
    Matrix d v ℝ :=
  ((1 : Matrix d d ℝ) - Uᵀ * U) * D * M + Uᵀ * (Matrix.diagonal ω * V)

omit [DecidableEq v] in
/-- Граница нормы одного шага GDN-2: норма памяти растёт не
быстрее, чем q·‖M‖ + b, где q — норма составного оператора
забывания-затухания (I−UᵀU)·D, b — норма вносимого сигнала. -/
theorem gdn2_step_bound (U : Matrix k d ℝ) (D : Matrix d d ℝ)
    (ω : k → ℝ) (V : Matrix k v ℝ) (M : Matrix d v ℝ) :
    rowSumNorm (gdn2Update U D ω V M)
      ≤ rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D
          * rowSumNorm M
        + rowSumNorm (Uᵀ * (Matrix.diagonal ω * V)) := by
  rw [gdn2Update]
  have h1 : rowSumNorm (((1 : Matrix d d ℝ) - Uᵀ * U) * D * M)
      ≤ rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D
          * rowSumNorm M :=
    le_trans (rowSumNorm_mul_le _ _)
      (mul_le_mul_of_nonneg_right (rowSumNorm_mul_le _ _)
        (rowSumNorm_nonneg _))
  have h2 := rowSumNorm_nonneg (Uᵀ * (Matrix.diagonal ω * V))
  calc rowSumNorm (((1 : Matrix d d ℝ) - Uᵀ * U) * D * M
        + Uᵀ * (Matrix.diagonal ω * V))
      ≤ rowSumNorm (((1 : Matrix d d ℝ) - Uᵀ * U) * D * M)
          + rowSumNorm (Uᵀ * (Matrix.diagonal ω * V)) :=
        rowSumNorm_add_le _ _
    _ ≤ rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D
          * rowSumNorm M
          + rowSumNorm (Uᵀ * (Matrix.diagonal ω * V)) :=
        add_le_add h1 (le_refl _)

/-- T-шаговая траектория памяти GDN-2 с фиксированными
параметрами записи (U, D, ω, V). -/
noncomputable def gdn2Iter (U : Matrix k d ℝ) (D : Matrix d d ℝ)
    (ω : k → ℝ) (V : Matrix k v ℝ) (M : Matrix d v ℝ) :
    ℕ → Matrix d v ℝ
  | 0 => M
  | t + 1 => gdn2Update U D ω V (gdn2Iter U D ω V M t)

omit [DecidableEq v] in
/-- Горизонтная граница памяти GDN-2: при коэффициенте
затухания q = ‖(I−UᵀU)·D‖ < 1 и неотрицательной норме
инжекции b норма T-шаговой памяти не превосывает
q^T·‖M₀‖ + b/(1−q) — рекуррентная память зажата
стационарным потолком неточного сжатия. -/
theorem gdn2_horizon (U : Matrix k d ℝ) (D : Matrix d d ℝ)
    (ω : k → ℝ) (V : Matrix k v ℝ) (M : Matrix d v ℝ)
    (hq0 : 0 < rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D)
    (hq1 : rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D < 1)
    (t : ℕ) :
    rowSumNorm (gdn2Iter U D ω V M t)
      ≤ (rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D) ^ t
          * rowSumNorm M
        + rowSumNorm (Uᵀ * (Matrix.diagonal ω * V))
          / (1 - rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D) := by
  have hstep : ∀ n : ℕ,
      rowSumNorm (gdn2Iter U D ω V M (n + 1))
        ≤ rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D
            * rowSumNorm (gdn2Iter U D ω V M n)
          + rowSumNorm (Uᵀ * (Matrix.diagonal ω * V)) := by
    intro n
    rw [gdn2Iter]
    exact gdn2_step_bound U D ω V _
  have h := Hagi.Optimization.inexact_contraction_floor
    (fun n => rowSumNorm (gdn2Iter U D ω V M n))
    (rowSumNorm ((1 : Matrix d d ℝ) - Uᵀ * U) * rowSumNorm D)
    (rowSumNorm (Uᵀ * (Matrix.diagonal ω * V)))
    hq0 hq1 (rowSumNorm_nonneg _) hstep t
  simpa [gdn2Iter] using h
