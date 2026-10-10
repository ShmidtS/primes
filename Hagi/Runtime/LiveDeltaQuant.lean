/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LiveDelta
import Hagi.Runtime.TernaryExact

set_option linter.style.header false

/-!
# Квантизация свёрнутых живых весов

Сертификат для фазы упаковки LiveDelta: когда принятые
низкоранговые блоки сворачиваются в базу и база
перквантизуется на троичной сетке, по-элементная ошибка
ограничена s/2 (для в-диапазоне элементов, qTern_error_in),
а суммарная квадратичная ошибка — n·m·(s/2)².

Вне-диапазонные (сатурированные) элементы исключены
гипотезой; их хвост учитывается отдельным насыщением
(satTail в Runtime.TernaryExact). Ничего о качестве модели
не утверждается — только арифметика квантизации.
-/

open Finset Real Matrix

namespace Hagi.LiveDeltaQuant

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]

/-- Поточечная тернарная квантизация матрицы на сетке шага s. -/
noncomputable def quantMat (s : ℝ) (M : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Matrix.of fun i j => qTern s (M i j)

/-- Поточечная гарантия: в-диапазоне элементы матрицы
квантизуются с ошибкой ≤ s/2 (qTern_error_in). -/
theorem quantMat_entry (s : ℝ) (hs : 0 < s) (M : Matrix m n ℝ)
    (i : m) (j : n) (hin : ternInRange s (M i j)) :
    |M i j - quantMat s M i j| ≤ s / 2 :=
  qTern_error_in s (M i j) hs hin

/-- Суммарная квадратичная ошибка квантизации в-диапазонной
матрицы: ∑_{i,j} |M_ij − Q_ij|² ≤ (m·n)·(s/2)². -/
theorem quantMat_sq_bound (s : ℝ) (hs : 0 < s) (M : Matrix m n ℝ)
    (hin : ∀ i j, ternInRange s (M i j)) :
    ∑ i, ∑ j, (M i j - quantMat s M i j) ^ 2
      ≤ (Fintype.card m * Fintype.card n) * (s / 2) ^ 2 := by
  have hle : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      (M i j - quantMat s M i j) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i _ j _
    have h := quantMat_entry s hs M i j (hin i j)
    have e2 : (M i j - quantMat s M i j) ^ 2
        = |M i j - quantMat s M i j| ^ 2 := (sq_abs _).symm
    rw [e2, pow_two, pow_two]
    have hs2 : 0 ≤ s / 2 := by positivity
    exact mul_le_mul h h (abs_nonneg _) hs2
  calc ∑ i, ∑ j, (M i j - quantMat s M i j) ^ 2
      ≤ ∑ i, ∑ j ∈ Finset.univ, (s / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hle i (Finset.mem_univ i) j (Finset.mem_univ j)
    _ = (Fintype.card m * Fintype.card n) * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ,
          Finset.sum_const, Finset.card_univ]
        ring

end Hagi.LiveDeltaQuant
