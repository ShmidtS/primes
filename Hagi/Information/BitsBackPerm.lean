/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# BitsBackPerm — bits-back на порядке взаимозаменяемых нейронов

cmix-neif-2.0 (Wölk, Hutter Prize 2026, README 4.3): порядок взаимозаменяемых
групп нейронов кодируется выбором их перестановки (Lehmer code) —
log₂(n!) бит возвращаются декодеру (Hinton–van Camp 1993). Формально: если
объект инвариантен к перестановкам группы из `n` элементов, то все `n!`
перестановок — один объект; кодирование номера перестановки переносит
log₂(n!) бит полезной нагрузки бесплатно. Граница: n! ≥ (n/2)^(n/2) для
чётного `n`, т.е. ≥ (n/2)·log₂(n/2) бит.
-/

namespace Hagi.Information.BitsBackPerm

/-- Инвариантность к перестановке: сумма по индексам не зависит от порядка. -/
theorem sum_perm_inv {ι : Type} [Fintype ι] (f : ι → ℝ) (σ : ι ≃ ι) :
    ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f

/-- Число перестановок `n` элементов — `n!`. -/
theorem card_perm (n : ℕ) : Fintype.card (Fin n ≃ Fin n) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]
-- (lower bound needs n ≥ 2 for the logarithm; see bits_back)

/-- Нижняя граница: `n! ≥ (n/2)^(n/2)` — из `(n/2)!·(n/2)^(n − n/2) ≤ n!`
и `(n/2)! ≥ 1`. Даёт не менее `(n/2)·log₂(n/2)` возвращённых бит. -/
theorem factorial_lower (n : ℕ) (hn : 2 ≤ n) : (n / 2) ^ (n / 2 : ℕ) ≤ n.factorial := by
  have h := Nat.factorial_mul_pow_sub_le_factorial (n := n / 2) (m := n) (Nat.div_le_self n 2)
  have hf : 1 ≤ (n / 2).factorial := Nat.succ_le_iff.mpr (Nat.factorial_pos _)
  calc (n / 2) ^ (n / 2 : ℕ) ≤ (n / 2) ^ (n - n / 2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (n / 2).factorial * (n / 2) ^ (n - n / 2) := le_mul_of_one_le_left (Nat.zero_le _) hf
    _ ≤ n.factorial := h

/-- Возвращённые биты: `log₂(n!) ≥ (n/2)·log₂(n/2)` для `n ≥ 2`. -/
theorem bits_back (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n.factorial : ℝ) / Real.log 2 ≥ ((n / 2 : ℕ) : ℝ) * (Real.log ((n / 2 : ℕ) : ℝ) / Real.log 2) := by
  have hcast : (((n / 2) ^ (n / 2 : ℕ) : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ) := by exact_mod_cast (by push_cast; rfl)
  have hlo : ((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ) ≤ (n.factorial : ℝ) := by rw [← hcast]; exact_mod_cast factorial_lower n hn
  have hnn : 0 < n / 2 := by omega
  have hpos : (0:ℝ) < ((n / 2 : ℕ) : ℝ) ^ (n / 2 : ℕ) := pow_pos (by exact_mod_cast hnn) _
  have h := Real.log_le_log hpos hlo
  rw [Real.log_pow] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [ge_iff_le, mul_div_assoc', div_le_div_iff₀ hlog hlog]
  exact mul_le_mul_of_nonneg_right h hlog.le
/-- Скрытые нейроны взаимозаменяемы: одновременная перестановка столбцов `W_down`
и строк `W_up` матрицей перестановки `P` не меняет произведение `W_down·W_up`
(`Pᵀ·P = 1`). Поэтому порядок `n` нейронов скрытого слоя не несёт информации —
его можно кодировать bits-back (выше): `log₂(n!)` бит на блок роста. -/
theorem hidden_neurons_permutable {m n k : ℕ} (Wd : Matrix (Fin m) (Fin n) ℝ)
    (Wu : Matrix (Fin n) (Fin k) ℝ) (σ : Equiv.Perm (Fin n)) :
    (Wd * σ.permMatrix ℝ) * ((σ.permMatrix ℝ).transpose * Wu) = Wd * Wu := by
  have h1 : (σ.permMatrix ℝ).transpose * σ.permMatrix ℝ = 1 := by
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have h2 : σ.permMatrix ℝ * (σ.permMatrix ℝ).transpose = 1 := by
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  calc (Wd * σ.permMatrix ℝ) * ((σ.permMatrix ℝ).transpose * Wu)
      = Wd * (σ.permMatrix ℝ * ((σ.permMatrix ℝ).transpose * Wu)) := by rw [Matrix.mul_assoc]
    _ = Wd * ((σ.permMatrix ℝ * (σ.permMatrix ℝ).transpose) * Wu) := by rw [Matrix.mul_assoc]
    _ = Wd * Wu := by rw [h2, Matrix.one_mul]
end Hagi.Information.BitsBackPerm
