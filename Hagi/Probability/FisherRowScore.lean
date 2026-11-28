/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# FisherRowScore — эмпирический Fisher-балл ошибки строки матрицы

HAWQ-V2 / cmix-neif-2.0 §4.3: цена ошибки квантования `e` строки слоя `y = W x`
— не `‖e‖²`, а средний квадрат `(e · x)²` по батчу: ошибка в направлении,
которое вход не возбуждает, бесплатна. PROPOSAL 29c сделал это для emb (строки =
классы, веса `p_i(1 − p_i)` — `ceShift`); здесь общая форма для любой матрицы.

* `rowFisherScore` — `(1/B)·Σ_b (e · x_b)²`, по battчу `X` строк-примеров;
* `rowFisherScore_nonneg` — неотрицателен;
* `rowFisherScore_diag` — при некоррелированных входах равен `Σ_j G_jj·e_j²`:
  взвешенная норма, веса — мощности входов;
* `rowFisherScore_eq_zero` — ошибка вдоль направления, которого батч не
  возбуждает (`X e = 0`), имеет нулевую цену.
-/

namespace Hagi.Probability.FisherRowScore

variable {B n : ℕ}

/-- Эмпирический Fisher-балл ошибки `e` по батчу `X` (строки — примеры). -/
noncomputable def rowFisherScore (X : Matrix (Fin B) (Fin n) ℝ) (e : Fin n → ℝ) : ℝ :=
  (∑ b, (∑ j, e j * X b j) ^ 2) / (B : ℝ)

theorem rowFisherScore_nonneg (X : Matrix (Fin B) (Fin n) ℝ) (e : Fin n → ℝ) :
    0 ≤ rowFisherScore X e := by
  unfold rowFisherScore; positivity

/-- Ошибка вдоль невыбуждаемого направления бесплатна. -/
theorem rowFisherScore_eq_zero (X : Matrix (Fin B) (Fin n) ℝ) (e : Fin n → ℝ)
    (h : ∀ b, ∑ j, e j * X b j = 0) : rowFisherScore X e = 0 := by
  unfold rowFisherScore; simp [h]

/-- Диагональная форма: если входы некоррелированы по батчу
(`Σ_b X b i X b j = 0` при `i ≠ j`), балл равен взвешенной норме ошибки
`Σ_j G_jj·e_j²`, `G_jj = Σ_b X b j² / B`. -/
theorem rowFisherScore_diag (X : Matrix (Fin B) (Fin n) ℝ) (e : Fin n → ℝ)
    (hunc : ∀ i j, i ≠ j → ∑ b, X b i * X b j = 0) :
    rowFisherScore X e = ∑ j, ((∑ b, X b j ^ 2) / (B : ℝ)) * e j ^ 2 := by
  by_cases hB : B = 0
  · subst hB; simp [rowFisherScore]
  · have expand : ∀ b, (∑ j, e j * X b j) ^ 2 = ∑ i, ∑ j, (e i * X b i) * (e j * X b j) := by
      intro b; rw [sq, Finset.sum_mul_sum]
    have key : ∑ b, (∑ j, e j * X b j) ^ 2 = ∑ i, ∑ j, e i * e j * (∑ b, X b i * X b j) := by
      rw [Finset.sum_congr rfl (fun b _ => expand b), Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    unfold rowFisherScore
    have hB' : (0:ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
    rw [key]
    have eR : ∑ j, (∑ b, X b j ^ 2) / (B:ℝ) * e j ^ 2 = (∑ j, (∑ b, X b j ^ 2) * e j ^ 2) / (B:ℝ) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
    rw [eR, Finset.sum_div, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    have hcol : ∑ j, e i * e j * (∑ b, X b i * X b j) = e i * e i * (∑ b, X b i * X b i) := by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hunc i j (Ne.symm hj)]; ring) (fun h => absurd (Finset.mem_univ i) h)]
    rw [hcol]
    have e2 : e i * e i * (∑ b, X b i * X b i) = (∑ b, X b i ^ 2) * e i ^ 2 := by
      rw [sq, mul_comm, Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
end Hagi.Probability.FisherRowScore
