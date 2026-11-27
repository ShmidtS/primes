/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# GaugeBalance — некомпактные симметрии масштабирования и баланс норм

Portilheiro, Liebana, Orbanz, Saxe, «Renormalized Entropy from Symmetries:
Simplicity Bias and Neural Heat Death», arXiv:2611.27889v1. В сетях с
некомпактными симметриями масштабирования равновесие Ланжевена при малой
регуляризации уходит вдоль gauge-орбиты на бесконечность (гиперболы
|a| ~ ½ log(1/α)), раздувая динамический диапазон весов и ухудшая квантование;
баланс норм (Sec. 5) — точный выбор представителя орбиты с минимальной суммой
квадратов норм. В HAGI-Prime такие симметрии живут в каждом ранг-1 факторе:
LowRankAdapter B·A, BigramSkip B_u·B_v, MLA, и понейронно в SwiGLU
(W_up,:,j, W_down,j,:). Блоки роста стартуют в мёртвом множестве W_down = 0
(Theorem 2, neural heat death).

* `rank1_gauge` — `(c•B)·(c⁻¹•A) = B·A`: калибровка не меняет функцию;
* `balance_key` — `(cA)² + (B/c)² ≥ 2AB`, равенство при `cA = B/c`;
* `stock_balance_min` — минимум по калибровке равен `2|ab|`;
* `stock_balance_attained` — достигается при `c = sqrt(|b|/|a|)` (формула
  баланса Sec. 5);
* `dead_block_out_zero`, `dead_loss_const` — при W_down = 0 выход блока ноль
  и функция потерь по W_up постоянна: верхняя матрица заморожена, пока блок
  не выйдет из D (обоснование детерминированного шага при прогреве).
-/

namespace Hagi.Step.GaugeBalance
open Matrix
variable {m n h d : ℕ}

/-- Некомпактная масштабная симметрия ранг-`1` фактора (`LowRankAdapter B·A`,
`BigramSkip B_u·B_v`, `MLA`): `(c • B) * (c⁻¹ • A) = B * A` — калибровка не
меняет функцию. -/
theorem rank1_gauge (B : Matrix (Fin m) (Fin 1) ℝ) (A : Matrix (Fin 1) (Fin n) ℝ)
    (c : ℝ) (hc : c ≠ 0) : (c • B) * (c⁻¹ • A) = B * A := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul]
  rw [show c * B i 0 * (c⁻¹ * A 0 j) = (c * c⁻¹) * (B i 0 * A 0 j) by ring, mul_inv_cancel₀ hc, one_mul]
/-- Локальная лемма баланса в координатах `A, B ≥ 0`. -/
theorem balance_key (A B c : ℝ) (hc : 0 < c) :
    (c * A) ^ 2 + (B / c) ^ 2 ≥ 2 * A * B := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have key : (c * A) ^ 2 + (B / c) ^ 2 - 2 * A * B = (c * A - B / c) ^ 2 := by
    field_simp [hcne]; ring
  have h := sq_nonneg (c * A - B / c)
  have h' : (c * A - B / c) ^ 2 ≥ 0 := h
  rw [← key] at h'
  linarith
/-- Stock-balance (Sec. 5 arXiv:2611.27889): среди калибровок `(c·a, b/c)` сумма
квадратов норм минимальна при `c² = |b/a|`; минимум равен `2|a b|`. -/
theorem stock_balance_min (a b c : ℝ) (hc : 0 < c) :
    (c * a) ^ 2 + (b / c) ^ 2 ≥ 2 * |a * b| := by
  have h := balance_key |a| |b| c hc
  have ha2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have hca' : (c * a) ^ 2 = c ^ 2 * a ^ 2 := by ring
  rw [hca', ← ha2, div_pow, ← hb2, abs_mul,
    show c ^ 2 * |a| ^ 2 = (c * |a|) ^ 2 by ring, ← div_pow]
  simpa [mul_assoc] using h
/-- Точка баланса `c = sqrt(|b|/|a|)` достигает минимума `2|a b|` (при `a, b ≠ 0`). -/
theorem stock_balance_attained (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Real.sqrt (|b| / |a|) * a) ^ 2 + (b / Real.sqrt (|b| / |a|)) ^ 2 = 2 * |a * b| := by
  set c := Real.sqrt (|b| / |a|) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.2 (div_pos (abs_pos.2 hb) (abs_pos.2 ha))
  have hsq : c ^ 2 = |b| / |a| := Real.sq_sqrt (div_nonneg (abs_nonneg b) (abs_nonneg a))
  have hsq' : c ^ 2 * |a| = |b| := by rw [hsq]; field_simp [abs_ne_zero.2 ha]
  have ha2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
  have h1 : (c * a) ^ 2 = |a| * |b| := by
    have hca : (c * a) ^ 2 = c ^ 2 * a ^ 2 := by ring
    rw [hca, ← ha2]
    have : c ^ 2 * |a| ^ 2 = (c ^ 2 * |a|) * |a| := by ring
    rw [this, hsq', mul_comm]
  have h2 : (b / c) ^ 2 = |a| * |b| := by
    rw [div_pow, ← hb2]
    have hbb : |b| ^ 2 = (c ^ 2 * |a|) * |b| := by rw [hsq', sq]
    rw [hbb, mul_assoc]
    field_simp [ne_of_gt hcpos]
  rw [h1, h2, abs_mul]; ring
/-- Мёртвое множество `D` для блока роста: `W_down = 0` ⇒ выход блока — ноль. -/
theorem dead_block_out_zero (W_up : Matrix (Fin h) (Fin d) ℝ) (x : Fin d → ℝ) :
    (0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W_up x) = 0 := by
  simp
/-- Функция потерь по `W_up` при `W_down = 0` постоянна (не зависит от `W_up`):
градиент по верхней матрице нулевой — она заморожена, пока `W_down` не выйдет
из мёртвого множества. -/
theorem dead_loss_const (obj : (Fin d → ℝ) → ℝ) (W₁ W₂ : Matrix (Fin h) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    obj ((0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W₁ x))
      = obj ((0 : Matrix (Fin d) (Fin h) ℝ) *ᵥ (Matrix.mulVec W₂ x)) := by
  congr 1
  simp

end Hagi.Step.GaugeBalance
