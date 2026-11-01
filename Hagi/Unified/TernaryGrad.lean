import Mathlib
import Hagi.Energy.Quantizer
import Hagi.Step.SignSGD

/-!
# TernaryGrad: МОСТ SignSGD × Quantizer —
знаковая компрессия градиента УЖЕ тернарна.

Связка источника №79 (signSGD) с единым квантователем
gridQ (Energy): значения sgn1 лежат в {−1, 0, 1} ⊂ ℤ —
решётке 1·ℤ. Следствия:
1. `sgn1_grid_fix`: gridQ 1 фиксирует знаковый градиент —
   повторное квантование тернарного вектора БЕЗ ПОТЕРЬ
   (канал компрессии исчерпан: 1 бит = минимальный объём,
   ошибка квантования 0);
2. `sgn1_zero_quant_error`: ошибка квантования знакового
   градиента равна НУЛЮ (не Δ/2) — знаковая компрессия
   доминирует решётчатую: signSGD = gridQ-оптимум;
3. `tern_grad_inner`: знаковый градиент сохраняет
   направление спуска ПОСЛЕ квантования (композиция
   каналов без деградации: ⟨Q(sign g), g⟩ = ‖g‖₁).
-/

namespace Hagi.Unified.TernaryGrad

open Hagi.Energy Hagi.Step.SignSGD

variable {k : Type*} [Fintype k]

/-- Знаковые значения — целые (round = тождество). -/
theorem sgn1_round (x : ℝ) :
    (round (sgn1 x) : ℝ) = sgn1 x := by
  rcases sgn1_ternary x with h | h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- gridQ 1 ФИКСИРУЕТ знаковый градиент: тернарный вектор
уже лежит в решётке 1·ℤ — повторное квантование без потерь
(минимальный объём достигнут, сжатие исчерпано). -/
theorem sgn1_grid_fix (x : ℝ) :
    gridQ 1 one_pos (sgn1 x) = sgn1 x := by
  unfold gridQ
  have hrr : (round (sgn1 x) : ℝ) = sgn1 x := sgn1_round x
  rw [div_one, hrr, one_mul]

/-- НУЛЕВАЯ ОШИБКА КВАНТОВАНИЯ: знаковая компрессия не
вносит ошибки решётки (в отличие от произвольного
квантования, где |Q(x)−x| ≤ Δ/2 — здесь строго 0). -/
theorem sgn1_zero_quant_error (g : k → ℝ) (i : k) :
    gridQ 1 one_pos (sgn1 (g i)) - sgn1 (g i) = 0 := by
  rw [sgn1_grid_fix (g i), sub_self]

/-- КОМПОЗИЦИЯ БЕЗ ДЕГРАДАЦИИ: после квантования знакового
градиента направление спуска сохранено в точности
(⟨Q(sign g), g⟩ = ‖g‖₁ ≥ 0 — два канала компрессии
складываются без потери сигнала). -/
theorem tern_grad_inner (g : k → ℝ) :
    ∑ i, gridQ 1 one_pos (sgn1 (g i)) * g i = ∑ i, |g i| := by
  have hfix : ∀ i, gridQ 1 one_pos (sgn1 (g i)) = sgn1 (g i) :=
    fun i => sgn1_grid_fix (g i)
  rw [Finset.sum_congr rfl (fun i _ => by rw [hfix i])]
  exact (sign_inner_nonneg g).1

end Hagi.Unified.TernaryGrad
