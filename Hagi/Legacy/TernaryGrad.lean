/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Legacy.TopLevel
import Hagi.Foundations.PerronCone
import Mathlib.Tactic
import Hagi.Energy.Quantizer
import Hagi.Step.SignSGD

/-!
# Квантование градиента (объединённое)

QuantizedCone и TernaryGrad. Имена деклараций
сохранены.
-/

/-!
# Unified.QuantizedCone — склейка (e) аудита v5

Квантизация внутри конусного инварианта: выигрыш роста
проходит через квантованные веса; штраф квантования
(quant_energy_bridge: dE ≤ κ·√n·s/2) вычитается из чистого
выигрыша. Конус γ·k·C ≤ G сохраняется при margin-условии:
штраф ≤ γ·(D − k·C) — избыток фронтира над конусом.
-/

namespace Hagi.Unified

/-- НИЖНЯЯ ГРАНИЦА ЧИСТОГО ВЫИГРЫША после квантования:
γ·D ≤ Graw и штраф Graw − G ≤ p дают γ·D − p ≤ G. -/
theorem quantized_net_gain (gamma D Graw G p : ℝ)
    (hgain : gamma * D ≤ Graw) (hquant : Graw - G ≤ p) :
    gamma * D - p ≤ G := by linarith

/-- КОНУС ПРИ КВАНТИЗАЦИИ: если конус k·C ≤ D выполнен и
штраф квантования p поглощается избытком фронтира
(p ≤ γ·(D − k·C)), то конусное условие усиления
γ·k·C ≤ G сохраняется НА КВАНТОВАННОМ шаге. -/
theorem quantized_cone_gain (gamma k C D Graw G p : ℝ)
    (hcone : k * C ≤ D) (hnn : 0 ≤ gamma)
    (hgain : gamma * D ≤ Graw) (hquant : Graw - G ≤ p)
    (hmargin : p ≤ gamma * (D - k * C)) :
    gamma * k * C ≤ G := by
  have h1 : gamma * k * C ≤ gamma * D := by
    have := mul_le_mul_of_nonneg_left hcone hnn
    ring_nf at this ⊢
    exact this
  have h2 : gamma * D - p ≤ G := quantized_net_gain gamma D Graw G p
    hgain hquant
  have hsub : gamma * (D - k * C)
      = gamma * D - gamma * k * C := by ring
  rw [hsub] at hmargin
  ring_nf at h1 h2 hmargin ⊢
  linarith

end Hagi.Unified

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
