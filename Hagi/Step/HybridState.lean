/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# HybridState — смещение устаревшего момента в тиражном оптимизаторе

Гибридный оптимизатор тиражирует состояние: плотные
координаты (градиенты каждый шаг) против редких/разреженных.

* `stale_momentum_bias`: слот момента, хранящий `g0` при
  текущем градиенте `gt`, разлагается как `gt + bias` с
  `‖bias‖ = ‖g0 − gt‖` в точности (одношаговая арифметика;
  многошаговая аккумуляция не доказана);
* `fresh_momentum_unbiased`: свежий слот (`slot = gt`)
  имеет нулевое смещение — граница тиража совпадает с
  границей свежести момента.
-/

namespace Hagi.Step

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Если `slot = g0`, то существует `bias` с
`slot = gt + bias` и `‖bias‖ = ‖g0 − gt‖` (смещение равно
дрейфу градиента; не усредняется по шагам — каждый устаревший
шаг его повторяет). -/
theorem stale_momentum_bias (g0 gt : V)
    (slot : V) (hslot : slot = g0) :
    ∃ bias : V, slot = gt + bias ∧ ‖bias‖ = ‖g0 - gt‖ := by
  refine ⟨g0 - gt, ?_, ?_⟩
  · rw [hslot]
    abel
  · rfl

/-- Если `slot = gt`, то существует `bias` с
`slot = gt + bias` и `‖bias‖ = 0`. -/
theorem fresh_momentum_unbiased (gt : V)
    (slot : V) (hslot : slot = gt) :
    ∃ bias : V, slot = gt + bias ∧ ‖bias‖ = 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [hslot]
    simp
  · exact norm_zero


end Hagi.Step

namespace Hagi
export Hagi.Step (stale_momentum_bias fresh_momentum_unbiased)
end Hagi
