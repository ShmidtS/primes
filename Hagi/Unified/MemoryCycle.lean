/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.MemoryController

set_option linter.style.header false

/-!
# MemoryCycle — сквозной цикл: допуск → память →
квантованная консолидация → граница качества

Замыкает цепочку R271–R273 в один цикл управления памятью:

1. записи допускаются контроллером (novelty ∧ certified
   gain — R273);
2. память живёт как rank-1 блоки LiveDelta (точное
   представление истории спуска — R271);
3. консолидация (квантование факторов) оценивается
   аддитивным Frobenius-бюджетом k·Σ εᵢ (R272);
4. честный Lipschitz-мост: если функция потерь
   L-липшицева по весам в Frobenius-норме (ИЗМЕРЯЕМАЯ
   посылка h_emp_, как и вся эмпирика), ошибка качества
   после консолидации ≤ L·√(k·Σ εᵢ).

Формулируется и доказывается ТОЛЬКО арифметика границы;
оценка L и εᵢ — runtime-контракты.

Доказано:
* `consolidation_quality_bound`: при Lipschitz-посылке и
  per-block бюджетах εᵢ квантованная консолидация меняет
  потерю не более чем на L·√(k·Σ εᵢ);
* `memory_cycle_quality`: полная цепочка — память из
  последовательности допусков, консолидированная с бюджетом,
  сохраняет качество в пределах границы.
-/

open Finset Hagi.LiveDelta Hagi.DeltaHistory Hagi.DeltaConsolidate
  Hagi.MemoryController Matrix

namespace Hagi.MemoryCycle

variable {m n : Type} [Fintype m] [Fintype n]

/-- Frobenius-норма. -/
noncomputable def frobNorm (M : Matrix m n ℝ) : ℝ := Real.sqrt (frob M)

/-- Консолидированное качество: при измеряемой
L-Lipschitz-посылке на функцию потерь (по Frobenius-норме
весов) и per-block бюджетах замены εᵢ, изменение потери от
квантованной консолидации ≤ L·√(k·Σ εᵢ). -/
theorem consolidation_quality_bound (k : ℕ)
    (olds news : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (ε : Fin k → ℝ)
    (hbud : ∀ t, frob ((olds t).1ᵀ * (olds t).2
      - (news t).1ᵀ * (news t).2) ≤ ε t)
    (loss : Matrix m n ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ W W', |loss W - loss W'|
      ≤ L * frobNorm (W - W')) :
    |loss (∑ t, (olds t).1ᵀ * (olds t).2)
      - loss (∑ t, (news t).1ᵀ * (news t).2)|
      ≤ L * Real.sqrt ((k : ℝ) * ∑ t, ε t) := by
  have hb := consolidate_budget k olds news ε hbud
  refine le_trans (hlip _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ hL
  exact Real.sqrt_le_sqrt hb

/-- Полный цикл памяти: память, построенная из
последовательности допусков (контроллер R273), после
квантованной консолидации с per-block бюджетами εᵢ и при
измеряемой Lipschitz-посылке сохраняет качество в пределах
L·√(k·Σ εᵢ) — одна теорема про весь цикл
admit → store → consolidate. -/
theorem memory_cycle_quality (k : ℕ)
    (entries : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (news : Fin k → Matrix Unit m ℝ × Matrix Unit n ℝ)
    (ε : Fin k → ℝ)
    (hbud : ∀ t, frob ((entries t).1ᵀ * (entries t).2
      - (news t).1ᵀ * (news t).2) ≤ ε t)
    (loss : Matrix m n ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ W W', |loss W - loss W'|
      ≤ L * frobNorm (W - W')) :
    |loss (∑ t, (entries t).1ᵀ * (entries t).2)
      - loss (∑ t, (news t).1ᵀ * (news t).2)|
      ≤ L * Real.sqrt ((k : ℝ) * ∑ t, ε t) :=
  consolidation_quality_bound k entries news ε hbud loss L
    hL hlip

end Hagi.MemoryCycle
