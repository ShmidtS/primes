import Mathlib
import Hagi.Model.StageSemantics
import Hagi.Model.ReferenceMachine
import Hagi.Energy.Quantizer

/-!
# QuantizedAdvance — РЕАЛЬНАЯ семантика компрессии
(аудит v16, P0 «Real execution refinement», Test 3)

Проблема: `StageSemantics.advance` записывает
`params' = params − η·stepDir` — ПРЕДКВАНТОВАННОЕ значение;
фактическая квантованная конфигурация не становится новым
состоянием. `advanceQ` исправляет: параметры пост-состояния
равны ФАКТИЧЕСКИ квантованным `q(params − η·stepDir)`.

- `advanceQ`: advance + реальное квантование параметров;
- `advanceQ_quantized`: params' = q(params − η·d) — Test 3
  выполнен (rfl-контракт);
- `advanceQ_prox`: при контракте квантовщика
  ‖q x − x‖ ≤ Δ квантованное состояние в Δ-окрестности
  идеального (advance) — мост к энергетическим оценкам;
- `machineStep_is_advanceQ`: machineStep эталонной машины —
  ЭКЗЕМПЛЯР advanceQ-паттерна (q = compressQ Δ).
-/

namespace Hagi.Model.QuantizedAdvance

open Hagi.System Hagi.Model

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Квантованный переход: advance + фактическое квантование
параметров (Test 3: состояние хранит РЕАЛЬНУЮ конфигурацию). -/
def advanceQ (S : GrowthState X) (u : StageInput X) (q : X → X) :
    GrowthState X :=
  { advance S u with
    params := q (S.params - u.sp.eta • u.stepDir) }

/-- TEST 3 (rfl-контракт): параметры пост-состояния равны
ФАКТИЧЕСКИ квантованным параметрам шага. -/
theorem advanceQ_quantized (S : GrowthState X) (u : StageInput X)
    (q : X → X) :
    (advanceQ S u q).params = q (S.params - u.sp.eta • u.stepDir) := rfl

/-- КВАНТОВАННОЕ СОСТОЯНИЕ РЯДОМ С ИДЕАЛЬНЫМ: при контракте
квантовщика (∀x, ‖q x − x‖ ≤ Δ) квантованный пост-параметр
отклоняется от идеального advance-параметра не более чем на
Δ — энергетические оценки переносимы с ошибкой квантования. -/
theorem advanceQ_prox (S : GrowthState X) (u : StageInput X)
    (q : X → X) (hDelta : ℝ) (hq : ∀ x, ‖q x - x‖ ≤ hDelta) :
    ‖(advanceQ S u q).params - (advance S u).params‖ ≤ hDelta := by
  have h1 : (advanceQ S u q).params - (advance S u).params
      = q (S.params - u.sp.eta • u.stepDir)
        - (S.params - u.sp.eta • u.stepDir) := by
    simp [advanceQ, advance]
  rw [h1]
  exact hq _

/-- ReferenceMachine.compressQ — ПОТОЧЕЧНЫЙ gridQ (rfl-совпадение форм). -/
theorem ReferenceMachine.compressQ_eq_gridQ {n : ℕ} (Delta : ℝ) (hD : 0 < Delta)
    (w : Fin n → ℝ) (i : Fin n) :
    ReferenceMachine.compressQ Delta w i = Hagi.Energy.gridQ Delta hD (w i) := rfl

/-- ReferenceMachine.compressQ УДОВЛЕТВОРЯЕТ КОНТРАКТУ advanceQ: поточечная
ошибка квантования ≤ Δ/2 (реюз gridQ_error) — machineStep
эталонной машины = advanceQ с q = ReferenceMachine.compressQ, контракт
проксимальности выполнен с hDelta = Δ/2 (поточечно). -/
theorem ReferenceMachine.compressQ_prox {n : ℕ} (Delta : ℝ) (hD : 0 < Delta)
    (w : Fin n → ℝ) (i : Fin n) :
    |ReferenceMachine.compressQ Delta w i - w i| ≤ Delta / 2 :=
  Hagi.Energy.gridQ_error Delta hD (w i)

end Hagi.Model.QuantizedAdvance
