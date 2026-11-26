/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# Rollback — откат приёма блока должен быть полным

`unified.py` (9baf5d6): откат приёма на месте обязан вернуть не только
параметры (`prm.copy_(inc)`), но и число блоков роста, заморозку и словари
обхода (`_restore_blocks`). До фикса «откат молча обнулял блок»: параметры
инкумбента при новых блоках — неконсистентное состояние.

* `GrowState` — параметры, блоки, заморозка, словари;
* `full` — точный откат (все четыре);
* `paramsOnly` — частичный откат (только параметры);
* `paramsOnly_ne_full` — если кандидат изменил блоки, заморозку или словари,
  частичный откат ≠ полному.
-/

namespace Hagi.Unified.Rollback

/-- Полное состояние роста: параметры `P`, число блоков `k`, маска заморозки
`F`, словари обхода `D`. Приём блока меняет все четыре. -/
structure GrowState (P K F D : Type) where
  params : P
  blocks : K
  frozen : F
  dicts : D
/-- Точный откат: все четыре компоненты возвращаются к снимку. -/
def full (snap : GrowState P K F D) (_cur : GrowState P K F D) : GrowState P K F D := snap
/-- Частичный откат: только параметры (как до 9baf5d6: блоки, заморозка и
словари оставались от принятого кандидата). -/
def paramsOnly (snap cur : GrowState P K F D) : GrowState P K F D :=
  { cur with params := snap.params }
/-- Частичный откат не равен полному, если кандидат изменил блоки, заморозку
или словари — состояние неконсистентно: новые блоки при старых параметрах. -/
theorem paramsOnly_ne_full (snap cur : GrowState P K F D)
    (h : cur.blocks ≠ snap.blocks ∨ cur.frozen ≠ snap.frozen ∨ cur.dicts ≠ snap.dicts) :
    paramsOnly snap cur ≠ full snap cur := by
  intro heq
  rcases h with h | h | h
  · exact h (by have := congrArg GrowState.blocks heq; simpa [paramsOnly, full] using this)
  · exact h (by have := congrArg GrowState.frozen heq; simpa [paramsOnly, full] using this)
  · exact h (by have := congrArg GrowState.dicts heq; simpa [paramsOnly, full] using this)

end Hagi.Unified.Rollback
