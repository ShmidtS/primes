/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Learning.ContinualForgetting

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

`unified.py` (52be847): откатанный домен записывается в книгу с признаком
`rolled_back` и честным CE — CE установленной (откатанной) модели.

* `Entry` — запись: `ce`, `rolled_back`;
* `honestCE` — CE книги: откатан ⇒ установленная модель, принят ⇒ кандидат;
* `honestCE_rolled_back`, `honestCE_accepted`;
* `rolled_back_forget_zero` — откатанный домен не забывается (прирост CE 0).
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

/-- Запись домена в книге: CE и признак отката. -/
structure Entry where
  ce : ℝ
  rolled_back : Bool
/-- Честная запись CE (52be847): для откатанного домена пишется CE
установленной модели, для принятого — CE кандидата (модель и есть кандидат). -/
def honestCE (installed candidate : ℝ) (rolled_back : Bool) : ℝ :=
  if rolled_back then installed else candidate
/-- CE книги для откатанного домена — это CE установленной модели. -/
theorem honestCE_rolled_back (installed candidate : ℝ) :
    honestCE installed candidate true = installed := by simp [honestCE]
/-- CE книги для принятого домена — CE кандидата. -/
theorem honestCE_accepted (installed candidate : ℝ) :
    honestCE installed candidate false = candidate := by simp [honestCE]
/-- Откатанный домен не забывается моделью: прирост CE на нём равен нулю
относительно снимка (модель после отката = модель до приёма). -/
theorem rolled_back_forget_zero (pre installed : ℝ) (h : installed = pre)
    (post : Fin 1 → ℝ) (hpost : post 0 = installed) :
    Hagi.Learning.ContinualForgetting.forget (fun _ => pre) post 0 = 0 := by
  unfold Hagi.Learning.ContinualForgetting.forget
  rw [hpost, h]; ring

end Hagi.Unified.Rollback
