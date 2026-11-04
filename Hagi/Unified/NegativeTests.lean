import Hagi.Unified.NCStepCert
import Hagi.Unified.CertifiedLoop
import Hagi.Unified.MemorySemantics
import Hagi.Unified.HonestTransition
import Hagi.Unified.LinkedQVec


/-!
# NegativeTests — типовые негативные тесты сертификатов (Gate 1)

Каждая теорема — формальное свидетельство НЕВОЗМОЖНОСТИ фиктивного
сертификата: только проекции и арифметика существующих контрактов,
без новых определений.
-/

namespace Hagi.Unified.NegativeTests

open Hagi.Unified.NCStepCert Hagi.Unified.CertifiedLoop
open Hagi.Unified.MemorySemantics Hagi.Unified.HonestTransition
open Hagi.Model.NeuralComputer Hagi.Unified.LinkedQVec

/-! ### N1. Спуск сертификата фиксирован исполнением -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §3.1): certificated drop нейрокомпьютера
РАВЕН u.gain по построению — доказательство rfl, значение иного спуска
не существует в типе. Искусственный `d` (старый дефект) более не
типизируется: параметр удалён из ncCertStep/ncStepCert. -/
theorem nc_drop_cannot_be_assigned
    (S : NCState) (u : NCInput) (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (hd : 0 < u.gain)
    (hriskLim : u.cost + u.riskSpend ≤ riskLim)
    (hfloor : ∀ i, floor i ≤ S.capability)
    (hgain : 0 ≤ u.gain)
    (hbud : 0 ≤ S.budget)
    (hcost_le : u.cost ≤ S.budget) :
    (ncStepCert S u floor riskLim hd hriskLim hfloor hgain hbud
      hcost_le).trans.objectiveDrop = u.gain := rfl

/-- НЕГАТИВНЫЙ ТЕСТ: энергия сертифицированного пост-состояния —
именно энергия канонического перехода (совпадение с реальным
исполнением, не независимая величина). -/
theorem nc_energy_matches_execution (S : NCState) (u : NCInput) :
    (ncCertStep S u).energy = (ncAdvance S u).energy := rfl

/-! ### N2. Перерасход бюджета невозможен -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §11.2-2): из StepCert следует, что
бюджетная трата шага не превосходит доступный бюджет (совместно
hdec : b' ≤ bt − budgetSpend и 0 ≤ b'). -/
theorem budget_overrun_impossible {S : Type*}
    (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (s s' : S) (bt b' : ℝ)
    (c : StepCert obj M floor riskLim s s' bt b') :
    c.budgetSpend ≤ bt := by
  have h1 := c.hdec
  have h2 := c.trans.budgetBound
  linarith

/-! ### N3. Превышение risk limit невозможно -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §11.2-3): риск-трата любого
сертифицированного шага ≤ riskLim. -/
theorem risk_limit_respected {S : Type*}
    (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (s s' : S) (bt b' : ℝ)
    (c : StepCert obj M floor riskLim s s' bt b') :
    c.riskSpend ≤ riskLim := c.trans.riskBound

/-! ### N4. Ухудшение защищённого канала качества невозможно -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §11.2-4): каждый покомпонентный канал
качества сертифицированного пост-состояния ≥ floor. -/
theorem quality_floor_holds {S : Type*}
    (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (s s' : S) (bt b' : ℝ)
    (c : StepCert obj M floor riskLim s s' bt b')
    (i : Fin 5) : floor i ≤ M.evaluate s' i := c.quality i

/-! ### N5. Чужой адрес памяти неизменен -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §11.2-5): сертификат записи не может
изменить посторонний адрес — post j = pre j для j ≠ address
(pre/address/value — параметры сертификата). -/
theorem ram_foreign_address_unchanged {m n : ℕ}
    {pre : Matrix (Fin m) (Fin n) ℝ} {i : Fin m} {v : Fin n → ℝ}
    (w : RamWriteCert pre i v) (j : Fin m) (hj : j ≠ i) :
    w.post j = pre j := w.others_untouched j hj

/-- НЕГАТИВНЫЙ ТЕСТ: пост-состояние записи — точно updateRow
pre address value (иное пост-состояние не типизируется). -/
theorem ram_post_is_exact_write {m n : ℕ}
    {pre : Matrix (Fin m) (Fin n) ℝ} {i : Fin m} {v : Fin n → ℝ}
    (w : RamWriteCert pre i v) :
    w.post = Matrix.updateRow pre i v := w.post_eq

/-! ### N6. Спуск-сертификат без реального убывания невозможен -/

/-- НЕГАТИВНЫЙ ТЕСТ (спека §11.2-1): HonestTransition со строгим
спуском влечёт РЕАЛЬНОЕ строгое убывание objective — «ручной»
положительный drop при невозрастающем objective противоречив. -/
theorem fictitious_drop_contradiction {S : Type*}
    (obj : S → ℝ) (s s' : S) (rs rl bs b' : ℝ)
    (T : HonestTransition obj s s' rs rl bs b')
    (hbad : obj s ≤ obj s') : False := by
  have ⟨h, _⟩ := honest_actual_drop obj s s' rs rl bs b' T
  have : obj s' < obj s := h
  linarith

end Hagi.Unified.NegativeTests
