import Hagi.Model.StageSemantics
import Hagi.System.Certificates

/-!
# CertifiedTransition — зависимый сертификат перехода

Реализация эскиза аудита v4 §5.4: сертификат привязан к
КОНКРЕТНЫМ состояниям pre/post — `exec` требует, чтобы post
был получен реальным `advance`; прогресс/риск/бюджет —
свойства именно этой пары состояний (нельзя выдать
сертификат произвольной последовательности чисел).
-/

namespace Hagi.Model

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Сертифицированный переход: post получен исполнением
advance над pre с входом u; спуск положителен; риск и бюджет
честно учтены относительно лимитов шага. -/
structure CertifiedTransition (S S' : Hagi.System.GrowthState X)
    (u : StageInput X) (riskLim : ℝ) where
  /-- Исполнение: S' — реальный результат advance. -/
  exec : S' = advance S u
  /-- Прогресс: verify-сертификат нового состояния положителен. -/
  progress : 0 < (Hagi.System.verify S').decrease
  /-- Безопасность: прирост защищённого риска в лимите. -/
  safety : S'.protectedRisk
    ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
      + u.eff.jointRisk + u.eff.compressRisk)
  /-- Ресурсы: точный бюджетный ledger пост-состояния. -/
  resources : S'.budget = S.budget - (u.eff.growCost + u.eff.mergeCost
    + u.eff.jointCost + u.eff.compressCost)

/-- КОНСТРУКТОР-ЗВУЧНОСТЬ: при операциональных условиях
(advance_verify_decrease_pos) honest-переход порождает
CertifiedTransition — поля safety/resources выполняются
rfl-определительно для advance. -/
theorem certifiedTransition_of_advance (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (hgap : 0 ≤ u.gap) (heta : 0 ≤ u.sp.eta)
    (hks : u.sp.kappa * u.sp.s < 2 * u.eff.growGain) :
    CertifiedTransition S (advance S u) u
      (u.eff.growRisk + u.eff.mergeRisk + u.eff.jointRisk
        + u.eff.compressRisk) where
  exec := rfl
  progress := advance_verify_decrease_pos S u hgap heta hks
  safety := by
    show (advance S u).protectedRisk
      ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk)
    simp only [advance]
    exact le_of_eq (by ring)
  resources := by
    simp only [advance]
    ring

end Hagi.Model
