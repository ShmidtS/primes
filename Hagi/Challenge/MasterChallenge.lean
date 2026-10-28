import Hagi.Unified.CorePremisesDerived

/-!
# Comparator-Challenge: MasterHAGICore (аудит v6, шаг 2)

Методология openai/math Comparator: ЧЕСТНАЯ формулировка
закреплена в отдельном challenge-файле. Вывод прописан
ПОЛНОСТЬЮ (не делегирован): любое изменение смысла
MasterHAGICore (усиление посылок, ослабление заключения)
ломает тип делегирующего доказательства — challenge падает в
сборке. Посылки — именованный контракт CorePremises (его тип
дополнительно закреплён хешем в Challenge/challenges.json,
проверяется scripts/ChallengeCheck.py). Допустимые аксиомы:
ровно propext, Classical.choice, Quot.sound.

Scope (что закреплено): заключение одностадийного
мастер-результата (убывание Φ_HAGI с точностью до
λ·riskSpend + ν·ε_Q И точная бюджетная бухгалтерия) при
посылках CorePremises S S' epsQ w. Что НЕ закреплено:
определение CorePremises (динамируется через pinned hash),
GenState/GrowthState поля.
-/

namespace Hagi.Challenge

open Hagi.Unified

/-- Comparator-формулировка: заключение MasterHAGICore
прописано полностью; посылка — именованный контракт
CorePremises. Доказательство делегирует MasterHAGICore: при
расхождении формулировок файл не скомпилируется. -/
theorem master_hagi_core_comparator {X : Type}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S S' : GenState X) (lam nu Qtarget epsQ : ℝ)
    (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu) (h_epsQ : 0 ≤ epsQ)
    (hp : CorePremises S S' epsQ w) :
    -- ЗАКЛЮЧЕНИЕ (прописано, не делегировано):
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w
        - (verify S.toGrowthState).decrease
        + lam * (verify S.toGrowthState).riskSpend
        + nu * epsQ
    ∧ S'.toGrowthState.budget
      = S.toGrowthState.budget
        - (verify S.toGrowthState).budgetSpend :=
  MasterHAGICore S S' lam nu Qtarget epsQ w hlam hnu h_epsQ hp

end Hagi.Challenge
