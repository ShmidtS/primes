import Hagi.Unified.MasterHAGI

/-!
# LearningProblem — склейка (b) аудита v5 (ядро)

Мини-формулировка задачи обучения: состояния с энергией и
ёмкостью, ЛАНДАУЭРОВСКАЯ граница ёмкости свободной энергией
(C ≤ E, единичная эффективность) и энергобаланс перехода.
Из них ВЫВОДИТСЯ grow-посылка CorePremises — шаг (b)
аудита: допущение превращается в теорему (как DerivAlong
сделал для joint/compress; здесь — для grow).
-/

namespace Hagi.Unified

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Ядро задачи обучения: энергия и ёмкость состояния +
ладауэровский принцип (ёмкость ограничена свободной
энергией, ε = 1) + энергобаланс шага. -/
structure LearningKernel (S S' : GenState X) where
  /-- Ландауэровская граница: capability ≤ energy. -/
  landauer : S'.toGrowthState.capability
    ≤ S'.toGrowthState.energy
  /-- Энергобаланс: энергия убывает ровно на grow-затрату. -/
  balance : S'.toGrowthState.energy
    = S.toGrowthState.energy - S.toGrowthState.effects.growEnergy

/-- GROW-ПОСЫЛКА ВЫВЕДЕНА: при ландауэровской границе
(capability' ≤ energy'), энергобалансе (energy' = energy −
growEnergy) и честном gain (growGain ≤ C' − C, C ≥ 0),
посылка CorePremises growEnergy ≤ energy − growGain —
ТЕОРЕМА, не допущение. -/
theorem grow_premise_derived (S S' : GenState X)
    (hk : LearningKernel S S')
    (hgain : S.toGrowthState.effects.growGain
      ≤ S'.toGrowthState.capability - S.toGrowthState.capability)
    (hC0 : 0 ≤ S.toGrowthState.capability) :
    S.toGrowthState.effects.growEnergy
      ≤ S.toGrowthState.energy
        - S.toGrowthState.effects.growGain := by
  -- из баланса: growEnergy = energy − energy'
  have hspent : S.toGrowthState.effects.growEnergy
      = S.toGrowthState.energy - S'.toGrowthState.energy := by
    have := hk.balance
    linarith [this]
  -- gain ≤ C' − C ≤ C' ≤ E'
  have hgain2 : S.toGrowthState.effects.growGain
      ≤ S'.toGrowthState.energy := by
    have h1 : S.toGrowthState.effects.growGain
        ≤ S'.toGrowthState.capability
          - S.toGrowthState.capability := hgain
    have h2 : S'.toGrowthState.capability
        ≤ S'.toGrowthState.energy := hk.landauer
    have h3 : S.toGrowthState.effects.growGain
        ≤ S'.toGrowthState.capability := by linarith
    linarith
  -- итог: growEnergy = energy − E' ≤ energy − gain
  linarith [hspent, hgain2]


/-- MERGE-КАСКАД: merge-затрата определена каскадом от
grow-затраты: growEnergy − gap − mergeEnergy = slack,
slack ≥ 0 — материальный остаток, обеспеченный энергией
post-merge состояния (slack ≤ E''). Посылка CorePremises
mergeEnergy ≤ growEnergy − gap — ТЕОРЕМА каскада. -/
theorem merge_premise_derived (growE gap mergeE slack : ℝ)
    (hcascade : growE - gap - mergeE = slack)
    (hslack : 0 ≤ slack) :
    mergeE ≤ growE - gap := by linarith

/-- Материальность остатка: если slack обеспечен свободной
энергией post-merge состояния (E'' ≥ slack при балансе
E'' = E' − mergeEnergy), то каскад согласован с
ландауэровской бюджетной дисциплиной. -/
theorem merge_slack_feasible (E' E'' mergeE slack : ℝ)
    (hbalance : E'' = E' - mergeE)
    (hslackE : slack ≤ E'') :
    mergeE + slack ≤ E' := by linarith

end Hagi.Unified
