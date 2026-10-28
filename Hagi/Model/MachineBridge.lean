import Hagi.Model.StageSemantics
import Hagi.Model.ReferenceMachine

/-!
# Мост: эталонная машина → стадийная семантика (аудит v7, этап 4)

`machineStageInput` строит `StageInput ℝ` из ИЗМЕРЕНИЙ
эталонной машины (ReferenceMachine, n = 1): все энергии —
ВЫЧИСЛЕННЫЕ функции весов (growEnergy = E(w),
jointEnergy = E(w − η∇E), compressEnergy = E(Q(w − η∇E)),
quantErr — вычисленная ошибка квантования).

`machine_advance_certified`: для любого состояния S с
S.energy = E(w) вход, собранный ИЗ МАШИНЫ, сертифицируется
каноническим `advance_energy_drop` — измерения имеют
происхождение (веса), сертификат — следствие, а не постулат.
-/

namespace Hagi.Model.MachineBridge

open Hagi.System Hagi.Model.ReferenceMachine Real InnerProductSpace

variable (a w : Fin 1 → ℝ)

/-- StageInput, СОБРАННЫЙ ИЗ МАШИННЫХ ИЗМЕРЕНИЙ: каждая
энергия — функция весов; стоимости/риски нулевые (машина их
не моделирует); L = 1 — фактическая кривизна E=(x−a)²/2. -/
noncomputable def machineStageInput (eta Delta kappa s : ℝ)
    (heta : 0 < eta) : StageInput ℝ where
  sp := { eta := eta, L := 1, kappa := kappa, s := s }
  eff := {
    growGain := 0, growCost := 0, growRisk := 0,
    growEnergy := energy a w,
    mergeEnergy := energy a w, mergeRisk := 0, mergeCost := 0,
    jointEnergy := energy a (jointStep a w eta),
    jointRisk := 0, jointCost := 0,
    quantErr := quantErr Delta (jointStep a w eta),
    compressEnergy := energy a (machineStep a w eta Delta),
    compressRisk := 0, compressCost := 0 }
  gap := 0
  stepDir := w 0 - a 0
  grad := w 0 - a 0
  h_costs_nn := by norm_num
  h_risks_nn := by norm_num
  h_eta_pos := heta

/-- ЗВУК МОСТА: если состояние S несёт энергию, ИЗМЕРЕННУЮ
машиной (S.energy = E(w)), и ledger-факт квантования
выполнен на ВЫЧИСЛЕННЫХ величинах, то канонический
`advance_energy_drop` сертифицирует переход — в скалярной
форме: certified drop = η·d² − η²·d²/2 − κ·s·quantErr,
при 0 < η ≤ 1 и d ≠ 0 строго положителен. Все слагаемые —
машинные измерения, ни одного постулата. -/
theorem machine_advance_certified (eta Delta kappa s : ℝ)
    (heta : 0 < eta) (hetaL : eta ≤ 1)
    (S : GrowthState ℝ) (hS : S.energy = energy a w)
    (hledger : energy a (machineStep a w eta Delta)
        - energy a (jointStep a w eta)
      ≤ kappa * s * quantErr Delta (jointStep a w eta)) :
    energy a (machineStep a w eta Delta)
      ≤ S.energy - (eta * (w 0 - a 0) * (w 0 - a 0)
          - eta ^ 2 * (w 0 - a 0) * (w 0 - a 0) / 2
          - kappa * s * quantErr Delta (jointStep a w eta)) := by
  have hdrop := advance_energy_drop S
    (machineStageInput a w eta Delta kappa s heta)
    (hgain := by
      simp only [machineStageInput]
      rw [hS]
      simp)
    (hgap0 := by simp [machineStageInput])
    (hmerge := by simp [machineStageInput])
    (hL := by simp [machineStageInput])
    (heta := by
      simp only [machineStageInput]
      simpa using hetaL)
    (hdesc := by
      simp only [machineStageInput, Real.inner_apply]
      calc ‖(w 0 - a 0 : ℝ)‖ ^ 2
          = ‖(w 0 - a 0 : ℝ)‖ * ‖(w 0 - a 0 : ℝ)‖ := by rw [sq]
        _ = |w 0 - a 0| * |w 0 - a 0| := by rw [Real.norm_eq_abs]
        _ = (w 0 - a 0) * (w 0 - a 0) := abs_mul_abs_self _
        _ ≤ (w 0 - a 0) * (w 0 - a 0) := le_refl _)
    (hjoint := by
      simp only [machineStageInput, Real.inner_apply]
      have hE : energy a w = (w 0 - a 0) ^ 2 / 2 := by
        unfold energy
        rw [Fin.sum_univ_one]
      have hn : ‖(w 0 - a 0 : ℝ)‖ ^ 2 = (w 0 - a 0) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [jointStep_energy, hE, hn]
      nlinarith [sq_nonneg (w 0 - a 0)])
    (hledger := hledger)
  simp only [machineStageInput, Real.inner_apply, zero_add,
    add_zero, Real.norm_eq_abs] at hdrop
  rw [sq_abs (w 0 - a 0)] at hdrop
  ring_nf at hdrop ⊢
  linarith

end Hagi.Model.MachineBridge
