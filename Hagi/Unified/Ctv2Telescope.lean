import Hagi.Unified.CertUnify

/-!
# Семейственный телескоп CertifiedTransitionV2

Кумулятивная связь между прогрессом сертификатов и
реальной энергией ВЫВОДИТСЯ из поштучных сертификатов
перехода с операциональными условиями спуска: гипотеза
телескопа становится теоремой. Каждый шаг честен по
`ctv2Honest`; индукция по горизонту собирает телескоп.
-/

namespace Hagi.Unified.Ctv2Telescope

open Hagi.Model Hagi.System Hagi.Unified.CertUnify Hagi.Unified.HonestTransition
open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Заявленный спуск шага (тот же, что у сертификата). -/
noncomputable def stepDrop (u : StageInput X) : ℝ :=
  u.eff.growGain + u.gap
    + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
      - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    - u.sp.kappa * u.sp.s * u.eff.quantErr

/-- ГЛАВНАЯ ТЕОРЕМА: из поштучных сертификатов перехода с
операциональными условиями спуска выводится кумулятивный
телескоп — сумма заявленных спусков не превосходит
реального убывания энергии. -/
theorem ctv2_family_telescope
    (S : ℕ → Hagi.System.GrowthState X)
    (u : ℕ → StageInput X) (riskLim : ℝ) (T : ℕ)
    (hexec : ∀ t, S (t + 1) = advance (S t) (u t))
    (hc : ∀ t, CertifiedTransitionV2 (S t) (advance (S t) (u t))
      (u t) riskLim)
    (hgain : ∀ t, (u t).eff.growEnergy
      ≤ (S t).energy - (u t).eff.growGain)
    (hgap0 : ∀ t, 0 ≤ (u t).gap)
    (hmerge : ∀ t, (u t).eff.mergeEnergy
      ≤ (u t).eff.growEnergy - (u t).gap)
    (hL : ∀ t, 0 < (u t).sp.L)
    (heta : ∀ t, (u t).sp.eta ≤ 1 / (u t).sp.L)
    (hdesc : ∀ t, ‖(u t).stepDir‖ ^ 2
      ≤ ⟪(u t).grad, (u t).stepDir⟫_ℝ)
    (hjoint : ∀ t, (u t).eff.jointEnergy
      ≤ (u t).eff.mergeEnergy
        - (u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
        + (u t).sp.L * (u t).sp.eta ^ 2
          * ‖(u t).stepDir‖ ^ 2 / 2)
    (hledger : ∀ t, (u t).eff.compressEnergy
        - (u t).eff.jointEnergy
      ≤ (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr) :
    ∑ t ∈ Finset.range T, stepDrop (u t)
      ≤ (S 0).energy - (S T).energy := by
  have hstep : ∀ t, (S (t + 1)).energy
      ≤ (S t).energy - stepDrop (u t) := by
    intro t
    have hd := Hagi.Model.advance_energy_drop (S t) (u t)
      (hgain t) (hgap0 t) (hmerge t) (hL t) (heta t)
      (hdesc t) (hjoint t) (hledger t)
    rw [hexec t]
    have hE : (advance (S t) (u t)).energy
        = (u t).eff.compressEnergy := rfl
    rw [hE]
    unfold stepDrop
    linarith
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have hs := hstep T
    linarith

end Hagi.Unified.Ctv2Telescope
