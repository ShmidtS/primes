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

/-- МОСТ ПОКАЗАТЕЛЬ ↔ ЧЕСТНЫЙ СПУСК: при выровненном
направлении, корректном шаге и ошибке квантования в
половину сетки честный спуск шага не меньше показателя
verify нового состояния. -/
theorem stepDrop_ge_verify (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (heta0 : 0 ≤ u.sp.eta)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hL : 0 < u.sp.L) (heta : u.sp.eta ≤ 1 / u.sp.L)
    (hkappa : 0 ≤ u.sp.kappa) (hs : 0 ≤ u.sp.s)
    (hq : u.eff.quantErr ≤ 1 / 2) :
    (Hagi.System.verify (advance S u)).decrease ≤ stepDrop u := by
  unfold Hagi.System.verify Hagi.System.gainJoint stepDrop
  simp only [Hagi.Model.advance]
  have hd2 : (0:ℝ) ≤ ‖u.stepDir‖ ^ 2 := by positivity
  have key : u.sp.eta * ‖u.stepDir‖ ^ 2 / 2
      ≤ u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2 := by
    have h1 : u.sp.eta * ‖u.stepDir‖ ^ 2
        ≤ u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ := by
      nlinarith [mul_le_mul_of_nonneg_left hdesc heta0]
    have h2 : u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2
        ≤ u.sp.eta * ‖u.stepDir‖ ^ 2 := by
      have hLeta : u.sp.L * u.sp.eta ≤ 1 := by
        have := (le_div_iff₀ hL).mp heta
        linarith
      nlinarith [mul_nonneg heta0 hd2,
        mul_le_mul_of_nonneg_right hLeta hd2]
    field_simp
    linarith
  have hq2 : u.sp.kappa * u.sp.s * u.eff.quantErr
      ≤ u.sp.kappa * u.sp.s / 2 := by
    have hk := mul_nonneg hkappa hs
    have := mul_le_mul_of_nonneg_left hq hk
    rw [mul_div_assoc'] at this
    norm_num at this
    linarith
  linarith

/-- СЛЕДСТВИЕ: телескоп в форме показателей verify выводится
из тех же поштучных условий — гипотеза кумулятивного
прогресса для семейства переходов является теоремой. -/
theorem verify_family_telescope
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
    (heta0 : ∀ t, 0 ≤ (u t).sp.eta)
    (hdesc : ∀ t, ‖(u t).stepDir‖ ^ 2
      ≤ ⟪(u t).grad, (u t).stepDir⟫_ℝ)
    (hjoint : ∀ t, (u t).eff.jointEnergy
      ≤ (u t).eff.mergeEnergy
        - (u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
        + (u t).sp.L * (u t).sp.eta ^ 2
          * ‖(u t).stepDir‖ ^ 2 / 2)
    (hledger : ∀ t, (u t).eff.compressEnergy
        - (u t).eff.jointEnergy
      ≤ (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr)
    (hkappa : ∀ t, 0 ≤ (u t).sp.kappa)
    (hs : ∀ t, 0 ≤ (u t).sp.s)
    (hq : ∀ t, (u t).eff.quantErr ≤ 1 / 2) :
    ∑ t ∈ Finset.range T, (Hagi.System.verify (S (t + 1))).decrease
      ≤ (S 0).energy - (S T).energy := by
  have htele := ctv2_family_telescope S u riskLim T hexec hc
    hgain hgap0 hmerge hL heta hdesc hjoint hledger
  have hle : ∀ t ∈ Finset.range T,
      (Hagi.System.verify (S (t + 1))).decrease ≤ stepDrop (u t) := by
    intro t ht
    rw [hexec t]
    exact stepDrop_ge_verify (S t) (u t) (heta0 t) (hdesc t)
      (hL t) (heta t) (hkappa t) (hs t) (hq t)
  calc ∑ t ∈ Finset.range T, (Hagi.System.verify (S (t + 1))).decrease
      ≤ ∑ t ∈ Finset.range T, stepDrop (u t) :=
        Finset.sum_le_sum hle
    _ ≤ (S 0).energy - (S T).energy := htele

end Hagi.Unified.Ctv2Telescope
