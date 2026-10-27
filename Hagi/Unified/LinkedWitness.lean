import Hagi.Unified.MasterHAGICoupled
import Hagi.Model.CertifiedTransition

/-!
# LinkedWitness — склейка (g) аудита v5

НЕТРИВИАЛЬНЫЙ витнес LinkedHAGIInvariant на T = 3 с
ненулевым состоянием: семейство CertifiedTransition строится
на РЕАЛЬНОЙ witness-траектории wTraj (capability 1 → 8,
бюджет 100 → 94), и certified_family_linked порождает
связанный инвариант. Витнес не T=1/нулевой — прямой ответ
аудиту v5 п.6.
-/

namespace Hagi.Unified

open Hagi.Model

/-- Семейство сертифицированных переходов на wTraj: каждый шаг
t < 3 удовлетворяет операционным условиям (η > 0, gap ≥ 0,
κ·s < 2·gain). -/
theorem wTraj_certified_family :
    ∀ t < wTraj.T, CertifiedTransition (wTraj.state t)
      (wTraj.state (t + 1)) (wTraj.input t)
      ((wTraj.input t).eff.growRisk + (wTraj.input t).eff.mergeRisk
        + (wTraj.input t).eff.jointRisk
        + (wTraj.input t).eff.compressRisk) := by
  intro t ht
  have ht3 : t < 3 := ht
  match t with
  | 0 =>
      have hstep : wTraj.state 1 = advance wS0 wU0 := rfl
      rw [show wTraj.input 0 = wU0 from rfl]
      exact certifiedTransition_of_advance (S := wS0) wU0
        (by simp [wU0]) (by simp [wU0]) (by simp [wU0])
  | 1 =>
      have h1 : wTraj.state 1 = advance wS0 wU0 := rfl
      have h2 : wTraj.state 2 = advance (advance wS0 wU0) wU1 := rfl
      rw [show wTraj.input 1 = wU1 from rfl]
      refine certifiedTransition_of_advance (S := wTraj.state 1)
        wU1 (by simp [wU1]) (by simp [wU1]) (by simp [wU1])
  | 2 =>
      refine certifiedTransition_of_advance (S := wTraj.state 2)
        wU2 (by simp [wU2]) (by simp [wU2]) (by simp [wU2])


/-- ПОНЫЙ НЕТРИВИАЛЬНЫЙ ВИТНЕС: LinkedHAGIInvariant на wTraj,
T = 3, ненулевые состояния (capability 1→8, budget 100→94),
alpha = 1. Построен ЧЕРЕЗ certified_family_linked — витнес
самого капстоуна на реальных exec-переходах. -/
theorem linkedHAGI_witness :
    LinkedHAGIInvariant 3 wTraj.state wTraj.input
      (fun t => (wTraj.input t).eff.growRisk
        + (wTraj.input t).eff.mergeRisk
        + (wTraj.input t).eff.jointRisk
        + (wTraj.input t).eff.compressRisk)
      (fun t => (wTraj.input t).eff.growCost
        + (wTraj.input t).eff.mergeCost
        + (wTraj.input t).eff.jointCost
        + (wTraj.input t).eff.compressCost)
      (fun _ _ => (0:ℝ)) (fun _ => (0:ℝ)) 1 := by
  have hrisk : ∀ t ∈ Finset.range 3,
      0 ≤ (wTraj.input t).eff.growRisk + (wTraj.input t).eff.mergeRisk
        + (wTraj.input t).eff.jointRisk
        + (wTraj.input t).eff.compressRisk := by
    intro t ht
    have ht3 : t < 3 := Finset.mem_range.mp ht
    interval_cases t
    · rw [show wTraj.input 0 = wU0 from rfl]; norm_num [wU0]
    · rw [show wTraj.input 1 = wU1 from rfl]; norm_num [wU1]
    · rw [show wTraj.input 2 = wU2 from rfl]; norm_num [wU2]
  have hspend : ∀ t ∈ Finset.range 3,
      0 ≤ (wTraj.input t).eff.growCost + (wTraj.input t).eff.mergeCost
        + (wTraj.input t).eff.jointCost
        + (wTraj.input t).eff.compressCost := by
    intro t ht
    have ht3 : t < 3 := Finset.mem_range.mp ht
    interval_cases t
    · rw [show wTraj.input 0 = wU0 from rfl]; norm_num [wU0]
    · rw [show wTraj.input 1 = wU1 from rfl]; norm_num [wU1]
    · rw [show wTraj.input 2 = wU2 from rfl]; norm_num [wU2]
  have hbudget : 0 ≤ (wTraj.state 3).budget := by
    have hb := Hagi.Model.certified_trajectory_budget wTraj.state
      wTraj.input 3 wTraj_certified_family
    have e0 : wTraj.input 0 = wU0 := rfl
    have e1 : wTraj.input 1 = wU1 := rfl
    have e2 : wTraj.input 2 = wU2 := rfl
    have hsum : ∑ t ∈ Finset.range 3,
        ((wTraj.input t).eff.growCost + (wTraj.input t).eff.mergeCost
          + (wTraj.input t).eff.jointCost
          + (wTraj.input t).eff.compressCost) = 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [e0, e1, e2]
      norm_num [wU0, wU1, wU2]
    rw [hsum] at hb
    have hB0 : (wTraj.state 0).budget = 100 := rfl
    rw [hB0] at hb
    linarith
  have hgrowth : (wTraj.state 0).capability * (1 + 1) ^ 3
      ≤ (wTraj.state 0).capability
        + ∑ t ∈ Finset.range 3, (wTraj.input t).eff.growGain := by
    have hcap := Hagi.Model.certified_trajectory_capability
      wTraj.state wTraj.input 3 wTraj_certified_family
    have e0 : wTraj.input 0 = wU0 := rfl
    have e1 : wTraj.input 1 = wU1 := rfl
    have e2 : wTraj.input 2 = wU2 := rfl
    have hsum : ∑ t ∈ Finset.range 3,
        (wTraj.input t).eff.growGain = 7 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [e0, e1, e2]
      norm_num [wU0, wU1, wU2]
    rw [hsum] at hcap
    have hC0 : (wTraj.state 0).capability = 1 := rfl
    rw [hC0] at hcap ⊢
    rw [hsum]
    norm_num
  exact certified_family_linked wTraj.state wTraj.input 3 1
    (fun _ _ => (0:ℝ)) (fun _ => (0:ℝ)) wTraj_certified_family
    hrisk hspend hbudget hgrowth (fun i => le_refl _)

end Hagi.Unified

