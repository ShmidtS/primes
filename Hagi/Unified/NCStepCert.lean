import Hagi.Unified.CertifiedLoop
import Hagi.Model.NeuralComputer

/-!
# Мост нейрокомпьютер → CertifiedLoop

Нейрокомпьютер (обучаемое ядро H-Net-чанкера + замороженный
точный CPU + адресуемая память) инстанцирует канонический
StepCert: шаг обучения с честным энергийным спуском,
покомпонентным полом capability и честным бюджетом.
Сертифицированная траектория нейрокомпьютера живёт внутри
главного капстоуна: строгий спуск энергии на любом
горизонте при неизменном процессоре.
-/

namespace Hagi.Unified.NCStepCert

open Hagi.Model.NeuralComputer
open Hagi.Unified.CertifiedLoop Hagi.Unified.HonestTransition
open Hagi.Unified.LinkedQVec

/-- Обучающий переход нейрокомпьютера: как канонический,
но с честным энергийным спуском. -/
noncomputable def ncCertStep (S : NCState) (u : NCInput)
    (d : ℝ) : NCState :=
  { ncAdvance S u with
    energy := S.energy - d }

/-- Инварианты канонического перехода сохраняются:
процессор заморожен и при обучающем спуске. -/
theorem ncCertStep_cpu_frozen (S : NCState) (u : NCInput)
    (d : ℝ) : (ncCertStep S u d).cpu = S.cpu := rfl

/-- Бюджетная бухгалтерия обучающего перехода точна. -/
theorem ncCertStep_budget (S : NCState) (u : NCInput)
    (d : ℝ) :
    (ncCertStep S u d).budget = S.budget - u.cost := rfl

/-- Энергийный спуск обучающего перехода — точное
равенство. -/
theorem ncCertStep_energy (S : NCState) (u : NCInput)
    (d : ℝ) :
    (ncCertStep S u d).energy = S.energy - d := rfl

/-- Измеритель качества нейрокомпьютера: канал —
capability состояния. -/
noncomputable def ncMeasured : MeasuredState NCState where
  evaluate S _ := S.capability

/-- Сертификат шага нейрокомпьютера: честный спуск +
покомпонентный пол + честный бюджет (риск-канал учтён
консервативным комбинированным лимитом: суммарная
стоимость и риск-трата не превосходят лимит риска). -/
noncomputable def ncStepCert (S : NCState) (u : NCInput)
    (d : ℝ) (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (hd : 0 < d)
    (hriskLim : u.cost + u.riskSpend ≤ riskLim)
    (hfloor : ∀ i, floor i ≤ S.capability)
    (hgain : 0 ≤ u.gain)
    (hbud : 0 ≤ S.budget)
    (hcost_le : u.cost ≤ S.budget) :
    StepCert (fun St => St.energy) ncMeasured floor riskLim
      S (ncCertStep S u d) S.budget (ncCertStep S u d).budget
      where
  spend := u.cost
  trans := ⟨d, hd,
    by
      show (ncCertStep S u d).energy ≤ S.energy - d
      rw [ncCertStep_energy],
    by
      have hr := u.hrisk
      linarith,
    by
      show (0:ℝ) ≤ (ncCertStep S u d).budget
      rw [ncCertStep_budget]
      linarith⟩
  hspend_nn := u.hcost
  hdec := by
    show (ncCertStep S u d).budget
      ≤ S.budget - u.cost
    rw [ncCertStep_budget]
  quality := by
    intro i
    have hcap : (ncCertStep S u d).capability
        = S.capability + u.gain := rfl
    have hf := hfloor i
    rw [ncMeasured]
    show floor i ≤ (ncCertStep S u d).capability
    rw [hcap]
    have hg := hgain
    linarith

/-- Траектория обучающих переходов. -/
noncomputable def ncTraj (S : NCState) (u : ℕ → NCInput)
    (d : ℕ → ℝ) : ℕ → NCState :=
  fun t => Nat.rec S (fun t' St => ncCertStep St (u t') (d t')) t

/-- Capability вдоль траектории не убывает при
неотрицательных приростах. -/
theorem ncTraj_capa_mono (S : NCState) (u : ℕ → NCInput)
    (d : ℕ → ℝ) (hgain : ∀ t, 0 ≤ (u t).gain) (t : ℕ) :
    S.capability ≤ (ncTraj S u d t).capability := by
  induction t with
  | zero =>
    show S.capability ≤ S.capability
    exact le_refl _
  | succ t ih =>
    have hstep : ncTraj S u d (t + 1)
        = ncCertStep (ncTraj S u d t) (u t) (d t) := rfl
    rw [hstep]
    have hcap : (ncCertStep (ncTraj S u d t) (u t) (d t)).capability
        = (ncTraj S u d t).capability + (u t).gain := rfl
    rw [hcap]
    have hg := hgain t
    linarith

/-- Процессор заморожен вдоль всей траектории. -/
theorem ncTraj_cpu_frozen (S : NCState) (u : ℕ → NCInput)
    (d : ℕ → ℝ) (t : ℕ) :
    (ncTraj S u d t).cpu = S.cpu := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hstep : ncTraj S u d (t + 1)
        = ncCertStep (ncTraj S u d t) (u t) (d t) := rfl
    rw [hstep, ncCertStep_cpu_frozen]
    exact ih

/-- ГЛАВНАЯ ТЕОРЕМА: сертифицированная траектория
нейрокомпьютера строго убывает по энергии на любом
положительном горизонте — процессор остаётся заморожен,
бюджет честен, качество держится покомпонентно. -/
theorem nc_loop_horizon (S : NCState) (u : ℕ → NCInput)
    (d : ℕ → ℝ) (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (hd : ∀ t, 0 < d t)
    (hriskLim : ∀ t, (u t).cost + (u t).riskSpend ≤ riskLim)
    (hfloor : ∀ i, floor i ≤ S.capability)
    (hgain : ∀ t, 0 ≤ (u t).gain)
    (hcost_le : ∀ t, (u t).cost ≤ (ncTraj S u d t).budget)
    (hbud : ∀ t, 0 ≤ (ncTraj S u d t).budget)
    (n : ℕ) (hn : 1 ≤ n) :
    (ncTraj S u d n).energy < (ncTraj S u d 0).energy
      ∧ (ncTraj S u d n).cpu = S.cpu := by
  have h₀ : FloorKept ncMeasured (ncTraj S u d 0) floor := by
    intro i
    have hf := hfloor i
    rw [ncMeasured]
    show floor i ≤ (ncTraj S u d 0).capability
    exact hf
  have main := certified_loop_strict
    (fun St => St.energy) ncMeasured floor riskLim
    (ncTraj S u d)
    (fun t => (ncTraj S u d t).budget)
    (fun t => d t) n
    h₀ (hbud 0)
    (fun t => ncStepCert (ncTraj S u d t.val) (u t.val)
      (d t.val) floor riskLim (hd t.val) (hriskLim t.val)
      (by
        intro i
        have hc := ncTraj_capa_mono S u d hgain t.val
        have hf := hfloor i
        linarith)
      (hgain t.val) (hbud t.val) (hcost_le t.val))
    (fun t => rfl)
    hn
  exact ⟨main.1, ncTraj_cpu_frozen S u d n⟩

end Hagi.Unified.NCStepCert
