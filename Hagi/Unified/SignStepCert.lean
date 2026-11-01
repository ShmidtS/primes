import Hagi.Unified.LoopInstances
import Hagi.Unified.SignDescent

/-!
# Сертифицированный сжатый шаг: знаковая компрессия в
StepCert

Sign-шаг (компрессия градиента до знаков с масштабом)
инстанцирует полный StepCert на квадратичной машине:
честный спуск через выравнивание масштабированного
знакового направления, покомпонентный пол качества и
ДЕШЁВЫЙ бюджет — пересылка одного бита на координату
вместо полного слова. Экономия коммуникации входит в
бюджетный канал certified-цикла.
-/

namespace Hagi.Unified.SignStepCert

open Hagi.Unified.CertifiedLoop Hagi.Unified.LinkedQVec
open Hagi.Unified.HonestTransition Hagi.Unified.LoopInstances
open Hagi.Unified.DescentCore Hagi.Unified.DescentCoreQuad
open Hagi.Unified.SignDescent Hagi.Step.SignSGD

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Стоимость пересылки сжатого градиента: по биту на
координату. -/
def signCommCost (k₂ : Type*) [Fintype k₂] : ℝ :=
  (Fintype.card k₂ : ℝ)

/-- Стоимость пересылки полного градиента: слово на
координату. -/
def fullCommCost (k₂ : Type*) [Fintype k₂] : ℝ :=
  32 * (Fintype.card k₂ : ℝ)

/-- КОМПРЕССИОННАЯ ЭКОНОМИЯ: пересылка знаков не дороже
полной пересылки градиента. -/
theorem sign_comm_le :
    signCommCost k ≤ fullCommCost k := by
  unfold signCommCost fullCommCost
  have hn : (0:ℝ) ≤ (Fintype.card k : ℝ) := by positivity
  nlinarith [hn]

/-- Масштабированный sign-шаг на квадратичной машине. -/
noncomputable def signStep (a x : k → ℝ) : k → ℝ :=
  fun i => signScale (quadGrad a x) * sgn1 (quadGrad a x i)

theorem sgn1_ne_zero {y : ℝ} (hy : y ≠ 0) : sgn1 y ≠ 0 := by
  unfold sgn1
  rcases lt_trichotomy y 0 with h | h | h
  · rw [if_pos h]
    norm_num
  · exact absurd h hy
  · rw [if_neg (by linarith), if_neg (by linarith : ¬ y = 0)]
    norm_num

/-- Норма знакового направления строго положительна при
ненулевом градиенте. -/
theorem signStep_nrm_pos (a x : k → ℝ)
    (hx : quadGrad a x ≠ 0) : 0 < nrm2 (signStep a x) := by
  obtain ⟨i₀, h₀⟩ : ∃ i, quadGrad a x i ≠ 0 := by
    by_contra hcon
    exact hx (funext fun i => by
      by_contra hi
      exact hcon ⟨i, hi⟩)
  have hs : 0 < signScale (quadGrad a x) := by
    unfold signScale
    have habs : (0:ℝ) < ∑ i, |quadGrad a x i| := by
      have hnn : (0:ℝ) ≤ ∑ i, |quadGrad a x i| :=
        Finset.sum_nonneg fun i _ => abs_nonneg _
      have hle : |quadGrad a x i₀| ≤ ∑ i, |quadGrad a x i| :=
        Finset.single_le_sum (f := fun i => |quadGrad a x i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i₀)
      have hpos : (0:ℝ) < |quadGrad a x i₀| := abs_pos.mpr h₀
      nlinarith
    have hcard : (0:ℝ) < (Fintype.card k : ℝ) := by positivity
    apply div_pos habs hcard
  have hdir : (signStep a x) i₀ ≠ 0 := by
    unfold signStep
    have hsgn := sgn1_ne_zero h₀
    intro hzero
    have : signScale (quadGrad a x) * sgn1 (quadGrad a x i₀) = 0 :=
      hzero
    exact absurd this (mul_ne_zero hs.ne' hsgn)
  have hsq : (0:ℝ) < (signStep a x i₀)^2 := by
    have hsq : (signStep a x i₀)^2
        = (signStep a x i₀) * (signStep a x i₀) := by ring
    rw [hsq]
    exact mul_self_pos.mpr hdir
  have hnn : (0:ℝ) ≤ nrm2 (signStep a x) := by
    unfold nrm2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hle : (signStep a x i₀)^2
      ≤ nrm2 (signStep a x) := by
    unfold nrm2
    exact Finset.single_le_sum (f := fun i => (signStep a x i)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  nlinarith

/-- Честный спуск сжатого шага: выравнивание знакового
направления даёт сертифицированное чистое убывание
квадратичной цели. -/
theorem sign_step_descent (a x : k → ℝ)
    (eta : ℝ) (heta : 0 < eta)
    (hetaL : eta ≤ 1 / (quadObjective a).L) :
    (quadObjective a).f (x - fun i => eta * (signStep a x i))
      ≤ (quadObjective a).f x
        - eta * (1 - (quadObjective a).L * eta / 2)
            * nrm2 (signStep a x) :=
  descent_drop (quadObjective a) x (signStep a x)
    (sign_scaled_aligned (quadObjective a) x) eta heta hetaL

/-- Заявленный спуск сжатого шага. -/
noncomputable def signDrop (a x : k → ℝ) (eta : ℝ) : ℝ :=
  eta * (1 - (quadObjective a).L * eta / 2) * nrm2 (signStep a x)

/-- Заявленный спуск строго положителен при корректном
шаге и ненулевом градиенте. -/
theorem signDrop_pos (a x : k → ℝ) (hx : quadGrad a x ≠ 0)
    (eta : ℝ) (heta : 0 < eta) (hetaL : eta ≤ 1) :
    0 < signDrop a x eta := by
  have hnrm := signStep_nrm_pos a x hx
  have hfac : (0:ℝ) < 1 - eta / 2 := by nlinarith [hetaL]
  unfold signDrop
  have hL : (quadObjective a).L = 1 := rfl
  rw [hL]
  simp only [one_mul]
  exact mul_pos (mul_pos heta hfac) hnrm

/-- Энергия после сжатого шага не выше стартовой. -/
theorem signStep_energy_le (a x : k → ℝ)
    (eta : ℝ) (heta : 0 < eta)
    (hetaL : eta ≤ 1 / (quadObjective a).L) :
    quadE a (x - fun i => eta * (signStep a x i)) ≤ quadE a x := by
  have h := sign_step_descent a x eta heta hetaL
  have hfac : (0:ℝ) ≤ 1 - (quadObjective a).L * eta / 2 := by
    have hL : (quadObjective a).L = 1 := rfl
    rw [hL]
    have h1 : eta ≤ 1 := by
      rw [show (1:ℝ) / (quadObjective a).L = 1 from by
        simp [hL]] at hetaL
      exact hetaL
    nlinarith
  have hpos : (0:ℝ) ≤ eta * (1 - (quadObjective a).L * eta / 2)
      * nrm2 (signStep a x) :=
    mul_nonneg (mul_nonneg (le_of_lt heta) hfac)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  show (quadObjective a).f (x - fun i => eta * (signStep a x i))
    ≤ (quadObjective a).f x
  linarith

/-- СЕРТИФИЦИРОВАННЫЙ СЖАТЫЙ ШАГ: полный StepCert для
знакового шага — честный спуск, покомпонентный пол и
ДЕШЁВЫЙ бюджет пересылки (бит вместо слова). -/
noncomputable def signStepCert (a x : k → ℝ)
    (hx : quadGrad a x ≠ 0)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (hfloor : ∀ i, floor i ≤ 1 / (1 + quadE a x))
    (hrisk : signCommCost k ≤ riskLim)
    (eta : ℝ) (heta : 0 < eta) (hetaL : eta ≤ 1) :
    StepCert (fun w => quadE a w) (quadMeasured a) floor riskLim
      x (x - fun i => eta * (signStep a x i))
      (fullCommCost k) (fullCommCost k - signCommCost k) where
  spend := signCommCost k
  trans := ⟨signDrop a x eta,
    signDrop_pos a x hx eta heta hetaL,
    by
      have h := sign_step_descent a x eta heta
        (by rw [show (quadObjective a).L = 1 from rfl]; simpa using hetaL)
      show quadE a (x - fun i => eta * (signStep a x i))
        ≤ quadE a x - signDrop a x eta
      exact h,
    hrisk,
    by
      unfold fullCommCost signCommCost
      have hn : (0:ℝ) ≤ (Fintype.card k : ℝ) := by positivity
      linarith⟩
  hspend_nn := by
    unfold signCommCost
    positivity
  hdec := by
    have := sign_comm_le (k := k)
    unfold fullCommCost signCommCost at *
    linarith
  quality := by
    intro i
    have hle := signStep_energy_le a x eta heta
      (by rw [show (quadObjective a).L = 1 from rfl]; simpa using hetaL)
    have hf := hfloor i
    rw [quadMeasured]
    show floor i
      ≤ 1 / (1 + quadE a (x - fun i => eta * (signStep a x i)))
    have h1 : (0:ℝ) < 1 + quadE a x := by
      have := quadE_nonneg a x
      linarith
    have h2 : (0:ℝ)
        < 1 + quadE a (x - fun i => eta * (signStep a x i)) := by
      have := quadE_nonneg a
        (x - fun i => eta * (signStep a x i))
      linarith
    exact le_trans hf
      (one_div_le_one_div_of_le h2 (by linarith))

end Hagi.Unified.SignStepCert
