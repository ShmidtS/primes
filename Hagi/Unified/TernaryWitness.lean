import Mathlib
import Hagi.Unified.DescentCoreQuad
import Hagi.Runtime.TernaryExact
import Hagi.Unified.HonestTransition

/-!
# TernaryWitness — многомерный составной свидетель (аудит-3, Фаза 4.2)

Связывает «острова» формализации в один результат:
многомерная квадратичная цель (DescentCoreQuad.quadE, k → ℝ)
+ реальный тернарный квантователь (Runtime.qTern, сетка {-1,0,+1}·s)
+ контракт шага (Unified.HonestTransition).

Доказуется ЧЕСТНО: тернарно-квантованный оптимум
w* := fun i => qTern s (a i) (при |a i| ≤ 3s/2 по всем каналам)
имеет энергию ≤ k·s²/8 — абсолютный потолок субоптимальности
через пошаговую дисторсию |x − qTern s x| ≤ s/2; и для любого
состояния x с энергией выше потолка прыжок к w* — сертифицированный
спуск с дропом E(x) − k·s²/8 ≥ 0. Никаких постулируемых спусков:
дроп выведен из свойств квантователя.
-/

namespace Hagi.Unified.TernaryWitness

open Hagi.Unified.DescentCoreQuad Hagi.Runtime Hagi.Unified.HonestTransition

variable {k : Type*} [Fintype k]

/-- Тернарно-квантованный оптимум: каждая координата цели
округляется на сетку {-1,0,+1}·s. -/
noncomputable def quantOpt (s : ℝ) (a : k → ℝ) : k → ℝ :=
  fun i => qTern s (a i)

/-- Абсолютный потолок субоптимальности квантованного оптимума:
quadE a (quantOpt s a) ≤ k·s²/8 при полной in-range цели.
Выведен из пошаговой дисторсии квантователя (qTern_error_in),
не постулирован. -/
theorem quantOpt_energy_bound (s : ℝ) (hs : 0 < s) (a : k → ℝ)
    (hin : ∀ i, ternInRange s (a i)) :
    quadE a (quantOpt s a) ≤ (Fintype.card k : ℝ) * s ^ 2 / 8 := by
  have hper : ∀ i, (a i - qTern s (a i)) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    have habs := qTern_error_in s (a i) hs (hin i)
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    have h3 : -(a i - qTern s (a i)) ^ 2 ≤ (s / 2) ^ 2 := by
      nlinarith [sq_nonneg (a i - qTern s (a i))]
    nlinarith [sq_nonneg (a i - qTern s (a i)), h1, h2, h3]
  have hsum : ∑ i, (a i - qTern s (a i)) ^ 2
      ≤ ∑ i : k, (s / 2) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hper i)
  have hconst : ∑ i : k, (s / 2) ^ 2
      = (Fintype.card k : ℝ) * (s / 2) ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hconst] at hsum
  -- цель: quadE a (quantOpt s a) ≤ card * s^2 / 8
  unfold quadE quantOpt
  have hsq : ∀ i : k, (qTern s (a i) - a i) ^ 2
      = (a i - qTern s (a i)) ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  -- теперь цель: (∑ (a i - qTern)^2)/2 ≤ card*s^2/8
  have heq : (s / 2) ^ 2 = s ^ 2 / 4 := by ring
  rw [heq] at hsum
  linarith

/-- СОСТАВНОЙ СВИДЕТЕЛЬ: для любого состояния x с энергией не
ниже потолка прыжок к тернарно-квантованному оптимуму — ЧЕСТНЫЙ
переход с выведенным спуском (дроп = E(x) − k·s²/8 ≥ 0 —
следствие quantOpt_energy_bound, не гипотеза). -/
noncomputable def quant_jump_honest (s : ℝ) (hs : 0 < s) (a x : k → ℝ)
    (hin : ∀ i, ternInRange s (a i))
    (hxe : (Fintype.card k : ℝ) * s ^ 2 / 8 < quadE a x) :
    HonestTransition (fun w => quadE a w) x (quantOpt s a)
      (riskSpend := 0) (riskLim := 0) (budgetSpend := 0)
      (budget' := 0) where
  objectiveDrop := quadE a x
    - (Fintype.card k : ℝ) * s ^ 2 / 8
  objectiveDrop_pos := by
    have hb := quantOpt_energy_bound s hs a hin
    linarith
  actualDescent := by
    have hb := quantOpt_energy_bound s hs a hin
    show quadE a (quantOpt s a) ≤ quadE a x
      - (quadE a x - (Fintype.card k : ℝ) * s ^ 2 / 8)
    linarith
  riskBound := le_refl 0
  budgetBound := le_refl 0

end Hagi.Unified.TernaryWitness
