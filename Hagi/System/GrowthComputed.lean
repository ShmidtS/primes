import Mathlib.Tactic
import Hagi.System.GrowthState
import Hagi.Learning.TrainingTransition

set_option linter.style.header false

/-!
# GrowthComputed — вычисляемая энергия состояний роста (цикл 35)

Ответ аудиту #8 п.8 («energy в GrowthState — просто поле»):
канонический ВЫЧИСЛЯЕМЫЙ инстанс энергии — квадратичная
энергия сжатых весов:
  growthQuad w = Σ wᵢ²/2  (однозадачная TrainingTransition-
  цель с нулевой задачей: taskQual = quadLossAt 0 w).

Мост-теорема growEnergy_derived: если измеренные поля
согласованы с вычисляемой энергией (S.energy = growthQuad S.weights,
growEnergy-эффект = growthQuad весов после шага), то
h_emp_grow-посылка стадии grow (S'.growEnergy ≤ S.energy − gain)
ВЫВОДИТСЯ из доказанного спуска TrainingTransition —
эмпирическая посылка становится теоремой в каноническом
инстансе. Измеряемое поле остаётся для общего случая
(токен-KL), но имеет доказанного канонического представителя.
-/

open Finset

namespace Hagi.System.GrowthComputed

open Hagi.Learning.TrainingTransition

/-- Вычисляемая энергия сжатых весов: Σ wᵢ²/2. -/
noncomputable def growthQuad {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2 / 2

/-- Положительность энергии при ненулевых весах. -/
theorem growthQuad_pos_of_nonzero {n : ℕ} (w : Fin n → ℝ)
    (hw : ∑ i, w i ^ 2 ≠ 0) : 0 < growthQuad w := by
  have hpos : 0 < ∑ i, w i ^ 2 := by
    have hnn : (0:ℝ) ≤ ∑ i, w i ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rcases eq_or_lt_of_le hnn with hE | hE
    · exact absurd hE.symm hw
    · exact hE
  unfold growthQuad
  have hper : ∀ i : Fin n, w i ^ 2 / 2 = (1/2) * w i ^ 2 := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper i),
    ← Finset.mul_sum]
  exact mul_pos (by norm_num : (0:ℝ) < 1/2) hpos

/-- Градиентный шаг по весам (однозадачная нулевая цель:
g = w). -/
def growthStep {n : ℕ} (w : Fin n → ℝ) (eta : ℝ) : Fin n → ℝ :=
  fun i => w i - eta * w i

/-- ТОЧНОЕ тождество вычисляемой энергии шага:
E(step w η) = (1−η)² · E(w). -/
theorem growthQuad_step {n : ℕ} (w : Fin n → ℝ) (eta : ℝ) :
    growthQuad (growthStep w eta) = (1 - eta) ^ 2 * growthQuad w := by
  unfold growthQuad growthStep
  have hper : ∀ i : Fin n, (w i - eta * w i) ^ 2
      = (1 - eta) ^ 2 * w i ^ 2 := by
    intro i
    ring_nf
  have hper2 : ∀ i : Fin n, (w i - eta * w i) ^ 2 / 2
      = (1 - eta) ^ 2 * (w i ^ 2 / 2) := by
    intro i; ring
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper2 i)

/-- СТРОГИЙ СПУСК вычисляемой энергии: при η ∈ (0,2) и
ненулевых весах энергия строго убывает. -/
theorem growthQuad_descent {n : ℕ} (w : Fin n → ℝ) (eta : ℝ)
    (h0 : 0 < eta) (h2 : eta < 2)
    (hw : ∑ i, w i ^ 2 ≠ 0) :
    growthQuad (growthStep w eta) < growthQuad w := by
  rw [growthQuad_step]
  have hcoef : (1 - eta) ^ 2 < 1 := by
    have hnn : -1 < 1 - eta := by linarith
    have hle : 1 - eta < 1 := by linarith
    nlinarith [sq_nonneg (1 - eta), hnn, hle]
  have hpos : 0 < growthQuad w := growthQuad_pos_of_nonzero w hw
  have := mul_lt_mul_of_pos_right hcoef hpos
  linarith

/-- МОСТ-ТЕОРЕМА: в каноническом инстансе (измеренные поля =
вычисляемая энергия) h_emp_grow-посылка стадии grow ВЫВОДИТСЯ:
  growEnergy(после шага) ≤ S.energy − gain
при gain = (1 − (1−η)²)·E(w) > 0. Эмпирическая посылка
становится теоремой для квадратичного канонического
представителя измеряемой энергии. -/
theorem growEnergy_derived {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S : GrowthState X)
    (eta : ℝ) (h0 : 0 < eta) (h2 : eta < 2)
    (hw : ∑ i, S.weights i ^ 2 ≠ 0)
    (hcanon : S.energy = growthQuad S.weights)
    (hstep : S.effects.growEnergy
      = growthQuad (growthStep S.weights eta)) :
    S.effects.growEnergy ≤ S.energy
      - (1 - (1 - eta) ^ 2) * growthQuad S.weights
      ∧ 0 < (1 - (1 - eta) ^ 2) * growthQuad S.weights := by
  constructor
  · rw [hstep, hcanon]
    have hpos : (0:ℝ) < growthQuad S.weights :=
      growthQuad_pos_of_nonzero S.weights hw
    have hkey : growthQuad (growthStep S.weights eta)
        = growthQuad S.weights
          - (1 - (1 - eta) ^ 2) * growthQuad S.weights := by
      rw [growthQuad_step]
      ring
    rw [hkey]
  · -- gain > 0: (1−(1−η)²) > 0 и E > 0
    have hcoef : 0 < 1 - (1 - eta) ^ 2 := by
      have : (1 - eta) ^ 2 < 1 := by
        have hnn : -1 < 1 - eta := by linarith
        have hle : 1 - eta < 1 := by linarith
        nlinarith [sq_nonneg (1 - eta), hnn, hle]
      linarith
    have hpos : (0:ℝ) < growthQuad S.weights := by
      exact growthQuad_pos_of_nonzero S.weights hw
    exact mul_pos hcoef hpos

end Hagi.System.GrowthComputed
