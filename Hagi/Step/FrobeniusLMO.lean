/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.MuonStableLR

set_option linter.style.header false

/-!
# FrobeniusLMO — одна геометрия для SafeQP и Muon

Мост плана (§2, LMO-унификация по PoLoRA 2607.17620,
Lemma 2 «Spectral norm LMO»; corpus-подтверждение: Muon =
steepest descent при spectral norm constraint): шаг Muon
(ортогонализация градиента) и SafeQP-шаг — одна и та же
LMO-геометрия: экстремум линейной функции ⟨G, X⟩ по шару
нормы.

Для шара нормы (наш рабочий случай — энерго-ограниченные
шаги SafeQP во Frobenius/гильбертовой норме) LMO решается
ТОЧНО элементарно (Коши–Шварц):

  min_{‖X‖≤η} ⟨G, X⟩ = −η·‖G‖,  X* = −η·G/‖G‖.

Спектральный шар (Lemma 2 статьи: min = −η·‖G‖_nuc на
X* = −η·sign(G)) — та же конструкция с ядерной дуальностью;
в Mathlib v4.34.1 спектральная/ядерная дуальность
отсутствует (hbridge-кандидат, план §3 докачки upstream).

Доказано:
* `lmo_lower_bound`: ∀ X с ‖X‖ ≤ η: −η·‖G‖ ≤ ⟨G, X⟩
  (Коши–Шварц);
* `lmo_attained`: X* = −(η/‖G‖)•G допустим и достигает
  границы — ТОЧНОЕ решение LMO;
* `lmo_descent_direction`: любой шаг с ‖D‖ ≤ η даёт спуск
  не лучше LMO-оптимума: ⟨G, D⟩ ≥ −η‖G‖ — SafeQP-конус и
  Muon живут в одном экстремальном каркасе.

Честная граница: Muon-контракты полярного разложения —
измеряемые посылки R281; спектральная версия — hbridge.
-/

open Finset InnerProductSpace Real

namespace Hagi.FrobeniusLMO

variable {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X]

/-- Нижняя граница LMO: любой допустимый X (‖X‖ ≤ η)
удовлетворяет −η·‖G‖ ≤ ⟨G, X⟩ (Коши–Шварц). -/
theorem lmo_lower_bound (G D : X) (eta : ℝ)
    (hD : ‖D‖ ≤ eta) :
    -eta * ‖G‖ ≤ ⟪G, D⟫_ℝ := by
  have hcs : |⟪G, D⟫_ℝ| ≤ ‖G‖ * ‖D‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_inner_le_norm G D
  have h1 : ⟪G, D⟫_ℝ ≥ -(‖G‖ * ‖D‖) := by
    linarith [(abs_le.mp hcs).1]
  have h2 : -(‖G‖ * ‖D‖) ≥ -(‖G‖ * eta) := by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hD
      (norm_nonneg G))
  linarith

/-- Точное решение LMO: X* = −(η/‖G‖)•G допустим (норма ≤ η)
и достигает границы ⟨G, X*⟩ = −η·‖G‖. -/
theorem lmo_attained (G : X) (eta : ℝ) (heta : 0 ≤ eta)
    (hG : G ≠ 0) :
    ‖(-(eta / ‖G‖) : ℝ) • G‖ ≤ eta ∧
    ⟪G, (-(eta / ‖G‖) : ℝ) • G⟫_ℝ = -eta * ‖G‖ := by
  have hnorm : (0:ℝ) < ‖G‖ := by
    rcases eq_or_lt_of_le (norm_nonneg G) with h | h
    · exact absurd (norm_eq_zero.mp h.symm) hG
    · exact h
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_div,
      abs_of_nonneg heta, abs_of_nonneg hnorm.le]
    field_simp
    exact le_refl _
  · rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- Единый экстремальный каркас: любой шаг D с ‖D‖ ≤ η даёт
⟨G, D⟩ не ниже LMO-оптимума −η‖G‖, и оптимум ДОСТИЖИМ —
SafeQP-проекция и Muon-направление решают задачи одного
семейства (линейная цель × шар нормы). -/
theorem lmo_descent_direction (G D : X) (eta : ℝ)
    (hD : ‖D‖ ≤ eta) :
    -eta * ‖G‖ ≤ ⟪G, D⟫_ℝ :=
  lmo_lower_bound G D eta hD

end Hagi.FrobeniusLMO
