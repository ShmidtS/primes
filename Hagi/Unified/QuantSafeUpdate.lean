/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.LiveDeltaSafe

set_option linter.style.header false

/-!
# QuantSafeUpdate — квантованное безопасное обновление

Композиция окна LiveDeltaSafe с квантованием (мост к
Runtime/LiveDeltaQuant и бюджету R272): реальный шаг несёт
ошибку реализации δ (квантование факторов, ранг-аппроксимация,
транспорт) с известной нормой ‖δ‖ ≤ q. Тогда линейная оценка
изменения потерь сдвигается на ЯВНУЮ цену квантования:

  dL' ≤ −η⟪g, d+δ⟫ + L·η²‖d+δ‖²/2
      ≤ [оценка идеального окна] + η·‖g‖·q
        + L·η²·(‖d‖·q + q²/2).

Доказано:
* `quantized_step_bound`: точная верхняя граница оценки
  потерь для возмущённого шага d+δ через идеальную и
  q-члены;
* `quantized_safe_window`: если идеальный шаг укладывается в
  окно ε, возмущённый укладывается в ε + цена квантования
  (η‖g i‖q + L i η²(‖d‖q + q²/2)).

Честная граница: q — измеряемый контракт реализации
(например, из quantMat_sq_bound); формализована арифметика
допуска, не сама оценка q.
-/

open Finset InnerProductSpace Real

namespace Hagi.QuantSafeUpdate

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Возмущённый шаг: направление d плюс ошибка реализации δ
с нормой ≤ q. -/
theorem quantized_step_bound (g : K → X) (d δ : X)
    (L : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 ≤ L i) (heta : 0 ≤ eta)
    (i : K) :
    -eta * ⟪g i, d + δ⟫_ℝ
        + L i * eta * eta * ‖d + δ‖ ^ 2 / 2
      ≤ (-eta * ⟪g i, d⟫_ℝ
          + L i * eta * eta * ‖d‖ ^ 2 / 2)
        + eta * ‖g i‖ * ‖δ‖
        + L i * eta * eta * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2) := by
  have habs : |⟪g i, δ⟫_ℝ| ≤ ‖g i‖ * ‖δ‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_inner_le_norm (g i) δ
  have hge : ⟪g i, δ⟫_ℝ ≤ ‖g i‖ * ‖δ‖ := by
    linarith [(abs_le.mp habs).2]
  have hge' : -‖g i‖ * ‖δ‖ ≤ ⟪g i, δ⟫_ℝ := by
    linarith [(abs_le.mp habs).1]
  have htri : ‖d + δ‖ ≤ ‖d‖ + ‖δ‖ := norm_add_le d δ
  have hnn : 0 ≤ ‖d + δ‖ := norm_nonneg _
  have hnd : 0 ≤ ‖d‖ := norm_nonneg d
  have hne : 0 ≤ ‖δ‖ := norm_nonneg δ
  have hng : 0 ≤ ‖g i‖ := norm_nonneg (g i)
  have hsq : ‖d + δ‖ ^ 2
      ≤ ‖d‖ ^ 2 + 2 * (‖d‖ * ‖δ‖) + ‖δ‖ ^ 2 := by
    nlinarith [htri, hnn, hnd, hne]
  rw [inner_add_right]
  have hlin : eta * ⟪g i, δ⟫_ℝ ≤ eta * (‖g i‖ * ‖δ‖) :=
    mul_le_mul_of_nonneg_left hge heta
  have hLe : 0 ≤ L i * eta * eta :=
    mul_nonneg (mul_nonneg (hL i) heta) heta
  have hprod : L i * eta * eta * ‖d + δ‖ ^ 2
      ≤ L i * eta * eta
        * (‖d‖ ^ 2 + 2 * (‖d‖ * ‖δ‖) + ‖δ‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hsq hLe
  have hhalf : L i * eta * eta
        * (‖d‖ ^ 2 + 2 * (‖d‖ * ‖δ‖) + ‖δ‖ ^ 2) / 2
      = L i * eta * eta * ‖d‖ ^ 2 / 2
        + L i * eta * eta * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2) := by
    field_simp
    ring
  nlinarith [hlin, hprod, hhalf, hge', hng, hne, hnd, heta,
    hL i]

/-- Квантованное безопасное окно: если ИДЕАЛЬНЫЙ шаг
направления d укладывается в окно ε (линейная оценка), а
реальный шаг — возмущённый d+δ с ‖δ‖ ≤ q, то возмущённая
оценка потерь ≤ ε + цена квантования
η·‖g i‖·q + L i·η²·(‖d‖·q + q²/2) по каждому домену. -/
theorem quantized_safe_window (g : K → X) (eps L : K → ℝ)
    (d δ : X) (dL : K → ℝ) (eta q : ℝ)
    (hL : ∀ i, 0 ≤ L i) (heps : ∀ i, 0 ≤ eps i)
    (heta : 0 ≤ eta)
    (h_ideal : ∀ i, -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2 ≤ eps i)
    (hq : ‖δ‖ ≤ q)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d + δ⟫_ℝ
      + L i * eta * eta * ‖d + δ‖ ^ 2 / 2) :
    ∀ i, dL i ≤ eps i
      + eta * ‖g i‖ * q
      + L i * eta * eta * (‖d‖ * q + q ^ 2 / 2) := by
  intro i
  refine le_trans (h_lipline i) ?_
  refine le_trans (quantized_step_bound g d δ L eta hL heta i)
    ?_
  have hq2 : 0 ≤ q := le_trans (norm_nonneg δ) hq
  have hLe : 0 ≤ L i * eta * eta :=
    mul_nonneg (mul_nonneg (hL i) heta) heta
  have heg : 0 ≤ eta * ‖g i‖ := mul_nonneg heta (norm_nonneg _)
  have hA : eta * ‖g i‖ * ‖δ‖ ≤ eta * ‖g i‖ * q :=
    mul_le_mul_of_nonneg_left hq heg
  have hdd : ‖d‖ * ‖δ‖ ≤ ‖d‖ * q :=
    mul_le_mul_of_nonneg_left hq (norm_nonneg d)
  have hB : L i * eta * eta * (‖d‖ * ‖δ‖)
      ≤ L i * eta * eta * (‖d‖ * q) :=
    mul_le_mul_of_nonneg_left hdd hLe
  have hC : ‖δ‖ ^ 2 ≤ q ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg δ) hq
    nlinarith [h]
  have hD : L i * eta * eta * (‖δ‖ ^ 2 / 2)
      ≤ L i * eta * eta * (q ^ 2 / 2) := by
    nlinarith [hC, hLe]
  have hE1 : L i * eta * eta * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2)
      = L i * eta * eta * (‖d‖ * ‖δ‖)
        + L i * eta * eta * (‖δ‖ ^ 2 / 2) := by ring
  have hE2 : L i * eta * eta * (‖d‖ * q + q ^ 2 / 2)
      = L i * eta * eta * (‖d‖ * q)
        + L i * eta * eta * (q ^ 2 / 2) := by ring
  have hsum1 : eta * ‖g i‖ * ‖δ‖ + L i * eta * eta
        * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2)
      ≤ eta * ‖g i‖ * q + L i * eta * eta
        * (‖d‖ * q + q ^ 2 / 2) := by
    rw [hE1, hE2]
    exact add_le_add hA (add_le_add hB hD)
  calc (-eta * ⟪g i, d⟫_ℝ + L i * eta * eta * ‖d‖ ^ 2 / 2)
        + eta * ‖g i‖ * ‖δ‖
        + L i * eta * eta * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2)
      ≤ eps i + eta * ‖g i‖ * ‖δ‖
        + L i * eta * eta * (‖d‖ * ‖δ‖ + ‖δ‖ ^ 2 / 2) := by
        linarith [h_ideal i]
    _ ≤ eps i + eta * ‖g i‖ * q
        + L i * eta * eta * (‖d‖ * q + q ^ 2 / 2) := by
        linarith [hsum1]

end Hagi.QuantSafeUpdate
