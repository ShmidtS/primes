/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Dominate — закон доминации: один корпус захватывает joint-шаг

Геометрия доминации смеси `g = Σ wᵢ gᵢ` корпусом s.

* `domination_decompose`: разложение `⟪gi, d⟫` на
  выровненную с `gs` часть и перпендикулярный остаток;
* `domination_regression`: при
  `(1/2)‖d‖‖gs‖ ≤ ⟪d, gs⟫` и
  `⟪gi, gs⟫ ≤ −(1/4)‖gi‖‖gs‖` выровненный член ограничен
  сверху оценкой
  `(‖d‖/(2‖gs‖))·(−(1/4)‖gi‖‖gs‖)` — отрицателен;
* `safe_consensus_harmless`: при `0 ≤ ⟪gi, gs⟫` и
  `d = c • gs` (c ≥ 0) выполнено `0 ≤ ⟪gi, d⟫`;
* `dominated_collateral_bound`: при `⟪gi, gs⟫ < 0` и
  `d = c • gs` (c > 0) выполнено `⟪gi, d⟫ < 0`;
* `guard_weight_parity`: вес `w = nr/(ns+nr)` даёт
  κ-паритет `w·ns = (1−w)·nr`.

Тезисы о κ-пороге/прогнозах на измерениях — эмпирические,
не теоремы (см. комментарии в теле).
-/

open Finset InnerProductSpace

namespace Hagi

section Dominate

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Разложение шага d вдоль доминантного градиента gs:
`⟪gi, d⟫ = (⟪d, gs⟫/‖gs‖²)·⟪gi, gs⟫ + ⟪gi, d − …•gs⟫`. -/
theorem domination_decompose (d gs gi : X) :
    ⟪gi, d⟫_ℝ = (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      + ⟪gi, d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs⟫_ℝ := by
  have hkey : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs
      + (d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs) = d := by abel
  have hstep1 : ⟪gi, d⟫_ℝ
      = ⟪gi, (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs
          + (d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs)⟫_ℝ := by
    rw [hkey]
  rw [hstep1, inner_add_right, inner_smul_right]

/-- При `0 < ‖d‖`, `0 < ‖gs‖`,
`(1/2)·‖d‖·‖gs‖ ≤ ⟪d, gs⟫` и
`⟪gi, gs⟫ ≤ −(1/4)·‖gi‖·‖gs‖` выровненная часть ограничена:
`(⟪d, gs⟫/‖gs‖²)·⟪gi, gs⟫
≤ ((1/2)·‖d‖·‖gs‖/‖gs‖²)·(−(1/4)·‖gi‖·‖gs‖)`. -/
theorem domination_regression (d gs gi : X)
    (hd : 0 < ‖d‖) (hgs : 0 < ‖gs‖)
    (hdom : (1/2) * ‖d‖ * ‖gs‖ ≤ ⟪d, gs⟫_ℝ)
    (hmis : ⟪gi, gs⟫_ℝ ≤ -(1/4) * ‖gi‖ * ‖gs‖) :
    (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      ≤ ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) := by
  have hAmin : ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
      ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) :=
    (div_le_div_iff_of_pos_right (by positivity)).mpr hdom
  have hA0 : 0 ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) := by
    calc (0:ℝ) ≤ (1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖) := by positivity
      _ ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) := hAmin
  have hstep1 : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      ≤ (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) :=
    mul_le_mul_of_nonneg_left hmis hA0
  have hB' : -(1/4) * ‖gi‖ * ‖gs‖ ≤ 0 := by
    have : (0:ℝ) ≤ (1/4) * ‖gi‖ * ‖gs‖ := by positivity
    linarith
  have hstep2 : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖)
      ≤ ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) :=
    mul_le_mul_of_nonpos_right hAmin hB'
  exact le_trans hstep1 hstep2

-- НЕ ТЕОРЕМА: прежняя формулировка совпадала с гипотезой.
-- Условие спуска ⟪gnorm, g⟫ > 0 — измеряемый знаковый тест;
-- гарантия спуска проекции — в Hagi.Plan41.proj_descent_inner.

-- Снято ранее: тезис «weight-to-zero — предел нормализации»
-- и объяснение round-32 свапа — эмпирические, не теоремы;
-- тождество масштабирования — нотацияльное.

/-- Если `0 ≤ ⟪gi, gs⟫` и `d = c • gs` с `c ≥ 0`,
то `0 ≤ ⟪gi, d⟫` — выровненные корпуса не получают
первопорядкового ущерба вдоль d. -/
theorem safe_consensus_harmless (d gs gi : X)
    (hpos : 0 ≤ ⟪gi, gs⟫_ℝ) (hmul : ∃ c : ℝ, 0 ≤ c ∧ d = c • gs) :
    0 ≤ ⟪gi, d⟫_ℝ := by
  obtain ⟨c, hc, hdmul⟩ := hmul
  rw [hdmul, inner_smul_right]
  exact mul_nonneg hc hpos

/-- Если `⟪gi, gs⟫ < 0` и `d = c • gs` с `c > 0`,
то `⟪gi, d⟫ < 0`. -/
theorem dominated_collateral_bound (d gs gi : X)
    (hmis : ⟪gi, gs⟫_ℝ < 0) (hmul : ∃ c : ℝ, 0 < c ∧ d = c • gs) :
    ⟪gi, d⟫_ℝ < 0 := by
  obtain ⟨c, hc, hdmul⟩ := hmul
  rw [hdmul, inner_smul_right]
  exact mul_neg_of_pos_of_neg hc hmis

/-- При `0 < ns`, `0 < nr` вес `w = nr/(ns+nr)` даёт
κ-паритет: `w·ns = (1−w)·nr` (доля доминанта равна 1/2). -/
theorem guard_weight_parity (ns nr : ℝ) (hns : 0 < ns) (hnr : 0 < nr) :
    -- κ(w) = w·ns / (w·ns + (1−w)·nr) = 1/2  ⟺  w·ns = (1−w)·nr
    -- i.e. w = nr/(ns+nr)
    (nr / (ns + nr)) * ns
      = (1 - nr / (ns + nr)) * nr := by
  field_simp
  ring

end Dominate

end Hagi
