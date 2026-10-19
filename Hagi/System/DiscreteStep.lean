/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Energy.Quantizer
import Hagi.Foundations.Telescope

set_option linter.style.header false

/-!
# System.DiscreteStep — квантованный шаг спуска

Четвёртый компонент единого ядра: динамический шаг с
квантованием. Реальная система обновляет состояние
`x (t+1) = Q_Δ (x t − γ · g t)` (решётка `Δℤ` — см.
`Hagi.Energy.Quantizer`), и ошибка квантования `≤ Δ/2`
на каждом шаге входит в ляпуновский телескоп
(`lyapunov_gain_noise`) как аддитивный шум. Итог —
сертификат горизонта `T` с явной ценой квантования
`T · Δ / 2`.
-/

namespace Hagi.System

/-- **Сертификат квантованного спуска**: если фактическая
динамика на каждом шаге (`t < T`) равна квантованному шагу
`x (t+1) = Q_Δ (x t − γ · g t)` с шагом сетки `Δ > 0`, то

  `x T ≤ x 0 − Σ t < T, γ · g t + T · Δ / 2`.

Единственная содержательная гипотеза — уравнение шага
(как обновляет себя система); всё остальное — универсальные
свойства квантователя (`gridQ_error`) и точный телескоп
(`lyapunov_gain_noise`). Цена квантования — ровно `Δ / 2`
за шаг, без скрытых констант. -/
theorem quantized_descent_telescope (x g : ℕ → ℝ) (Δ γ : ℝ)
    (hΔ : 0 < Δ) (T : ℕ)
    (hstep : ∀ t < T, x (t + 1) = Hagi.Energy.gridQ Δ hΔ (x t - γ * g t)) :
    x T ≤ x 0 - (∑ t ∈ Finset.range T, γ * g t)
      + (T : ℝ) * Δ / 2 := by
  classical
  -- per-step: квантование портит шаг не более чем на Δ/2
  have hnoise : ∀ t < T,
      x (t + 1) ≤ x t - γ * g t + Δ / 2 := by
    intro t ht
    rw [hstep t ht]
    have hq := Hagi.Energy.gridQ_error Δ hΔ (x t - γ * g t)
    rw [abs_le] at hq
    linarith [hq]
  -- телескоп с gain t = γ * g t, noise t = Δ / 2
  have htel := lyapunov_gain_noise (V := x) (gain := fun t => γ * g t)
    (noise := fun _ => Δ / 2) hnoise
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at htel
  linarith [htel]

end Hagi.System
