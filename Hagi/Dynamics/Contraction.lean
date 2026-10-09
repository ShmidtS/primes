/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Foundations.Recurrence
set_option linter.style.header false

/-!
# Contraction — оператор поколения как контракция

При контракции `E (t+1) ≤ γ·E t + δ` с `γ < 1` (эмпирическая
ставка — посылка):

* `geom_sum_telescope` / `geom_sum_le_inv` — телескоп и
  оценка геометрической суммы (делегация Foundations);
* `contraction_limit`:
  `E t ≤ γ^t·E 0 + δ/(1−γ)` — экспоненциальный вход в шар
  радиуса δ/(1−γ). Метрико-абстрактная форма;
  Wasserstein/Fisher-формы — открыто.
-/

open Finset

namespace Hagi

/-- Телескопическое тождество:
`(1 − γ)·Σ_{i<t} γ^i = 1 − γ^t` (делегация Foundations). -/
theorem geom_sum_telescope (gamma : ℝ) (t : ℕ) :
    (1 - gamma) * ∑ i ∈ Finset.range t, gamma ^ i = 1 - gamma ^ t :=
  Hagi.Foundations.geom_telescope gamma t

/-- При `0 ≤ γ < 1` — `Σ_{i<t} γ^i ≤ 1/(1−γ)` (делегация
Foundations). -/
theorem geom_sum_le_inv (gamma : ℝ) (hg : 0 ≤ gamma) (hg1 : gamma < 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, gamma ^ i ≤ 1 / (1 - gamma) :=
  Hagi.Foundations.geom_sum_le_inv gamma t hg hg1

/-- При `0 ≤ γ < 1`, `0 ≤ δ` и `E (t+1) ≤ γ·E t + δ` —
`E t ≤ γ^t·E 0 + δ/(1−γ)` (делегация Foundations). -/
theorem contraction_limit (E : ℕ → ℝ) (gamma delta : ℝ)
    (hg : 0 ≤ gamma) (hg1 : gamma < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, E (t + 1) ≤ gamma * E t + delta) (t : ℕ) :
    E t ≤ gamma ^ t * E 0 + delta / (1 - gamma) :=
  Hagi.Foundations.contraction_limit gamma E delta t hg hg1 hdelta hstep

end Hagi
