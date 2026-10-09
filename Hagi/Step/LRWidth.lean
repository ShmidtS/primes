/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.ChunkedCE
set_option linter.style.header false

/-!
# LRWidth — неинвариантность LR по ширине и muP-скейлинг

Модель: линейный слой W (m строк) на квадратичной потере
`L = ½·‖W·1‖²`.

* `grad_norm_grows`: при all-ones инициализации квадрат
  нормы градиента равен `m·d³` — растёт линейно по ширине m
  (фиксированный LR не инвариантен по ширине);
* `mup_grad_invariant`: при скейлинге `W i j = 1/√m` квадрат
  нормы градиента равен `d³` — не зависит от ширины
  (muP-предписание для этого слоя).

Полный muP-перенос (все слои, моменты Adam) — эмпирический;
здесь — точное утверждение для квадратичной линейной модели.
-/

namespace Hagi
open Finset

/-- Компонент градиента потери `L = ½·Σ_i (Σ_j W i j)²`:
`gradEntry W i j = Σ_j' W i j'`. -/
def gradEntry {m d : ℕ} (W : Fin m → Fin d → ℝ) (i : Fin m) (j : Fin d) : ℝ :=
  ∑ j', W i j'

/-- При `Wones i j = 1` для всех i j:
`Σ_i Σ_j (gradEntry Wones i j)² = m·d³` — линейный рост
по m (фиксированный LR не инвариантен по ширине). -/
theorem grad_norm_grows (m d : ℕ)
    (Wones : Fin m → Fin d → ℝ) (hones : ∀ i j, Wones i j = 1) :
    ∑ i, ∑ j, (gradEntry Wones i j)^2 = (m : ℝ) * (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wones i j = (d : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hones i j']
    simp
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- При `1 ≤ m` и `Wmup i j = 1/√m` для всех i j:
`Σ_i Σ_j (gradEntry Wmup i j)² = d³` — не зависит от
ширины (muP-скейлинг). -/
theorem mup_grad_invariant (m d : ℕ) (hm : 1 ≤ m)
    (Wmup : Fin m → Fin d → ℝ)
    (hmup : ∀ i j, Wmup i j = 1 / Real.sqrt (m : ℝ)) :
    ∑ i, ∑ j, (gradEntry Wmup i j)^2 = (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wmup i j
      = (d : ℝ) / Real.sqrt (m : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hmup i j']
    rw [Finset.sum_const, Finset.card_univ]
    simp
    ring
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ]
  have hmpos : (0:ℝ) < (m : ℝ) := by positivity
  have hkey : ((d : ℝ) / Real.sqrt (m : ℝ))^2
      = (d : ℝ)^2 / (m : ℝ) := by
    have h1 : (Real.sqrt (m : ℝ))^2 = (m : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [div_pow, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hkey]
  simp
  field_simp
end Hagi
