/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# IntegrationOrder — аргумент обмена для порядка интеграции экспертов

В аддитивном режиме (чистые выигрыши `g i = twoGap i − price i`, без
кросс-членов между экспертами):

* `sum_perm_invariant`: `Σ g i` инвариантен относительно
  перестановки `σ`;
* `negative_expert_hurts_any_order`: если `g i < 0`, то сумма
  над `univ.erase i` строго больше полной суммы;
* `positive_selection_dominates`: если `i ∈ s` и `g i < 0`, то
  сумма над `s.erase i` строго больше суммы над `s`.

Кросс-члены (перекрытие fiber, конкуренция за cortex) не
рассматриваются.
-/

namespace Hagi.Growth

open Finset

/-- `∑ i, g i = ∑ i, g (σ i)` для любой перестановки `σ`. -/
theorem sum_perm_invariant {N : ℕ} (g : Fin N → ℝ)
    (σ : Fin N ≃ Fin N) :
    ∑ i, g i = ∑ i, g (σ i) :=
  (Fintype.sum_equiv σ _ _ fun _ => rfl).symm

/-- Если `g i < 0`, то `∑ j ∈ univ.erase i, g j > ∑ j, g j`. -/
theorem negative_expert_hurts_any_order {N : ℕ}
    (g : Fin N → ℝ) (i : Fin N) (hg : g i < 0) :
    ∑ j : Fin N, g j
      < ∑ j ∈ Finset.univ.erase i, g j := by
  have h := Finset.sum_erase_add
    (Finset.univ : Finset (Fin N)) g (Finset.mem_univ i)
  rw [← h]
  linarith

/-- Если `i ∈ s` и `g i < 0`, то
`∑ j ∈ s.erase i, g j > ∑ j ∈ s, g j`. -/
theorem positive_selection_dominates {N : ℕ}
    (g : Fin N → ℝ) (s : Finset (Fin N))
    (i : Fin N) (hi : i ∈ s) (hg : g i < 0) :
    ∑ j ∈ s, g j < ∑ j ∈ s.erase i, g j := by
  have h := Finset.sum_erase_add s g hi
  rw [← h]
  linarith

end Hagi.Growth

namespace Hagi
export Hagi.Growth (sum_perm_invariant negative_expert_hurts_any_order positive_selection_dominates)
end Hagi
