/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# IntegrationOrder — the exchange argument for expert order

The algorithmic side of integration: in WHAT ORDER should
experts be integrated? The exchange argument, in its honest
additive form (net gains g_i = twoGap_i − price_i, the
R211 gate evaluated per expert):

* `sum_perm_invariant`: under ADDITIVE net gains the total
  is invariant under the integration order — no sequencing
  trick creates value (the MOPD finding restated: order is
  not where the gain lives);
* `negative_expert_hurts_any_order`: an expert with negative
  net gain (incompatible: D_policy above cap, or price above
  gap) lowers the total in EVERY position — exclusion is
  order-independent;
* `positive_selection_dominates`: integrating exactly the
  positive-net experts dominates any selection that includes
  a negative one — greedy-by-net-gain is optimal in the
  additive regime; the order inside the positive set is free.

Honest boundary: the additive regime is the LOCAL view (one
macro-cycle, no cross-expert interference through the shared
cortex). Cross-terms (fiber overlap, cortex contention) are
exactly where order could matter — that regime is NOT
claimed here.
-/

namespace Hagi

open Finset

/-- **Order invariance (additive regime)**: the total net
gain does not depend on the integration order. -/
theorem sum_perm_invariant {N : ℕ} (g : Fin N → ℝ)
    (σ : Fin N ≃ Fin N) :
    ∑ i, g i = ∑ i, g (σ i) :=
  (Fintype.sum_equiv σ _ _ fun _ => rfl).symm

/-- **A negative expert hurts in any position**: including
an expert with negative net gain lowers the total — no
sequencing rescues an incompatible expert. -/
theorem negative_expert_hurts_any_order {N : ℕ}
    (g : Fin N → ℝ) (i : Fin N) (hg : g i < 0) :
    ∑ j : Fin N, g j
      < ∑ j ∈ Finset.univ.erase i, g j := by
  have h := Finset.sum_erase_add
    (Finset.univ : Finset (Fin N)) g (Finset.mem_univ i)
  rw [← h]
  linarith

/-- **Greedy-by-net-gain dominates**: any selection
containing a negative-net expert is dominated by the
selection excluding it — in the additive regime the optimal
selection is exactly the positive-net set, and the order
inside it is free. -/
theorem positive_selection_dominates {N : ℕ}
    (g : Fin N → ℝ) (s : Finset (Fin N))
    (i : Fin N) (hi : i ∈ s) (hg : g i < 0) :
    ∑ j ∈ s, g j < ∑ j ∈ s.erase i, g j := by
  have h := Finset.sum_erase_add s g hi
  rw [← h]
  linarith

end Hagi
