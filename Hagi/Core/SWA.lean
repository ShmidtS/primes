/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.GQA
set_option linter.style.header false

/-!
# Sliding window + relay: receptive-field recursion

* `swa_reach_step`, `swa_reach_eq`, `swa_reach_mono` — the
  recursion `reach W (L + 1) = reach W L + (W - 1)` (for `2 ≤ W`)
  and its closed form `reach W L = L * (W - 1) + 1`.
  (source: 2609.34049)
* `swa_relay_full` — a single full-width layer covers the entire
  context: `reach T 1 = T`.
* `swa_cost_bound` — the causal sliding-window mask size is
  between `(T - W) * W` and `T * W` for `W ≤ T`.

Information preservation through the relay is an architectural
assumption, not proven here. -/

namespace Hagi.Core

/-- Receptive field after L sliding-window layers of width W. -/
def reach (W L : ℕ) : ℕ := L * (W - 1) + 1

/-- For `2 ≤ W`, each additional window layer adds exactly
`W - 1` positions. -/
theorem swa_reach_step (W L : ℕ) (hW : 2 ≤ W) :
    reach W (L + 1) = reach W L + (W - 1) := by
  unfold reach
  have h : (L + 1) * (W - 1) = L * (W - 1) + (W - 1) := by ring_nf
  rw [h]; omega

/-- Closed form: `reach W L = L * (W - 1) + 1`. -/
theorem swa_reach_eq (W L : ℕ) : reach W L = L * (W - 1) + 1 := rfl

/-- Monotonicity: more layers never shrink the reach. -/
theorem swa_reach_mono (W L : ℕ) (hW : 2 ≤ W) :
    reach W L ≤ reach W (L + 1) := by
  rw [swa_reach_step W L hW]; omega

/-- A relay layer is a full-attention layer - a window of the
whole length T: it alone covers the entire context. -/
theorem swa_relay_full (T : ℕ) (hT : 1 ≤ T) : reach T 1 = T := by
  unfold reach
  omega

/-- For `1 ≤ W` and `W ≤ T`, the sliding-window mask size
`∑ t < T, min (t + 1) W` lies between `(T - W) * W` and `T * W`:
no position attends to more than `W` predecessors. -/
theorem swa_cost_bound (T W : ℕ) (hW : 1 ≤ W) (hTW : W ≤ T) :
    (T - W) * W ≤ ∑ t ∈ Finset.range T, min (t + 1) W
      ∧ ∑ t ∈ Finset.range T, min (t + 1) W ≤ T * W := by
  constructor
  · -- split: range T = range W ∪ Ico W T (disjoint)
    have hsplit : Finset.range T
        = Finset.range W ∪ Finset.Ico W T := by
      ext t
      simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.range W) (Finset.Ico W T) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_Ico] at hb
      omega
    -- on Ico W T each term is exactly W
    have hico : ∑ t ∈ Finset.Ico W T, min (t + 1) W
        = (T - W) * W := by
      have h1 : ∑ t ∈ Finset.Ico W T, min (t + 1) W
          = ∑ t ∈ Finset.Ico W T, W := by
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_Ico] at ht
        have hw : W ≤ t + 1 := by omega
        simp only [min_eq_right hw]
      rw [h1, Finset.sum_Ico_eq_sum_range (fun _ => W),
        Finset.sum_const, Finset.card_range]
      simp
    -- head sum is nonnegative (Nat)
    have hle : (T - W) * W
        ≤ ∑ t ∈ Finset.range W, min (t + 1) W
          + ∑ t ∈ Finset.Ico W T, min (t + 1) W := by
      have h0 : 0 ≤ ∑ t ∈ Finset.range W, min (t + 1) W :=
        Nat.zero_le _
      omega
    rw [hsplit, Finset.sum_union hdisj, hico]
    omega
  · calc ∑ t ∈ Finset.range T, min (t + 1) W
          ≤ ∑ _ ∈ Finset.range T, W :=
        Finset.sum_le_sum fun t _ => Nat.min_le_right (t + 1) W
      _ = T * W := by
          rw [Finset.sum_const, Finset.card_range]
          simp

end Hagi.Core

namespace Hagi
export Hagi.Core (reach swa_reach_step swa_reach_eq swa_reach_mono swa_relay_full swa_cost_bound)
end Hagi
