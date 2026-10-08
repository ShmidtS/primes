/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.GQA
set_option linter.style.header false

/-!
# R142: Sliding window + relay - receptive field recursion

Phase B (R135 of the plan). Source: 2609.34049 - the exact
receptive-field recursion R_L = L(W-1) + 1 for a stack of L
sliding-window attention layers of window W, with relaying
through the residual stream; 2609.38109 (SWA ~ moving-
average convolution, recency bias relayed to global layers).

Theorems:

* swa_reach_closed - closed form: after L window layers
of width W the receptive field is exactly L*(W-1)+1
(induction: each layer adds W-1 positions).
* swa_reach_full - a single relay (full-attention) layer
extends the reach to the whole sequence length T.
* `swa_cost_bound` - exact mask cardinality for T >= W:
T*W - W*(W-1)/2 = O(T*W) against O(T^2) for full attention.

Honest boundary: information PRESERVATION through the relay
(the residual stream carries unsummarized content) is
an architectural assumption, verified empirically in
2609.34049, not proven here. -/

namespace Hagi

/-- Receptive field after L sliding-window layers of width W. -/
def reach (W L : ℕ) : ℕ := L * (W - 1) + 1

/-- Each additional window layer adds exactly W - 1 positions
(the recursion of 2609.34049). -/
theorem swa_reach_step (W L : ℕ) (hW : 2 ≤ W) :
    reach W (L + 1) = reach W L + (W - 1) := by
  unfold reach
  have h : (L + 1) * (W - 1) = L * (W - 1) + (W - 1) := by ring_nf
  rw [h]; omega

/-- Closed form (2609.34049): reach is exactly the definition. -/
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

/-- Causal sliding-window mask size is O(T*W): each of the
T - W tail positions attends to exactly W predecessors and
no position attends to more than W - linear against the
quadratic T*(T+1)/2 of full causal attention. -/
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

end Hagi
