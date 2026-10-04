/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.SWA
set_option linter.style.header false

/-!
# R143: causal transmit filter - zero future leakage under left pad

Phase B (R136 of the plan; lesson V26). Sources: 2607.20125
(block-causal mask "blocks leakage from future frames"),
2609.14191 (leakage-test template: the STANDARD mask lets
same-step neighbors through), 2609.34475 (PAD discipline:
average only over non-padding entries).

Model: causal convolution with LEFT padding -
y t = sum_{i <= t} w (t - i) * x i: the output at t is a
function of the prefix x 0..t ONLY.

Theorems:

* `causal_prefix_determined` - if two inputs agree on the
prefix 0..t then the outputs agree at t: ZERO future
leakage (the formal content of the left-pad discipline).
* `leak_same_step` - COUNTEREXAMPLE: a centered (same)
convolution y t = ... + w 0 * x (t+1) + ... DOES leak:
changing x (t+1) alone changes the output at t.

This pins lesson V26 against regressions. -/

namespace Hagi
open Finset

/-- Causal convolution with left padding: the output at t
depends only on the prefix x 0..t. -/
def causalConv (w x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), w (t - i) * x i

/-- ZERO FUTURE LEAKAGE: if two inputs agree on the prefix
0..t, the causal outputs agree at t. -/
theorem causal_prefix_determined (w x y : ℕ → ℝ) (t : ℕ)
    (hagree : ∀ i ≤ t, x i = y i) :
    causalConv w x t = causalConv w y t := by
  unfold causalConv
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have : x i = y i := hagree i (by omega)
  rw [this]

/-- Centered convolution reads one step AHEAD (the standard
mask leaking same-step neighbors, 2609.14191). -/
def centeredConv (w x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 2), w (t + 1 - i) * x i

/-- COUNTEREXAMPLE: the centered form DOES leak the future -
changing x (t+1) alone changes the output at t by w 0 * c. -/
theorem leak_same_step (w x : ℕ → ℝ) (t : ℕ) (hw : w 0 ≠ 0)
    (c : ℝ) :
    centeredConv w (fun i => if i = t + 1 then x i + c else x i) t
      = centeredConv w x t + w 0 * c := by
  unfold centeredConv
  have key : ∀ i ∈ Finset.range (t + 2),
      w (t + 1 - i) * (if i = t + 1 then x i + c else x i)
      = w (t + 1 - i) * x i
        + (if i = t + 1 then w 0 * c else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    by_cases h : i = t + 1
    · subst h
      rw [if_pos rfl, if_pos rfl, Nat.sub_self]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have hlast : ∑ x ∈ Finset.range (t + 2),
      (if x = t + 1 then w 0 * c else 0) = w 0 * c := by
    rw [Finset.sum_eq_single (t + 1)]
    · rw [if_pos rfl]
    · intro b hb hne
      rw [if_neg hne]
    · intro hcon
      exfalso
      simp only [Finset.mem_range] at hcon
      omega
  rw [hlast]

end Hagi
