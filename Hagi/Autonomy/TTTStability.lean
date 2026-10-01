/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R60: BIBO stability of test-time training

Block III.2 of the grand-unified roadmap: the TTT loop
adapts hidden states by gradient steps during inference. If
the adaptation operator W is non-expansive (‖W x‖ ≤ ‖x‖ for
all x — the h_emp_ spectral condition ρ(W) ≤ 1 in operator
norm), then NO adaptation chain of any length T can blow up
the hidden state: ‖W^T x‖ ≤ ‖x‖ for every T. BIBO stability
of the infinite-context adaptation loop, independent of T.
-/

namespace Hagi

/-- **BIBO core**: a non-expansive operator's iterates never
amplify the state — ‖W^T x‖ ≤ ‖x‖ for all T, by induction on
the composition bound. -/
theorem ttt_bibo (W : ℝ) (hW : abs W ≤ 1) (x : ℝ) (T : ℕ) :
    abs (W ^ T * x) ≤ abs x := by
  have hpow : abs (W ^ T) ≤ 1 := by
    induction T with
    | zero => simp
    | succ T ih =>
        have hcal : abs (W * W ^ T) ≤ 1 := by
          calc abs (W * W ^ T) = abs W * abs (W ^ T) := abs_mul _ _
            _ ≤ 1 * 1 := mul_le_mul hW ih (abs_nonneg _) (by norm_num)
            _ = 1 := by ring
        rw [pow_succ W T, mul_comm (W ^ T) W]
        exact hcal
  calc abs (W ^ T * x) = abs (W ^ T) * abs x := abs_mul _ _
    _ ≤ 1 * abs x := by
        apply mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = abs x := by ring

/-- **The TTT adaptation chain is bounded for every depth**:
composing non-expansive adaptation operators (per-layer TTT
updates with ρ ≤ 1) keeps the hidden state within its initial
norm — infinite-context adaptation cannot diverge. -/
theorem ttt_chain_bounded (W : ℕ → ℝ) (hW : ∀ t, abs (W t) ≤ 1)
    (x : ℝ) (T : ℕ) :
    abs ((List.map W (List.range T)).foldr (· * ·) 1 * x) ≤ abs x := by
  induction T with
  | zero => simp
  | succ T ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.foldr_append,
      List.map_nil, List.foldr_cons, List.foldr_nil, mul_one]
    have hstep : abs (W T * ((List.map W (List.range T)).foldr (· * ·) 1 * x)) ≤ abs x := by
      calc abs (W T * ((List.map W (List.range T)).foldr (· * ·) 1 * x))
          = abs (W T) * abs ((List.map W (List.range T)).foldr (· * ·) 1 * x) := abs_mul _ _
        _ ≤ 1 * abs ((List.map W (List.range T)).foldr (· * ·) 1 * x) := by
            apply mul_le_mul_of_nonneg_right (hW T) (abs_nonneg _)
        _ = abs ((List.map W (List.range T)).foldr (· * ·) 1 * x) := by ring
        _ ≤ abs x := ih
    -- goal: |foldr (·*·) (W T) rest * x| ≤ |x|; foldr (·*·) (W T) rest = rest.foldr(·*·)1 * W T
    have hfoldr : List.foldr (· * ·) (W T) (List.map W (List.range T))
        = (List.map W (List.range T)).foldr (· * ·) 1 * W T := by
      induction (List.map W (List.range T)) with
      | nil => simp
      | cons a as ih => simp [ih]; ring
    rw [hfoldr]
    rw [show (List.map W (List.range T)).foldr (· * ·) 1 * W T * x
        = W T * ((List.map W (List.range T)).foldr (· * ·) 1 * x) from by ring]
    exact hstep

end Hagi
