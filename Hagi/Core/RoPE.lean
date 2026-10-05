/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R140: RoPE - rotary kernel depends only on relative position

Phase B (R133 of the plan). Sources: 2607.18759
(offset-equivariance + position-pinning counterexample),
2609.30576 (T-RoPE), 2609.33804 (group-representation limit),
2609.39604 (1D-RoPE loses 2D neighborhood).

Main theorem: rope_score_delta - rotary score
depends ONLY on the position difference. -/

open Finset

namespace Hagi

variable {d : ℕ}

/-- Rotary code: rotate the j-th pair by angle theta_j * m. -/
noncomputable def rotVec (θ : Fin d → ℝ) (m : ℕ) (x : Fin d → ℝ × ℝ) :
    Fin d → ℝ × ℝ :=
  fun j =>
    (Real.cos (θ j * m) * (x j).1 - Real.sin (θ j * m) * (x j).2,
     Real.sin (θ j * m) * (x j).1 + Real.cos (θ j * m) * (x j).2)

/-- Pairwise-block inner product. -/
def pairInner (x y : Fin d → ℝ × ℝ) : ℝ :=
  ∑ j, ((x j).1 * (y j).1 + (x j).2 * (y j).2)

/-- Rotation preserves the pairwise-block norm (unitarity). -/
theorem rot_norm (θ : Fin d → ℝ) (m : ℕ) (x : Fin d → ℝ × ℝ) :
    pairInner (rotVec θ m x) (rotVec θ m x) = pairInner x x := by
  unfold pairInner rotVec
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := Real.cos_sq_add_sin_sq (θ j * m)
  nlinarith [h]

/-- MAIN (offset-equivariance, 2607.18759): the rotary score
⟨rotVec θ m x, rotVec θ n y⟩ equals ⟨x, rotVec θ (n-m) y⟩ --
it depends ONLY on the position difference n - m. -/
theorem rope_score_delta (θ : Fin d → ℝ) (m n : ℕ) (hmn : m ≤ n)
    (x y : Fin d → ℝ × ℝ) :
    pairInner (rotVec θ m x) (rotVec θ n y)
      = pairInner x (rotVec θ (n - m) y) := by
  unfold pairInner rotVec
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : Real.cos (θ j * n - θ j * m)
      = Real.cos (θ j * n) * Real.cos (θ j * m)
        + Real.sin (θ j * n) * Real.sin (θ j * m) := Real.cos_sub _ _
  have hs : Real.sin (θ j * n - θ j * m)
      = Real.sin (θ j * n) * Real.cos (θ j * m)
        - Real.cos (θ j * n) * Real.sin (θ j * m) := Real.sin_sub _ _
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) :=
    Nat.cast_sub hmn
  rw [hcast]
  simp only [mul_sub, hc, hs]
  ring

/-- Shifting both positions by k leaves the rotary score
unchanged (special case of the delta form). -/
theorem rope_translation_shift (θ : Fin d → ℝ) (m n k : ℕ) (hmn : m ≤ n)
    (x y : Fin d → ℝ × ℝ) :
    pairInner (rotVec θ (m + k) x) (rotVec θ (n + k) y)
      = pairInner (rotVec θ m x) (rotVec θ n y) := by
  rw [rope_score_delta θ (m + k) (n + k) (by omega),
      rope_score_delta θ m n hmn]
  congr 2
  omega

end Hagi
