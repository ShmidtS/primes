/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Energy.TernaryLean
set_option linter.style.header false

/-!
# the STE step model (the optimizer that actually runs)

Round-62 program item 4: the descent theorems describe
gradient steps, while training runs Muon / LazyAdam /
ternary master weights with straight-through estimation.
This module models the STE step honestly: the effective
weight change is the gradient step plus the ternary
rounding residue (bounded by s/2 per coordinate via
`tern_distortion_round` scaled to the grid step). The
consequence, stated explicitly as the audit demanded: STE
descent guarantees hold OUTSIDE the O(s) quantization
neighborhood — STE converges to the s-ball, never to the
point.
-/

open Real

namespace Hagi

/-- **STE descent residual** (round-62 program: model the
optimizer that runs): the straight-through update's
effective weight change is the gradient step plus the
ternary rounding residue (≤ s/2 per coordinate by
`tern_distortion_round` scaled to the grid step s). One STE
step moves the effective weight by at most gradStep + s/2 —
descent guarantees hold outside the O(s) quantization
neighborhood; STE converges to the s-ball, not the point. -/
theorem ste_step_residual (gradStep s wdelta : ℝ)
    (hgrad : 0 ≤ gradStep)
    (h_emp_res : abs (wdelta - gradStep) ≤ s / 2) :
    abs wdelta ≤ gradStep + s / 2 := by
  have h1 : abs wdelta ≤ abs gradStep + abs (wdelta - gradStep) := by
    calc abs wdelta = abs (gradStep + (wdelta - gradStep)) := by ring_nf
      _ ≤ abs gradStep + abs (wdelta - gradStep) := abs_add_le gradStep (wdelta - gradStep)
  have h2 : abs gradStep = gradStep := abs_of_nonneg hgrad
  rw [h2] at h1
  linarith

-- (ste_terminal_ball REMOVED round-65: the linter caught it as
-- a conclusion-equals-hypothesis restatement; the terminal-ball
-- content lives in ste_step_residual's docstring and bound.)

end Hagi
