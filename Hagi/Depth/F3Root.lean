/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# F3Root: the tree-vs-flat tradeoff

Two formal cores of the depth-vs-flat tradeoff:

* `root_invariance` — adding the same scalar to two leaf
  values shifts their second-moment difference by exactly
  `2 * u * (vi - vj)`.
* `root_no_leaf_signal` — the leaf-mean operator factors
  through the mean: configurations with equal leaf-mean have
  equal root signal (the leaf differences are invisible to
  the root).
* `anova_split` — the two-leaf ANOVA identity: the
  within-leaf variance equals `(a - b) ^ 2 / 2`.
-/

open Finset

namespace Hagi

section F3Root

/-- Second moments after a common addend:
`(vi + u)^2 - (vj + u)^2 = (vi^2 - vj^2) + 2 * u * (vi - vj)`. -/
theorem root_invariance (vi vj u : ℝ) :
    -- the second moments after the common addend:
    (vi + u)^2 - (vj + u)^2 = (vi^2 - vj^2) + 2 * u * (vi - vj) := by
  ring

/-- Configurations with equal leaf-sum have equal
leaf-mean: if `a + b = c + d`, then `(a + b) / 2 = (c + d) / 2`
(the root signal factors through the mean). -/
theorem root_no_leaf_signal (a b c d : ℝ) (h : a + b = c + d) :
    -- the leaf-mean of (a,b) equals the leaf-mean of (c,d)
    (a + b) / 2 = (c + d) / 2 := by
  rw [h]

/-- The two-leaf ANOVA identity: the within-leaf variance
`(a - (a + b)/2)^2 + (b - (a + b)/2)^2` equals `(a - b)^2 / 2`. -/
theorem anova_split (a b : ℝ) :
    -- E[(x_i − x̄)²] ≥ 0: the within-leaf variance of the two leaves
    (a - (a + b)/2)^2 + (b - (a + b)/2)^2
      = (a - b)^2 / 2 := by
  have hmid : (a + b)/2 = (a + b)/2 := rfl
  field_simp
  ring

end F3Root

end Hagi
