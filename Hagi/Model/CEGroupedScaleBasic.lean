/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Feature absolute mass leaf

The single Mathlib-only definition `featureAbsSum` that the batch
descent common part consumes.  Split out of `Hagi.Model.CEGroupedScale`
(C276) so that the descent import path does not pay for the grouped
scale stack; the namespace is continued here, so the fully-qualified
name is unchanged.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEGroupedScale

/-- Full absolute feature mass.  No within-block factor is substituted
for the full sum over all feature columns and all logits. -/
noncomputable def featureAbsSum {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : ℝ :=
  ∑ v, ∑ j, |X v j|

end Hagi.Model.CEGroupedScale
