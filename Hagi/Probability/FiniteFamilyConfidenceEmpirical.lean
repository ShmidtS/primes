/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# Empirical mean leaf

The single Mathlib-only definition `empiricalMean` that the batch
descent parts consume.  Split out of
`Hagi.Probability.FiniteFamilyConfidence` (C276) so that the descent
import path does not pay for the full confidence stack; the namespace
is continued here, so the fully-qualified name is unchanged.
-/

set_option relaxedAutoImplicit false

open Finset Real

namespace Hagi.Probability.FiniteFamilyConfidence

variable {V : Type} [Fintype V]

/-- Empirical coordinate-average loss on one product sample. -/
noncomputable def empiricalMean {n : ℕ} (X : Fin n → V → ℝ)
    (ω : Fin n → V) : ℝ :=
  (∑ i, X i (ω i)) / (n : ℝ)

end Hagi.Probability.FiniteFamilyConfidence
