/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# Prelude.Info — the single information-theory prelude

The ONE home of the information-theoretic definitions of the
corpus (the R198 deduplication of the four parallel KL's, two
entropies, two TV's and the softmax family):

* `klDef q p := ∑ v, q v * log (q v / p v)` — THE KL divergence
  (first argument = the sampling distribution);
* `entDef p := −∑ v, p v * log (p v)` — THE Shannon entropy;
* `tvDef p q := (∑ v, |p v − q v|)/2` — THE total variation;
* `softDef z := exp(z)/Σexp` — THE softmax.

Consumers keep their historical names; the bridge identities
(`KLdiv = klDef`, `ent = entDef`, `negEntropy = -entDef`,
`tvDist = tvDef`) are stated in the CONSUMERS (layer >= Data),
each as a one-line rfl, so no bridge is ever re-proved.
-/

namespace Hagi.Prelude

open Finset

variable {V : Type*} [Fintype V]

/-- THE KL divergence of the corpus (q is the sampling
distribution). -/
noncomputable def klDef (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (q v / p v)

/-- THE Shannon entropy. -/
noncomputable def entDef (p : V → ℝ) : ℝ :=
  -∑ v, p v * Real.log (p v)

/-- THE total variation distance (half L1). -/
noncomputable def tvDef (p q : V → ℝ) : ℝ :=
  (∑ v, |p v - q v|) / 2

/-- THE softmax. -/
noncomputable def softDef {k : Type*} [Fintype k] (z : k → ℝ) : k → ℝ :=
  fun a => Real.exp (z a) / ∑ b, Real.exp (z b)

end Hagi.Prelude
