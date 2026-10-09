/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# Prelude.Info — the single information-theory prelude

The canonical information-theoretic definitions:

* `klDef q p := ∑ v, q v * log (q v / p v)` — KL divergence
  (`q` is the sampling distribution);
* `entDef p := −∑ v, p v * log (p v)` — Shannon entropy;
* `tvDef p q := (∑ v, |p v − q v|)/2` — total variation;
* `softDef z := exp(z)/Σexp` — softmax.

Bridge identities to historical consumer names are stated in
the consumers, each as a one-line `rfl`.
-/
namespace Hagi.Prelude

open Finset

variable {V : Type*} [Fintype V]

/-- KL divergence: `∑ v, q v * log (q v / p v)` (`q` is the
sampling distribution). -/
noncomputable def klDef (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (q v / p v)

/-- Shannon entropy: `−∑ v, p v * log (p v)`. -/
noncomputable def entDef (p : V → ℝ) : ℝ :=
  -∑ v, p v * Real.log (p v)

/-- Total variation distance (half the L1 distance). -/
noncomputable def tvDef (p q : V → ℝ) : ℝ :=
  (∑ v, |p v - q v|) / 2

/-- The softmax: `exp (z a) / ∑ b, exp (z b)`. -/
noncomputable def softDef {k : Type*} [Fintype k] (z : k → ℝ) : k → ℝ :=
  fun a => Real.exp (z a) / ∑ b, Real.exp (z b)

end Hagi.Prelude
