/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.PuncturedCE
set_option linter.style.header false

/-!
# QFormer bridge - zero-init identity (function-preserving)

Phase B. Sources: 2609.31448 (ViSTA:
learned queries U, zero-init output projection => Z = V
exactly - the bridge is INCLUDED without changing the
behavior), 2609.34598 (fixed summary-token count as KV),
2607.18042 (constant learnable bridge tokens).

Theorems:

* `vista_bridge_zero` - with a zero output projection the
bridge output is exactly zero.
* `vista_residual_identity` - inserting the bridge into
the residual stream changes nothing: V + bridge = V.

Honest boundary: fixed-rate cost (K summary tokens
regardless of input length) is definitional; the CLAIM
that this preserves downstream quality while compressing
is empirical (2609.31448), not proven. -/

namespace Hagi

/-- The bridge: K learned queries attend to the value V and
project through Wout into the residual stream. -/
def bridgeOut {d : ℕ} (U : Fin 1 → (Fin d → ℝ))
    (A : Fin d → ℝ) (Wout : ℝ) : ℝ :=
  ∑ k, Wout * (∑ i, U k i * A i)

/-- With a zero output projection the bridge output is
exactly zero (ViSTA zero-init). -/
theorem vista_bridge_zero {d : ℕ} (U : Fin 1 → (Fin d → ℝ))
    (A : Fin d → ℝ) :
    bridgeOut U A 0 = 0 := by
  unfold bridgeOut
  simp

/-- Inserting the bridge into the residual stream changes
nothing: the function is PRESERVED on inclusion. -/
theorem vista_residual_identity {d : ℕ} (U : Fin 1 → (Fin d → ℝ))
    (A : Fin d → ℝ) (Vres : ℝ) :
    Vres + bridgeOut U A 0 = Vres := by
  rw [vista_bridge_zero]
  ring

end Hagi
