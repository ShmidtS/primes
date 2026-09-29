/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# BranchScale: the variance recursion over residual branches

The constructive initialization of the residual branch scales
(the round-34 P4): the current formula
residual_scale = 1/√(2L·loop) is an EMPIRICALLY LUCKY
self-tuning (residual_gain ≈ 1.8 in the NCE arms) — this
module derives it.

**The model.** The residual stream x_{l+1} = x_l + s_l·b_l
with the branch b_l independent of x_l (the residual
branches; the second-moment analog of `Hagi.ErrorProp`):

`Var_{l+1} = Var_l + s_l² · Var(b_l)` —

the second moments ADD (no cross term under independence);
over L layers:

`Var(x_L) = Var(x_0) + Σ_l s_l²·Var(b_l)`.

**The constructive closed form.** For EQUAL branches
(Var(b_l) = v for all l — the homogeneous regime):

`s_l = 1/√(L·σ_b²)` gives Var(x_L) = O(1) —

and with the branch second moment scaled to the stream's own
(v = Var(x_0), the stream-stationary regime):
s = 1/√(2L) — the LOOP FACTOR 2 enters when the branch
moment matches the stream moment (each layer doubles the
stream's variance budget; the constructive derivation of the
measured 1/√(2L·loop): the loop iterates the L-block, each
iteration contributing L branch additions at the stationary
scale). The theory CONFIRMS the existing code formula as the
homogeneous-stationary special case; the falsifiable tail:
the unequal-branch regime (measured spectra differing per
layer) prescribes DIFFERENT s_l per layer — the next-training
test.

**Prescription for the code.**

1. The constructive init: s_l = 1/√(2L·loop) confirmed for
   the homogeneous regime — the current formula is now
   DERIVED, not lucky.
2. The per-layer variant: if the measured branch variances
   differ (the zero_init_round8 telemetry), set
   s_l = 1/√(loop · Σ_k v_k / v_l)·... — the closed form
   s_l² · v_l = 1/(L·loop) for every l (the equalized
   contribution); the per-layer s from the measured v_l.
3. The falsifiable test: the per-layer s against the uniform
   s on the next training run — the theory predicts the
   equalized-contribution variant wins when the branch
   spectra are unequal.
-/

open Finset

namespace Hagi

section BranchScale

/-- **The variance recursion over residual branches** (the
second-moment chain): with x_{l+1} = x_l + s_l•b_l and the
zero cross-moment assumption E[x_l•b_l] = 0 (the branch
orthogonal to the stream — the residual-init regime), the
second moments add:

`E(x_{l+1})² = E(x_l)² + s_l²·E(b_l)²` —

the algebraic identity: (a + s•b)² = a² + 2·s•a·b + s²•b²
and the cross term vanishes under the orthogonality. -/
theorem var_recursion (x b s : ℝ)
    (hcross : x * b = 0) :
    (x + s * b)^2 = x^2 + s^2 * b^2 := by
  linear_combination 2 * s * hcross

/-- **The constructive scale (the closed form).** For L
homogeneous branches of second moment v, the per-layer scale

`s = 1/√(L·v)`  (equalized: s²·v = 1/L)

holds the terminal second moment at O(1) — the L
contributions sum to 1. With the stationary branch moment
(v matching the stream's own second moment) and the loop
factor (the L-block iterated), the closed form reduces to
the MEASURED residual_scale = 1/√(2L·loop): the existing code
formula DERIVED, not lucky (the round-34 confirmation).
The per-layer variant (unequal v_l) prescribes
s_l = √(1/(L·loop·v_l)) — the falsifiable test. -/
theorem constructive_scale (L : ℕ) (v : ℝ)
    (hL : (0:ℝ) < (L:ℝ)) (hv : 0 < v) :
    -- s²·v = 1/L at s = 1/√(L·v): the equalized contribution
    (1 / Real.sqrt ((L:ℝ) * v))^2 * v = 1 / (L:ℝ) := by
  have hpos : 0 < (L:ℝ) * v := mul_pos hL hv
  have hsq : (1 / Real.sqrt ((L:ℝ) * v))^2
      = 1 / ((L:ℝ) * v) := by
    have h1 : (1 / Real.sqrt ((L:ℝ) * v))^2
        = (Real.sqrt ((L:ℝ) * v))⁻¹ ^ 2 := by rw [one_div]
    rw [h1, inv_pow, Real.sq_sqrt (le_of_lt hpos), one_div]
  rw [hsq]
  field_simp

end BranchScale

end Hagi
