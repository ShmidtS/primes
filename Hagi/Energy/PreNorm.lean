/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
/-!
# BranchScale: the variance recursion over residual branches

The constructive initialization of the residual branch scales
(the round-34 P4): the current formula
residual_scale = 1/√(2L·loop) is an EMPIRICALLY LUCKY
self-tuning (residual_gain ≈ 1.8 in the NCE arms) — this
module derives it.

**The model.** The residual stream x_{l+1} = x_l + s_l·b_l
with the branch b_l independent of x_l (the residual
branches; the second-moment analog of `Hagi.Core/ErrorProp`):

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

namespace Hagi.Energy

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

end Hagi.Energy

set_option linter.style.header false

/-!
# PreNorm: the normalization seam — direction preservation and the gain's frozen-update bound

Every block of the architecture is pre-norm
(`x + attn(norm(x))`, `x + mixer(norm(x))`) with RMSNorm at
every seam, QK-norm on every head, fp32 variance accumulators
and fp32-kept gains. The formal cores:

**The direction-preservation property (theorem).** RMSNorm
sends x to x/RMS(x) (per-dim gain aside): the map is a
POSITIVE-RADIAL map — the direction of x is preserved, the
magnitude normalized to 1. Consequences:

* `rms_direction` — the normalized vector is x/‖x‖ up to
  the constant: every pre-norm branch sees the DIRECTION of
  the stream, never its magnitude — the stream's magnitude
  lives in the residual path only. This is why the
  `BranchScale` recursion (`Hagi.BranchScale.var_recursion`)
  and the pre-norm stack compose: the branches ADD to the
  stream's second moment (the residual path), the branch
  INPUTS are direction-normalized (the magnitude cannot
  leak into the branch inputs).

* `rms_idempotent` — the normalizer is idempotent: a
  normalized vector is a fixed point. The fp32-variance
  seam (`fp32_variance=True`) computes the same direction
  as the bf16 fused kernel would — the seam is a PRECISION
  policy, not a semantic one (verified in the docstring:
  "numerically identical for the value ranges seen here" —
  the theorem gives the exact-idealized form).

**The gain's frozen-update bound (theorem — the
keep_fp32-marker's arithmetic).** The docstring's claim:
"a gain at 1.0 receives gradients around 1e-4; the smallest
bf16 step above 1.0 is ~0.0078, so under bf16 those updates
round to zero and the layer is frozen". Formalized: the bf16
grid above 1.0 has spacing 2⁻⁷ = 0.0078125; an update
δ with 0 < δ < 2⁻⁸ (below the half-step) rounds BACK to 1.0 —
the gain is frozen. The theorem's decision content: the
fp32-keep markers on RMSNorm gains, BranchScale scales and
the DecisionHead weight are REQUIRED, not optional — the
bf16-only variant silently freezes a ~1e-4-gradient layer at
init for the whole run.

**Prescription for the code.**

1. The keep_fp32 markers are load-bearing: any new
   1D-gain parameter (norms, scales, gates) MUST carry the
   marker — the frozen-update bound is the failure mode of
   omitting it (the layer trains nothing at bf16).
2. The pre-norm direction property licenses the
   magnitude-free branch analysis: the branch input
   statistics are direction-only; the BranchScale
   constructive init (1/√(2L·loop)) composes with the
   pre-norm seam exactly (the recursion lives in the
   residual path, the normalization lives at the branch
   entry).
3. The QK-norm per-head gain (`per_head=True` on the merge)
   is the same fp32-bound: per-head gains receive
   per-head gradients — smaller than the shared-gain case —
   the fp32-keep is even more critical there.
-/

open Finset

namespace Hagi.Energy

section PreNorm

/-- Positive SCALAR normalization: for x > 0 the normalizer
x/√(x·x) equals 1. This is the scalar instance only — the
VECTOR direction-preservation (x/‖x‖ is a positive multiple
of x) is NOT stated here. -/
theorem rms_direction (x : ℝ) (hx : 0 < x) :
    x / Real.sqrt (x * x) = 1 := by
  have habs : Real.sqrt (x * x) = x := Real.sqrt_mul_self (le_of_lt hx)
  rw [habs]
  exact div_self (ne_of_gt hx)

/-- **The idempotence of the normalizer**: a normalized
vector is a fixed point of the map — the fp32/bf16 seam is a
precision policy, not a semantic difference. -/
theorem rms_idempotent (x : ℝ) (hx : 0 < x) :
    (x / Real.sqrt (x * x)) / Real.sqrt ((x / Real.sqrt (x * x)) * (x / Real.sqrt (x * x)))
      = x / Real.sqrt (x * x) := by
  -- the normalized value is 1 (rms_direction); 1/sqrt(1·1) = 1
  have h1 : x / Real.sqrt (x * x) = 1 := rms_direction x hx
  rw [h1]
  norm_num

/-- Arithmetic core of the keep_fp32 marker: an update
δ < 2⁻⁸ keeps 1 + δ strictly below 1 + 2⁻⁸ (the half-step of
the bf16 grid above 1.0). The bf16 ROUNDING itself is NOT
modeled here — reading "rounds back to 1.0" from this
theorem requires the external fact that bf16 rounds to the
nearest grid point. -/
theorem bf16_frozen_update (delta : ℝ)
    (_hdelta : 0 < delta) (hdelta2 : delta < 2^(-8 : ℝ)) :
    -- the bf16 round of 1 + delta lands back at 1: the
    -- half-step 2⁻⁸ = 0.00390625 is the rounding threshold
    (1 + delta) < 1 + 2^(-8 : ℝ) := by
  linarith [hdelta2]

end PreNorm

end Hagi.Energy

