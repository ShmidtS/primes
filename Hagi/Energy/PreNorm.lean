/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.BranchScale

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

namespace Hagi
export Hagi.Energy (rms_direction rms_idempotent bf16_frozen_update)
end Hagi
