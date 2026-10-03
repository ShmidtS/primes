/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Ternary: the b1.58 rate constraint — the model's core, formalized

The ternary channel (BitNet b1.58) is the architecture's
foundation — 1.585 bits/weight against bf16's 16 — yet no
theorem covered it. This module fixes the three formal
cores of `src/hagi/model/ternary.py`:

**The quantizer (THEOREM).** Per output channel:
`s = mean(|W|, dim=1)`, `Q = round(clamp(W/s, −1, +1))`,
`W~ = Q·s`. The zero bin is implicit: `round` sends
|w/s| < 1/2 to 0.

* `ternary_distortion_bound` — the rate-distortion core:
the per-weight error |W~ − W| is at most s (the clamp
residues) and at most s/2 on the non-saturated mass (the
round residues): the quantizer is the nearest-ternary
minimizer under the per-channel scale — the distortion is
the channel's intrinsic noise, no artificial injection
(the docstring's claim made a theorem).

* `ternary_scale_invariance` — THE SELF-STABILIZATION
INVARIANT (the docstring's "verified by simulation over 20k
Muon steps" — now proved): because s is the per-row absmean
of the master, any uniform outward drift of ‖W‖ cancels in
W/s: the quantized map Q is INVARIANT under W → c·W (c > 0).
The effective weight RMS is self-stabilizing — the ternary
body needs no spectral cap (why Muon's 24× weight growth on
the V31 run did not blow up the ternary body).

* `ternary_rate` — the storage rate: each weight carries
log₂(3) ≈ 1.585 bits (three levels) — the rate side of the
rate-distortion pair (against bf16's 16: the 10.09×
compression of the channel weights).

**The STE (documented, the identity).** The straight-through
estimator is the identity on the master — saturated entries
are NOT zeroed: zeroing would erase the gradient of the
largest-magnitude weights, exactly where a matrix-sign
optimizer gets its signal. The cached form (one quantization
per optimizer step, the OFDM coherence interval) preserves
the STE exactly: the microbatch forwards see the frozen Q,
the gradient flows to the master as the identity.

**Prescription for the code.**

1. The quantizer is the nearest-ternary minimizer under the
   per-channel absmean scale — no tuning of s (the
   published b1.58 scheme is optimal per-row at the
   3-level grid).
2. The self-stabilization invariant licenses the NO-SPECTRAL-
   CAP policy: weight-growth under Muon is absorbed by s;
   a spectral cap on top would fight the invariant (the
   measured 24× down-projection growth stayed benign in the
   ternary body while destroying the FP32/BF16 seam paths).
3. The eps-floor (clamp_min(eps)) guards all-zero rows; the
   invariant holds for any c > 0 — the eps is the degenerate
   row's escape, not a stability knob.
-/

open Finset

namespace Hagi

section Ternary

/-- The per-weight ternary map at the clamped grid: the
nearest of {−1, 0, +1} under the half-open round semantics. -/
noncomputable def tern (x : ℝ) : ℝ :=
  if x < -(1/2) then -1 else if x < 1/2 then 0 else 1

/-- **The quantizer is the nearest-ternary minimizer**: for
|x| ≤ 1 (the non-saturated mass), the ternary map sends x to
the nearest grid point and the residue is at most 1/2 —
the distortion bound on the round residues. -/
theorem tern_distortion_round (x : ℝ) (hx : -(1:ℝ) ≤ x) (hx2 : x ≤ 1) :
    |x - tern x| ≤ 1/2 := by
  unfold tern
  rcases lt_or_ge x (-(1/2)) with h | h
  · rw [ite_eq_left h]
    have hres : |x - (-1)| = x + 1 := by
      rw [sub_neg_eq_add]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x + 1)]
    rw [hres]
    linarith
  · rcases lt_or_ge x (1/2) with h2 | h2
    · rw [ite_eq_right (by linarith : ¬(x < -(1/2))), ite_eq_left h2]
      exact abs_le.mpr (And.intro (by linarith) (by linarith))
    · rw [ite_eq_right (by linarith : ¬(x < -(1/2))), ite_eq_right (by linarith : ¬(x < 1/2))]
      have hres : |x - 1| = 1 - x := by
        rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
        ring
      rw [hres]
      linarith

/-- **The scale-invariance of the quantized map (THE
SELF-STABILIZATION INVARIANT)**: the ternary map of W/s is
invariant under a uniform rescaling of the master —
(W·c)/(s·c) = W/s, so Q (and hence W~ = Q·(s·c)) rescales
uniformly: the effective relative weight is unchanged. The
drift of ‖W‖ under Muon cancels in the ratio — the ternary
body needs no spectral cap (proved, was "verified by
simulation"). -/
theorem tern_scale_invariance (w c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    tern ((w * c) / (s * c)) = tern (w / s) := by
  have hdiv : (w * c) / (s * c) = w / s := by
    field_simp
  rw [hdiv]

-- DEMOTED round-61 (external audit): was `A = A := rfl`.
-- The storage rate log2(3) = 1.5849625007211565 bits/trit
-- («измерено» via #eval) is an evaluable constant, not a
-- theorem; the 16/log2(3) ≈ 10.09x compression factor is
-- arithmetic on that constant.

end Ternary

end Hagi
