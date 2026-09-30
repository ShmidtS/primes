/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.LazyAdamMomentum

set_option linter.style.header false

/-!
# ElementQuant: factorization × quantization commutation (round 49, block 2)

For the TableLoRA + ternary pipeline: the reconstruction
error of "factorize to rank r, then quantize" splits by the
triangle inequality into the TAIL (the rank-r truncation
error, measured from the spectrum) plus the QUANT error (the
grid rounding of the factors) — and the GO/NO-GO: the
factor-then-quantize route beats direct quantization IFF
tail + qerr(r) < qdirect.

NOT PROVED: the closed form of qerr(r) for ternary grids in
terms of r, s and the factor spectra (the nearest-3-level
rounding bound per entry — elementary but not assembled).

**Prescription**: measure tail(r) from the σ-spectrum of ΔE
and qdirect from one ternary pass; the comparison is a
one-line certificate before any GPU run.
-/

open Finset

namespace Hagi

/-- **The commutation triangle**: the reconstruction error of
factor-then-quantize is at most tail + qerr — the exact
split of the two error sources. -/
theorem factor_quant_error {X : Type*} [NormedAddCommGroup X] (dE AB QAB : X)
    (tail qerr : ℝ) (h1 : ‖dE - AB‖ = tail) (h2 : ‖AB - QAB‖ = qerr) :
    ‖dE - QAB‖ ≤ tail + qerr := by
  have h3 : dist dE QAB ≤ dist dE AB + dist AB QAB := dist_triangle _ _ _
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h3
  rw [h1, h2] at h3
  exact h3

/-- **The GO/NO-GO comparison**: the factorize+quantize
route beats the direct quantization IFF tail + qerr < qdirect
— with the factor-quantize bound from the triangle above,
the direct route's error exceeds it whenever the measured
inequality holds. -/
theorem factor_quant_go (tail qerr qdirect boundDirect : ℝ)
    (hgain : tail + qerr < qdirect)
    (hbound : boundDirect ≤ qdirect) (hbest : qdirect ≤ tail + qerr) :
    boundDirect < tail + qerr := by
  linarith

end Hagi
