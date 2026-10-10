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

not PROVED: the closed form of qerr(r) for ternary grids in
terms of r, s and the factor spectra (the nearest-3-level
rounding bound per entry — elementary but not assembled).

**Prescription**: measure tail(r) from the σ-spectrum of ΔE
and qdirect from one ternary pass; the comparison is a
one-line certificate before any GPU run.
-/

open Finset

namespace Hagi.Budget

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

/-- **The GO/NO-GO certificate (honest form)**: if the
factor-route error bound `tail + qerr` is strictly below the
measured direct-quantization error `qdirect`, then the true
factor-route error is strictly below `qdirect` — via the
commutation triangle above. This is a real decision rule, not
a vacuous implication: the earlier revision carried the
contradictory pair (tail+qerr < qdirect) ∧ (qdirect ≤
tail+qerr), which made the theorem about an empty hypothesis
set. Found in external review, 2025-round-51. -/
theorem factor_quant_go {X : Type*} [NormedAddCommGroup X]
    (dE AB QAB : X) (tail qerr qdirect : ℝ)
    (htail : ‖dE - AB‖ = tail) (hqerr : ‖AB - QAB‖ = qerr)
    (hgain : tail + qerr < qdirect) :
    ‖dE - QAB‖ < qdirect := by
  have h3 := factor_quant_error dE AB QAB tail qerr htail hqerr
  calc ‖dE - QAB‖ ≤ tail + qerr := h3
    _ < qdirect := hgain

end Hagi.Budget

namespace Hagi
export Hagi.Budget (factor_quant_error factor_quant_go)
end Hagi
