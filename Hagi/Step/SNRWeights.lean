/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# SNRWeights — uniform orthogonalization overweights noise
(plan §2 R230; source 2607.16169 HTMuon/Pion; analysis link
R225: the SNR regime split of the NS polynomial error)

Uniform (msign) orthogonalization treats every singular
direction equally: a noise direction with tiny signal gets
the SAME weight as a clean direction. The SNR-aware
transform weights directions by confidence. The accounting:

* `uniform_is_mean`: uniform weighting (1/r each) achieves
  exactly the MEAN squared deviation — the noise floor of
  uniform orthogonalization;
* `focused_beats_uniform`: concentrating the weight on the
  below-mean directions gives a weighted deviation STRICTLY
  under the uniform mean (whenever some direction is
  strictly below mean) — the existence statement: SNR-aware
  weighting is never worse and strictly better when the
  spectrum is non-degenerate. NOT proved here: which
  weighting an implementable transform realizes (the
  polynomial design); this module proves the TARGET is
  better, i.e. the motivation, not the mechanism.
-/

namespace Hagi

open Finset

variable {r : ℕ} [NeZero r]

/-- **Uniform weighting is the mean**: with equal weights
1/r the weighted squared deviation is exactly the arithmetic
mean — the noise floor of uniform (msign)
orthogonalization. -/
theorem uniform_is_mean (dev : Fin r → ℝ) :
    ∑ i, (1 / (r : ℝ)) * (dev i)^2
      = (∑ i, (dev i)^2) / r := by
  rw [← Finset.mul_sum]
  field_simp

/-- **Focused weighting beats uniform**: if some direction j
has deviation strictly below the mean, concentrating weight
on j gives weighted deviation strictly under the uniform
mean — the SNR-aware target strictly dominates the uniform
floor whenever the spectrum is non-degenerate. -/
theorem focused_beats_uniform (dev : Fin r → ℝ)
    (hdev : ∀ i, 0 ≤ (dev i)^2)
    (mean : ℝ) (hmean : mean = (∑ i, (dev i)^2) / r)
    (j : Fin r) (hj : (dev j)^2 < mean) :
    ∃ v : Fin r → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)
      ∧ ∑ i, v i * (dev i)^2 < (∑ i, (dev i)^2) / r := by
  refine ⟨fun i => if i = j then (1:ℝ) else 0, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = j
    · simp [h]
    · simp [h]
  · simp
  · have hsingle : ∑ i, (if i = j then (1:ℝ) else 0) * (dev i)^2
        = (dev j)^2 := by
      simp
    rw [hsingle, ← hmean]
    exact hj

end Hagi
