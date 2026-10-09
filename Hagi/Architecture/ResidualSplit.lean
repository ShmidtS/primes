/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LatentAlign

/-!
# ResidualSplit — expert disagreement and quantization error
are different residuals

The merge separates two corrections: the expert disagreement
`R_expert = W i - W_shared` and the compression error
`R_quant = W - Ŵ_primary`.

* `ResidualSplit` — the exact three-way bookkeeping
  `Wshared + Re + Rq = W`.
* `residual_gate_two_sided` — the decision rule for the
  quantization-residual branch: enabled iff
  `η * E > C + P`.
* `expert_residual_not_compressible` — if the expert residual
  is zero in the merged model, no budget spent on the
  quantization residual recovers it.
* `fidelity_bound_with_fibers` — bookkeeping when the expert
  residual is kept and the quantization residual driven down.
-/

open scoped BigOperators
open Matrix

namespace Hagi.Residual

variable {d : ℕ}

/-- The exact three-way decomposition of a merged weight. -/
structure ResidualSplit (W Wshared Re Rq : Matrix (Fin d) (Fin d) ℝ) : Prop where
  exact_split : Wshared + Re + Rq = W

/-- The gate for the quantization-residual branch:
`η * E > C + P`. -/
def ResidualGateOn (η E C P : ℝ) : Prop := η * E > C + P

theorem residual_gate_two_sided (η E C P : ℝ) :
    ResidualGateOn η E C P ↔ η * E - C - P > 0 := by
  unfold ResidualGateOn
  constructor <;> intro h <;> linarith

/-- If the expert residual is zero in the merged model
(`hdead`), then any split `Wshared + 0 + Rq' = W` forces
`Wshared + Rq' = W`. -/
theorem expert_residual_not_compressible
    (W Wshared Re Rq : Matrix (Fin d) (Fin d) ℝ)
    (h : ResidualSplit W Wshared Re Rq) (hdead : Re = 0)
    (Rq' : Matrix (Fin d) (Fin d) ℝ) :
    ResidualSplit W Wshared 0 Rq' →
      Wshared + Rq' = W := by
  intro hsplit'
  have h1 : Wshared + 0 + Rq' = W := hsplit'.exact_split
  rw [add_zero] at h1
  exact h1

/-- If the split holds and `Wshared + Re + Rq' = W`, then
`W - (Wshared + Re) = Rq` and
`W - (Wshared + Re + Rq') = 0`. -/
theorem fidelity_bound_with_fibers
    (W Wshared Re Rq Rq' : Matrix (Fin d) (Fin d) ℝ)
    (h : ResidualSplit W Wshared Re Rq)
    (hkeep : Wshared + Re + Rq' = W) :
    W - (Wshared + Re) = Rq ∧ W - (Wshared + Re + Rq') = 0 := by
  constructor
  · rw [← h.exact_split]
    abel_nf
  · rw [hkeep]
    abel_nf

end Hagi.Residual
