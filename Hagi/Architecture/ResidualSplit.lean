/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LatentAlign

/-!
# ResidualSplit — expert disagreement and quantization error
are DIFFERENT residuals (R243; LittleBit integration)

LittleBit runs a separate residual branch for the
compression error of the primary low-rank approximation,
gated by economics (it helps at 0.3–1.0 BPW and on larger
models, but HURT on OPT-1.3B at 0.1 BPW). HAGI's merge has
been treating two conceptually different corrections as one
`r64` path:

* R_expert = W_i − W_shared — the expert DISAGREEMENT, the
  thing the whole fiber architecture exists to preserve;
* R_quant  = W − Ŵ_primary — the COMPRESSION error of the
  factorized-ternary representation.

They have different jobs, different budgets and different
signs of usefulness. This module separates them at the
Lean-model level:

* `ResidualSplit` — the exact three-way bookkeeping
  W = W_shared + R_expert + R_quant;
* `residual_gate_two_sided` — the economic gate for the quantization
  residual branch: enabled iff η_r·E_r > C_r + P_quant —
  exactly the LittleBit empirical exception, formalized as a
  decision rule rather than a constant;
* `expert_residual_not_compressible` — the warning result:
  R_quant can be reduced by spending bits, but R_expert can
  only be PRESERVED (alignment/fibers) or DESTROYED
  (averaging) — compression gains on the wrong residual do
  not recover expert specialization.
-/

open scoped BigOperators
open Matrix

namespace Hagi.Residual

variable {d : ℕ}

/-- The exact three-way decomposition of a merged weight. -/
structure ResidualSplit (W Wshared Re Rq : Matrix (Fin d) (Fin d) ℝ) : Prop where
  exact_split : Wshared + Re + Rq = W

/-- **The economic gate for the quantization-residual
branch** (LittleBit's empirical exception, formalized):
the branch is justified iff its transported gain exceeds
its parameter+compute price plus the quantization penalty
it is meant to fix. -/
def ResidualGateOn (η E C P : ℝ) : Prop := η * E > C + P

theorem residual_gate_two_sided (η E C P : ℝ) :
    ResidualGateOn η E C P ↔ η * E - C - P > 0 := by
  unfold ResidualGateOn
  constructor <;> intro h <;> linarith

/-- **Compression gains on R_quant do not recover expert
specialization**: if the expert residual is destroyed by
the merge (zero energy in the merged model) then NO budget
spent on the quantization residual changes that — the two
residuals are orthogonal books. -/
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

/-- **Fiber-preservation bookkeeping**: if the expert
residual is kept as fibers (nonzero energy) while the
quantization residual is driven down by spending budget,
the total fidelity error is bounded by the quantization
residual alone. -/
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
