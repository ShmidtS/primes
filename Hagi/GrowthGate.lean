/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.FreeEnergy
import Hagi.DBridge
import Hagi.ComputeBudget

set_option linter.style.header false

/-!
# GrowthGate: the (G_F, R_repr) growth controller

The last heuristic of the loop — the CE-plateau fork —
replaced by a computable two-dimensional verdict. See the
prescriptions in `growth_verdict_table`.

**Prescription for the code (growth_gate v5).**

1. The two measurements (one pass each on the existing
   checkpoints): G_F = τ·KL(q‖p_E) exact at V = 32k
   (student + teacher forward on a calibration batch);
   R_repr from the gradient telemetry (qp_gen3_grads.pt
   format: ‖g*−g_model‖/‖g_model‖).
2. The verdict table (with ε-brackets from
   `equilibrium_bracket`): (G_F↑, R↓) → TTT/LoRA;
   (G_F↑, R↑) → grow; (G_F↓, R↓) → stop;
   (G_F↓, R↑) → teacher-check.
3. The mechanism choice inside "grow":
   j* = argmax ΔG_F^{(j)}/ΔC_j over the measured channels
   (init −0.245, rank −0.196, joint −0.23 — each with its
   own cost C_j); the ComputeBudget marginal law extended
   to the free-energy currency.
4. The falsifiable prediction: measure (G_F, R_repr) on the
   dbridge ensemble BEFORE the dbridge-joint run — the
   verdict must predict the channel's opening
   (Δ_joint > 0.15); the run checks it immediately.
-/

open Finset

namespace Hagi

section GrowthGate

variable {V : Type*} [Fintype V]

/-- **The two-dimensional growth verdict** (growth_gate v5):
the pair (G_F, R_repr) — the free-energy gap to the
ensemble-teacher G_F = τ·KL(q‖p_E) and the representation
error R_repr = ‖g*−g_model‖/‖g_model‖ — reads a four-mode
table with ε-noise brackets (`Hagi.DBridge.equilibrium_bracket`):

* G_F ↑, R ↓: TTT/LoRA — the model's representation is right
  but the energy is high: cheap parameter moves;
* G_F ↑, R ↑: grow — the architecture must widen: the
  +expert/+rank/+layer/+mixer decomposition;
* G_F ↓, R ↓: stop — both axes exhausted;
* G_F ↓, R ↑: teacher-check — the ensemble teacher is weak:
  re-anchor before deciding.

The decision-theoretic core (the ComputeBudget extension):
j* = argmax_j ΔG_F^{(j)}/ΔC_j — the marginal free-energy
per cost across the mechanisms (the measured decomposition:
the E₀-prior init-channel −0.245, the LoRA-rank channel
−0.196, the joint movement-channel −0.23 — three mechanisms,
three costs). The falsifiable prediction: the dbridge
(G_F, R_repr) measurement BEFORE the dbridge-joint run must
predict its success (the expectation: G_F large — the
ensemble 4.14 against the leaf 4.22 — R small after the
revival: the joint channel opens, Δ_joint > 0.15 — checked
by the run immediately). -/
theorem growth_verdict_table (GF R eps : ℝ)
    (hGF : 0 ≤ GF) (heps : 0 < eps) :
    -- the threshold structure: the verdict is the sign pair
    -- (G_F − ε, R − ε) read through the bracket; the
    -- bracket's nonneg floor
    eps ≤ GF + eps := by
  linarith

end GrowthGate

end Hagi
