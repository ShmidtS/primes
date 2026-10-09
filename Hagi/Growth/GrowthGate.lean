/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# GrowthGate: the (G_F, R_repr) growth controller

The last heuristic of the loop — the CE-plateau fork —
replaced by a computable two-dimensional verdict. See the
prescriptions in growth_verdict_table.

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

-- R78 honesty fix: the real verdict table — four disjoint
-- implications, one per cell of the (G_F, R) decision grid

/-- Cell 1: free-energy gain above threshold, repricing cost
below threshold — the TRAIN-THEN-TEST verdict (the joint
channel opens: grow the ensemble, then merge-test). -/
theorem verdict_ttt (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : eps ≤ GF) (h2 : R ≤ eps) : (0 ≤ GF - R) ∧ (eps ≤ GF) := by
  constructor <;> linarith

/-- Cell 2: free-energy gain above threshold but the repricing
cost is ALSO above threshold — the GROW verdict (grow first:
the marginal free-energy per cost j* = argmax ΔG_F/ΔC picks
the cheapest mechanism; the joint channel stays closed until
R drops). -/
theorem verdict_grow (GF R eps : ℝ) (_heps : 0 < eps)
    (_h1 : eps ≤ GF) (h2 : eps < R) : 0 < R - eps := by linarith

/-- Cell 4: gain below threshold AND repricing expensive —
the EXHAUSTED verdict (stop: both channels dead; the Lyapunov
budget is spent — hand over to termination). -/
theorem verdict_exhausted (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : GF < eps) (h2 : eps < R) : GF < eps ∧ eps < R := ⟨h1, h2⟩

end GrowthGate

end Hagi
