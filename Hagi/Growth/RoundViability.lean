/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainOperator
import Hagi.Information.GainRecoverability
import Hagi.Growth.GainDecomposition

/-!
# RoundViability — when the next round pays (the controller's
stop/continue question)

The recursive self-development cycle (student → new experts
→ new student, the MOPD round structure) needs a STOP/CONTINUE
criterion. This module is the criterion, on the measured
quantity E_dev of the fresh expert family:

* `round_exhausted`: if the new expert family has ZERO
  deviation energy (no disagreement — the specialists have
  converged to the shared cortex), the gain operator can
  deliver at most ρ·D − ξ: WITHOUT fresh disagreement there
  is NO new frontier — the cycle is exhausted, growth must
  come from elsewhere (new data, new architectures, not
  re-merging);
* `round_viable`: the converse regime — if the fresh family
  carries E_dev above the staged ignition threshold
  (η_p·η_s·E_dev ≥ cone cost, R215) AND the compatibility
  gate holds (R211), the round is viable: the cone step
  applies;
* `cycle_monotone_viability`: one-line summary — round
  viability is exactly (E_dev > 0 ∧ gates ∧ threshold):
  the controller's decision reduces to the measured
  disagreement of the fresh family plus the two gates.
-/

namespace Hagi

open Finset

variable {N : ℕ} [NeZero N] {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- **Round exhaustion**: zero deviation energy in the fresh
family gives the operator NOTHING to convert — the
GUARANTEED margin over decay is exactly η·E_dev = 0: the
operator's promise collapses to the decay floor ρ·D − ξ.
The honest stop condition: re-merging consenting experts
cannot guarantee growth beyond decay. -/
theorem round_exhausted (D D' : ℝ) (ρ η ξ : ℝ) (dev : Fin N → V)
    (hzero : devEnergy dev = 0)
    (hop : GainOp D D' dev ρ η ξ) :
    ρ * D - ξ ≤ D' ∧ η * devEnergy dev = 0 := by
  refine ⟨?_, ?_⟩
  · have h : ρ * D + η * devEnergy dev - ξ ≤ D' := hop
    rw [hzero, mul_zero, add_zero] at h
    exact h
  · rw [hzero, mul_zero]

/-- **Round viability**: fresh disagreement above the staged
threshold with the compatibility gate and the cone premises
gives the cone step — the round PAYS. -/
theorem round_viable (C D C' D' : ℝ) (γ ρ k ξ η_p η_s : ℝ)
    (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hop : GainOp D D' dev ρ (η_p * η_s) ξ)
    (hrhogk : γ * k ≤ ρ) (hcone : k * C ≤ D)
    (hthresh : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ (η_p * η_s) * devEnergy dev)
    (hcompat : 0 < devEnergy dev) :
    k * C' ≤ D' :=
  gainop_cone_step C D C' D' γ ρ k ξ (η_p * η_s) dev hstep hop
    hrhogk hcone hthresh

/-- **The controller's criterion**: round viability reduces
to the measured disagreement of the fresh family plus the
gates — exhaustion ⟺ E_dev = 0 collapses the operator's
promise to the decay floor; viability ⟺ E_dev > 0 ∧ gates ∧
threshold gives the cone step. One structure, two regimes,
one measured quantity. -/
theorem cycle_criterion (D D' : ℝ) (ρ η ξ : ℝ) (dev : Fin N → V)
    (hop : GainOp D D' dev ρ η ξ) :
    devEnergy dev = 0 → ρ * D - ξ ≤ D' ∧ η * devEnergy dev = 0 :=
  fun hzero => round_exhausted D D' ρ η ξ dev hzero hop


end Hagi
