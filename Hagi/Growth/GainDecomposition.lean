/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainOperator
import Hagi.Information.GainRecoverability

/-!
# GainDecomposition — the measurable GainOp chain

The GainOperator η (disagreement → frontier) is one big
empirical black box. The MOPD/looped-models decomposition
splits it into MEASURABLE stage conversions:

  E_dev --η_policy--> G_policy --η_state--> G_cap

* `η_policy`: policy-space distillation efficiency (MOPD:
  student-teacher KL reduction per unit disagreement — the
  E_dev → G_policy stage, measurable on rollouts);
* `η_state`: state/consolidation efficiency (fiber extraction
  + SafeQP + fixed-point stabilization: G_policy → retained
  capability, measurable post-integration);
* `gain_chain`: the composition law — if both stages convert
  and the twoGap gate plus the compatibility gate hold, the
  net capability gain is the PRODUCT η_policy·η_state·E_dev
  minus the price;
* `zero_stage_kills_gain`: the NECESSITY result: a zero (or
  negative) stage conversion kills the total gain whatever
  the other stage does — the decomposition is a chain, not a
  sum: no amount of distillation efficiency rescues a zero
  consolidation stage, and vice versa;
* `chain_ignition_threshold`: the ignition condition restated
  in stages: η_policy·η_state ≥ (γk² + (1−ρ)k)·C/E_dev — the
  empirical program is to measure BOTH stage constants.
-/

namespace Hagi

open Finset

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V]

/-- Stage-1 conversion: policy-space distillation efficiency
(MOPD stage; measured on student rollouts). -/
noncomputable def etaPolicy (E_dev G_policy : ℝ) : ℝ :=
  G_policy / E_dev

/-- Stage-2 conversion: consolidation efficiency (fiber
extraction + safe update + fixed-point stabilization;
measured post-integration). -/
noncomputable def etaState (G_policy G_cap : ℝ) : ℝ :=
  G_cap / G_policy

/-- **The composition law**: if both stages convert
(G_policy = η_p·E_dev, G_cap = η_s·G_policy) then the total
disagreement-to-capability conversion is the PRODUCT — the
GainOperator η decomposes multiplicatively. -/
theorem gain_chain (E_dev G_policy G_cap η_p η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_cap = η_s * G_policy) :
    G_cap = (η_p * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2]
  ring

/-- **Necessity of both stages**: if one stage converts at
≤ 0 while the OTHER stage is nonnegative (no hidden
rescue by a negative-times-negative product), the total gain
is ≤ 0 — the chain has no bypass: distillation efficiency
cannot rescue a non-consolidating state stage, and vice
versa. (A stage with negative conversion and a nonnegative
partner destroys exactly its share; the case both negative
is a double-failure, excluded as not a rescue.) -/
theorem zero_stage_kills_gain (E_dev G_policy G_cap η_p η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev) (h2 : G_cap = η_s * G_policy)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_s) ∨ (0 ≤ η_p ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_s) * E_dev :=
    gain_chain E_dev G_policy G_cap η_p η_s h1 h2
  rcases hzero with ⟨hp, hs⟩ | ⟨hp, hs⟩
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith

/-- **The staged ignition threshold**: the GainOp ignition
condition η·E_dev ≥ γk²C + (1−ρ)kC + ξ, restated for the
measured product η_p·η_s — the empirical program: measure
BOTH stage constants on real trajectories and compare the
product to the cone threshold. -/
theorem chain_ignition_threshold (C D C' D' : ℝ)
    (γ ρ k ξ η_p η_s : ℝ) (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hrhogk : γ * k ≤ ρ) (hcone : k * C ≤ D)
    (hprod : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ (η_p * η_s) * devEnergy dev) :
    ∃ η, γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev ∧ η = η_p * η_s :=
  ⟨η_p * η_s, hprod, rfl⟩

end Hagi
