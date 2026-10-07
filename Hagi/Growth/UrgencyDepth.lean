/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.EndpointContraction

/-!
# UrgencyDepth — urgency selects the configuration

The heterarchy paper's urgency principle, formalized for the
looped HAGI core: available time selects the active
configuration — fast contexts take the shallow path, patient
contexts may recurse toward the fixed point.

* `depth_capped_by_time` — the load-bearing trivial bound:
  a trajectory within the budget has depth ≤ τ/δ;
* `shallow_misses_tube` — THE NECESSITY RESULT: if the
  κ-contraction needs exactly T₀ steps to bring the
  initial-condition part under ε ((1/κ)^{T₀} = x₀/ε), any
  strictly shallower run is still OUTSIDE the ε-tube —
  urgency trades depth for accuracy;
* `patient_configuration_reaches` — the converse: with T₀
  steps the endpoint budget applies — the patient
  configuration needs no architecture change, only time.
-/

namespace Hagi

/-- **Depth is capped by time**: a trajectory of T steps at
per-step cost δ fits the budget τ only if T ≤ τ/δ. -/
theorem depth_capped_by_time (τ δ : ℝ) (T : ℕ)
    (hδ : 0 < δ)
    (hfit : (T : ℝ) * δ ≤ τ) :
    (T : ℝ) ≤ τ / δ := by
  rw [le_div_iff₀ hδ]
  exact hfit

/-- **Shallow misses the tube**: if T₀ steps are exactly
enough ((1/κ)^{T₀} = x₀/ε) and the context runs strictly
fewer (T < T₀), then (1/κ)^T < x₀/ε — the depth budget of
`endpoint_depth_budget` is UNSATISFIED: the shallow
configuration cannot reach the tolerance. Urgency trades
depth for accuracy. -/
theorem shallow_misses_tube (κ x₀ ε : ℝ) (T₀ T : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (heps : 0 < ε) (_hx₀ : 0 < x₀)
    (hneed : (1 / κ) ^ T₀ = x₀ / ε)
    (hshort : T < T₀) :
    (1 / κ) ^ T < x₀ / ε := by
  have hone : 1 < 1 / κ := one_lt_one_div hκ hκ1
  have hmono := pow_lt_pow_right₀ hone hshort
  rw [hneed] at hmono
  exact hmono

/-- **The patient configuration reaches**: with exactly T₀
steps the endpoint depth budget applies — reaching the tube
needs no architecture change, only time. (Composition with
`endpoint_depth_budget`: its premise is exactly the budget
inequality satisfied at T₀.) -/
theorem patient_configuration_reaches (x c : ℕ → ℝ)
    (κ β cbar ε x₀ : ℝ) (T₀ : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hβ : 0 ≤ β)
    (hcbar : 0 ≤ cbar) (heps : 0 < ε) (hx₀ : 0 < x₀)
    (hcbound : ∀ t, c t ≤ cbar)
    (hstep : ∀ t, x (t + 1) ≤ κ * x t + β * c t)
    (hneed : x 0 / ε ≤ (1 / κ) ^ T₀) :
    x T₀ ≤ β * cbar / (1 - κ) + ε :=
  endpoint_depth_budget x c κ β cbar ε T₀ hκ hκ1 hβ hcbar
    hcbound hstep heps hneed

end Hagi
