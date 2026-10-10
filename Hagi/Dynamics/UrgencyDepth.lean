/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.EndpointContraction

/-!
# UrgencyDepth — срочность выбирает конфигурацию

* `depth_capped_by_time`: при `0 < δ` и `T·δ ≤ τ` —
  `T ≤ τ/δ`;
* `shallow_misses_tube`: при `(1/κ)^T₀ = x₀/ε` и `T < T₀` —
  `(1/κ)^T < x₀/ε` (мелкая конфигурация не достигает
  ε-трубки); κ ∈ (0,1), `ε > 0`;
* `patient_configuration_reaches`: при
  `x 0/ε ≤ (1/κ)^T₀` — `x T₀ ≤ β·cbar/(1−κ) + ε`
  (композиция с `endpoint_depth_budget`).
-/

namespace Hagi.Dynamics

/-- При `0 < δ` и `(T:ℝ)·δ ≤ τ`: `(T:ℝ) ≤ τ/δ`. -/
theorem depth_capped_by_time (τ δ : ℝ) (T : ℕ)
    (hδ : 0 < δ)
    (hfit : (T : ℝ) * δ ≤ τ) :
    (T : ℝ) ≤ τ / δ := by
  rw [le_div_iff₀ hδ]
  exact hfit

/-- При `0 < κ < 1`, `0 < ε`, `(1/κ)^T₀ = x₀/ε` и `T < T₀`:
`(1/κ)^T < x₀/ε` — бюджет глубины `endpoint_depth_budget`
не выполнен. -/
theorem shallow_misses_tube (κ x₀ ε : ℝ) (T₀ T : ℕ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (heps : 0 < ε) (_hx₀ : 0 < x₀)
    (hneed : (1 / κ) ^ T₀ = x₀ / ε)
    (hshort : T < T₀) :
    (1 / κ) ^ T < x₀ / ε := by
  have hone : 1 < 1 / κ := one_lt_one_div hκ hκ1
  have hmono := pow_lt_pow_right₀ hone hshort
  rw [hneed] at hmono
  exact hmono

/-- При посылках `endpoint_depth_budget` и
`x 0/ε ≤ (1/κ)^T₀` — `x T₀ ≤ β·cbar/(1−κ) + ε`. -/
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

end Hagi.Dynamics

namespace Hagi
export Hagi.Dynamics (depth_capped_by_time shallow_misses_tube patient_configuration_reaches)
end Hagi
