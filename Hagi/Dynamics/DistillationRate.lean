/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.EndpointContraction

/-!
# DistillationRate — бюджет rollout-ов для policy KL

Стадия E_dev → G_policy при пошаговой контракции KL
`kl (t+1) ≤ κ_KL·kl t` (измеряемая посылка MOPD-режима).

* `kl_contraction_budget`: при `0 < κ_KL < 1`, `0 < δ` и
  `kl 0/δ ≤ (1/κ_KL)^T` — `kl T ≤ δ` (бюджет логарифмичен
  в начальном зазоре);
* `kl_half_steps`: при `κ_KL = 1/2` —
  `kl T ≤ KL₀·(1/2)^T` (каждый rollout — бит близости).
-/

namespace Hagi

/-- При `0 < κ_KL < 1`, `0 < δ`, `kl (t+1) ≤ κ_KL·kl t` и
`kl 0/δ ≤ (1/κ_KL)^T` — `kl T ≤ δ`. -/
theorem kl_contraction_budget (kl : ℕ → ℝ) (κ_KL δ : ℝ)
    (T : ℕ) (hκ : 0 < κ_KL) (hκ1 : κ_KL < 1)
    (hδ : 0 < δ)
    (hstep : ∀ t, kl (t + 1) ≤ κ_KL * kl t)
    (hneed : kl 0 / δ ≤ (1 / κ_KL) ^ T) :
    kl T ≤ 0 + δ := by
  have h := endpoint_depth_budget kl (fun _ => (0:ℝ)) κ_KL 0 0 δ T
    hκ hκ1 (le_refl 0) (le_refl 0) (fun _ => le_refl 0)
    (fun t => by simpa using hstep t) hδ hneed
  simpa using h

/-- При `kl 0 ≤ KL₀` и `kl (t+1) ≤ (1/2)·kl t` —
`kl T ≤ KL₀·(1/2)^T`. -/
theorem kl_half_steps (kl : ℕ → ℝ) (KL₀ : ℝ) (T : ℕ)
    (h0 : kl 0 ≤ KL₀) (_hKL₀ : 0 ≤ KL₀)
    (hstep : ∀ t, kl (t + 1) ≤ (1 / 2 : ℝ) * kl t) :
    kl T ≤ KL₀ * (1 / 2 : ℝ) ^ T := by
  have hpos : (0:ℝ) < 1 / 2 := by norm_num
  have hκ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hstep' : ∀ t, kl (t + 1) ≤ (1 / 2 : ℝ) * kl t + 0 * 0 :=
    fun t => by simpa using hstep t
  have hmain := endpoint_bivariate_bound kl (fun _ => (0:ℝ))
    (1 / 2 : ℝ) 0 T (le_of_lt hpos) hκ1 (le_refl 0) hstep'
  have hsum : ∑ i ∈ Finset.range T, (1 / 2 : ℝ) ^ i * 0
      = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [mul_comm, mul_zero]
  rw [hsum, mul_zero, add_zero] at hmain
  have hhalf : (1 / 2 : ℝ) ^ T * kl 0 ≤ (1 / 2 : ℝ) ^ T * KL₀ :=
    mul_le_mul_of_nonneg_left h0 (pow_nonneg (le_of_lt hpos) T)
  calc kl T ≤ (1 / 2 : ℝ) ^ T * kl 0 := hmain
    _ ≤ (1 / 2 : ℝ) ^ T * KL₀ := hhalf
    _ = KL₀ * (1 / 2 : ℝ) ^ T := by ring

end Hagi
