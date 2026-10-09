/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.ChainToCone

/-!
# T3Ignition — условие зажигания конуса через эффективную конверсию

* `ignitionGate`: `(cbeta − (1−ρ)k)/k²`; `ignitionGate_nonneg` —
  неотрицательность при `0 < k` и `(1−ρ)k ≤ cbeta`;
* `ignitionCeiling`: `min(ρ/k, (cbeta − (1−ρ)k)/k²)`;
  `ignitionCeiling_pos` — положительность при `0 < k`,
  `0 < ρ`, `(1−ρ)k < cbeta`;
* `T3_ignition`: если `β⁴·κ ≤ ignitionCeiling` и выполнены
  сертификаты `takeoff_from_certificate` (стадийные полы β,
  κ-доля, шаг, верхняя лента прироста на той же ставке
  `β⁴κ`, динамика), то `C 0·(1 + β⁴κ·k)^T ≤ C T`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- `ignitionGate rho cbeta k = (cbeta − (1−ρ)k)/k²`. -/
noncomputable def ignitionGate (rho cbeta k : ℝ) : ℝ :=
  (cbeta - (1 - rho) * k) / k ^ 2

/-- При `0 < k` и `(1−ρ)·k ≤ cbeta` выполнено
`0 ≤ ignitionGate rho cbeta k`. -/
theorem ignitionGate_nonneg (rho cbeta k : ℝ)
    (hk : 0 < k) (hdom : (1 - rho) * k ≤ cbeta) :
    0 ≤ ignitionGate rho cbeta k := by
  unfold ignitionGate
  apply div_nonneg _ (by positivity)
  linarith

/-- `ignitionCeiling rho cbeta k = min(ρ/k, (cbeta − (1−ρ)k)/k²)`. -/
noncomputable def ignitionCeiling (rho cbeta k : ℝ) : ℝ :=
    min (rho / k) ((cbeta - (1 - rho) * k) / k ^ 2)

theorem ignitionCeiling_pos (rho cbeta k : ℝ)
    (hk : 0 < k) (hrho : 0 < rho)
    (hdom : (1 - rho) * k < cbeta) :
    0 < ignitionCeiling rho cbeta k := by
  unfold ignitionCeiling
  have h1 : 0 < rho / k := div_pos hrho hk
  have h2 : 0 < (cbeta - (1 - rho) * k) / k ^ 2 := by
    apply div_pos _ (by positivity)
    nlinarith
  exact lt_min_iff.mpr ⟨h1, h2⟩

/-- При `0 < k`, `0 < ρ` и `(1−ρ)·k < cbeta` выполнено
`0 < ignitionCeiling rho cbeta k`. -/
theorem T3_ignition
    (C D G : ℕ → ℝ) (stages : ℕ → DisagreementStages)
    (T : ℕ) (beta kappa rho cbeta k : ℝ)
    (hβ : 0 < beta) (hκ : 0 < kappa) (hk : 0 < k)
    (hceiling : beta^4 * kappa ≤ ignitionCeiling rho cbeta k)
    -- runtime certificates (R247 vocabulary)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hcert : ∀ t ∈ Finset.range T, beta ≤ (stages t).α_align
      ∧ beta ≤ (stages t).α_trunc
      ∧ beta ≤ (stages t).α_safe ∧ beta ≤ (stages t).α_cap)
    (hdiv : ∀ t ∈ Finset.range T,
      kappa * D t ≤ (stages t).E_raw)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hG : ∀ t ∈ Finset.range T,
      (stages t).G_cap = G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ (beta^4 * kappa) * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + cbeta * C t ≤ D (t + 1))
    (hcone0 : k * C 0 ≤ D 0) :
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T := by
  -- распаковка потолка в два условия конуса
  have hγpos : 0 < beta^4 * kappa := by positivity
  unfold ignitionCeiling at hceiling
  have hsupport : (beta^4 * kappa) * k ≤ rho := by
    have := le_trans hceiling (min_le_left _ _)
    have h1 : beta^4 * kappa ≤ rho / k := this
    have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hk
    have h2 : beta^4 * kappa * k ≤ rho / k * k :=
      mul_le_mul_of_nonneg_right h1 hk.le
    rwa [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hk0] at h2
  have hcurv : (beta^4 * kappa) * k ^ 2 + (1 - rho) * k ≤ cbeta := by
    have h1 := le_trans hceiling (min_le_right _ _)
    have hk2 : (0:ℝ) < k ^ 2 := by positivity
    have hk20 : ((k:ℝ)) ^ 2 ≠ 0 := ne_of_gt hk2
    have h3 : beta^4 * kappa ≤ (cbeta - (1 - rho) * k) / k ^ 2 := h1
    have h4 : beta^4 * kappa * k ^ 2
        ≤ (cbeta - (1 - rho) * k) / k ^ 2 * k ^ 2 :=
      mul_le_mul_of_nonneg_right h3 hk2.le
    rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hk20] at h4
    linarith
  -- применяем конус-мост с точной лентой
  exact takeoff_from_certificate C D G stages T
    beta kappa (beta^4 * kappa) rho cbeta k
    hβ.le hκ.le hk.le hD hC hcert hdiv hstep hG hup hdyn
    hsupport hcurv hcone0



end Hagi.Growth
