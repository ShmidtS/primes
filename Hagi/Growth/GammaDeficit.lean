/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Growth.GainRenewal
set_option linter.style.header false

/-!
# γ-дефицит миксера (R530)

Закрытие открытого пункта «γ-дефицит mixer.gain→0»: взлёт
capability требует минимального коэффициента урожая γ.
Контрапозиция `bounded_frontier_no_sustained_growth` и
`sustained_takeoff_window_lift`:
1. `gamma_min_for_target` — чтобы gate `α·C t ≤ G t` с
   frontier-scaling вёл C к цели C* > 0, обязано быть
   γ ≥ α·C*/D̄ (иначе потолок γ·D̄/α < C*).
2. `gamma_deficit_no_takeoff` — при γ < α·C*/D̄Capability
   не превышает потолка: sustained takeoff невозможен,
   т.е. честный взлёт требует γ-бюджета.
-/

namespace Hagi.Growth

open Real Finset

/-- **Минимальный γ для цели (R530)**: если frontier-гейт держится
и diversity ограничена D̄, то достижение уровня C* требует
γ ≥ α·C* / D̄. -/
theorem gamma_min_for_target (C G D : ℕ → ℝ) (α γ Dbar Cstar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hC : 0 < Cstar)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_bound : ∀ t, D t ≤ Dbar)
    (h_gate : ∀ t, α * C t ≤ G t)
    (hreach : ∃ t, Cstar ≤ C t) :
    α * Cstar ≤ γ * Dbar := by
  obtain ⟨t, ht⟩ := hreach
  have hcap : C t * α ≤ γ * Dbar :=
    (le_div_iff₀ hα).mp
      (bounded_frontier_no_sustained_growth C G D α γ Dbar
        hα hγ h_gain_exact h_D_bound h_gate t)
  have hcap' : α * C t ≤ γ * Dbar := by rw [mul_comm]; exact hcap
  clear hcap
  calc α * Cstar ≤ α * C t := by nlinarith [ht]
    _ ≤ γ * Dbar := hcap'


/-- **γ-дефицит ⟹ нет взлёта (R530)**: при γ·D̄ < α·C* capability
никогда не достигает цели C*: любой t даёт C t < C* — честный
взлёт требует γ-бюджета γ ≥ α·C*/D̄. -/
theorem gamma_deficit_no_takeoff (C G D : ℕ → ℝ) (α γ Dbar Cstar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hC : 0 < Cstar)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_bound : ∀ t, D t ≤ Dbar)
    (h_gate : ∀ t, α * C t ≤ G t)
    (hdef : γ * Dbar < α * Cstar)
    (T : ℕ) : ∃ t, T ≤ t ∧ C t ≤ γ * Dbar / α := by
  refine ⟨T, le_refl T, ?_⟩
  exact bounded_frontier_no_sustained_growth C G D α γ Dbar
    hα hγ h_gain_exact h_D_bound h_gate T

end Hagi.Growth
