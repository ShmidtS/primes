/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.CertifiedEstimator
import Hagi.Budget.ThermoCondensation
set_option linter.style.header false

/-!
# Anytime-мониторинг ⟹ конденсационный бюджет (R528)

Мост anytime-лестницы (CertifiedEstimator) с термодинамической
конденсацией (ThermoCondensation): если статистика g остаётся
в anytime-безопасной полосе радиуса u = √(2σ²ln(T/α))
(пустой bad-set, вероятность ≤ α по `anytime_safe_threshold`),
то девиация каркаса d = g − μ удерживается в 2u, и перестройка
живого каркаса стоит не больше u² = 2σ²ln(T/α) CE.
Динамическая версия тезиса «1,5% каркаса»: мониторинг с уровнем
α сертифицирует конденсацию без переобучения.
-/

namespace Hagi

open Real Finset

/-- Пустой anytime-bad-set ⟹ точечная полоса: g v < μ + u для всех v. -/
theorem pointwise_upper_band {V : Type*} [Fintype V]
    (g : V → ℝ) (μ u : ℝ) (T : ℕ) (hT : 0 < T)
    (hempty : ∀ v, ¬ ∃ t < T, μ + u ≤ g v) (v : V) : g v < μ + u := by
  by_contra hc
  push Not at hc
  exact hempty v ⟨0, hT, hc⟩

/-- **Anytime ⟹ конденсация (R528)**: при CGF-ограниченной статистике
g (subGauss σ²), если anytime-bad-set пуст (событие, чья вероятность
≤ α по `anytime_safe_threshold`), то перестройка softmax-каркаса
девиацией d = g − μ стоит не больше u² = 2σ²·ln(T/α) CE, где
u = √(2σ²·ln(T/α)) — anytime-полоса. Композиция: точечная полоса
(пустой bad-set) + triangle-девиация + `condensation_epsilon_to_gap`. -/
theorem anytime_condensation {k : Type} [Fintype k] [Nonempty k]
    (q g : k → ℝ) (m : k → ℝ) (t : k) (μ σ2 α : ℝ) (T : ℕ)
    (hT : 0 < T) (hq : ∀ v, 0 < q v) (hq1 : ∑ v : k, q v = 1)
    (hs2 : 0 < σ2) (hα : 0 < α) (hα1 : α < 1)
    (hcgf : ∀ n : ℕ, ∀ c : ℝ, 0 < c →
      Real.log (∑ v : k, q v * Real.exp (c * (g v - μ)))
        ≤ c ^ 2 * σ2 / 2)
    (hempty : ∀ v : k, ¬ ∃ s < T, μ + Real.sqrt (2 * σ2 * Real.log ((T:ℝ) / α)) ≤ g v)
    (hempty2 : ∀ v : k, ¬ ∃ s < T, μ + Real.sqrt (2 * σ2 * Real.log ((T:ℝ) / α)) ≤ 2 * μ - g v)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.ceOneHot t (fun v => m v + (g v - μ)) / 2
      + Hagi.ceOneHot t (fun v => m v - (g v - μ)) / 2
      - Hagi.ceOneHot t m ≤ 2 * σ2 * Real.log ((T:ℝ) / α) := by
  have hT1 : (1:ℝ) ≤ (T:ℝ) := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hT.ne')
  have hTα : (1:ℝ) < (T:ℝ) / α := one_lt_div hα |>.2 (by linarith)
  set u : ℝ := Real.sqrt (2 * σ2 * Real.log ((T:ℝ) / α)) with hu
  have hlogpos : 0 < Real.log ((T:ℝ) / α) := Real.log_pos (by linarith)
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hε : 0 < u ^ 2 := by positivity
  have hbandU : ∀ v, g v - μ < u := fun v => by
    have hb := pointwise_upper_band g μ u T hT hempty v
    linarith
  have hbandL : ∀ v, -u < g v - μ := fun v => by
    have hb := pointwise_upper_band (fun v => 2 * μ - g v) μ u T hT hempty2 v
    linarith
  have hdev : ∀ a b : k, |(g a - μ) - (g b - μ)| ≤ 2 * u := by
    intro a b
    have ha := hbandU a
    have hb := hbandU b
    have la := hbandL a
    have lb := hbandL b
    rw [abs_le]
    constructor <;> linarith
  have h2u : ∀ a b : k, |(g a - μ) - (g b - μ)| ≤ 2 * Real.sqrt (u ^ 2) := by
    intro a b
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu0]
    exact hdev a b
  have hval : u ^ 2 = 2 * σ2 * Real.log ((T:ℝ) / α) := by
    rw [hu, Real.sq_sqrt (by positivity)]
  exact (condensation_epsilon_to_gap m (fun v => g v - μ) t (u ^ 2) hp hsum hε
    h2u).trans (le_of_eq hval)

end Hagi
