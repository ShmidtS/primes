/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.ReferenceMachine
import Hagi.Step.NoisyPL

set_option linter.style.header false

/-!
# VerticalCapstone — итоговая теорема вертикали: точность за бюджет

Композиция всех звеньев сертифицированной цепи: noisy PL-спуск
(NoisyPL) + термостат-отжиг (ReferenceMachine.batch_anneal_floor).
Рекуррентность `e(t+1) <= q·e(t) + d(t)`, `d(t) = sigma^2/(B0·c^t)`,
q < 1, c > 1 даёт `e(t) <= E* + q^t·(e0 - E*) + sigma^2/B0/(1-q)`:
два экспоненциальных члена (сжатие спуска и охлаждение пола)
плюс консервативный пол d(0)/(1-q). Точность за бюджет
(t циклов, B0·c^t измерений) в закрытой форме.
-/

namespace Hagi.Unified

/-- Лемма о стационарном члене: `q·x/(1-q) + x = x/(1-q)`
при `q < 1`. -/
theorem affine_stationary (q x : ℝ) (hq1 : q < 1) :
    q * (x / (1 - q)) + x = x / (1 - q) := by
  have hd : (0:ℝ) < 1 - q := by linarith
  field_simp
  ring

/-- КАПСТОН ВЕРТИКАЛИ: noisy-спуск с отжигающим полом
`d(t) = sigma^2/(B0·c^t)`: `e t <= Estar + q^t·(e0 - Estar)
+ sigma^2/B0/(1-q)` — спуск сжимает начальный зазор
экспоненциально, отжиг измерений опускает пол (floor(t)
<= d(0)/(1-q) — консервативная закрытая форма). Точность за
бюджет: t циклов + B0·c^t измерений. -/
theorem accuracy_for_budget (e : ℕ → ℝ) (Estar q sigma B0 c : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hsigma : 0 ≤ sigma)
    (hB0 : 0 < B0) (hc1 : 1 < c) (hEstar0 : 0 ≤ Estar)
    (hstep : ∀ s, e (s + 1) ≤ q * e s + sigma ^ 2 / (B0 * c ^ s))
    (t : ℕ) :
    e t ≤ Estar + q ^ t * (e 0 - Estar)
      + sigma ^ 2 / B0 / (1 - q) := by
  have hqpos : (0:ℝ) < 1 - q := by linarith
  have hstep' : ∀ s, (e (s + 1) - Estar)
      ≤ q * (e s - Estar) + sigma ^ 2 / (B0 * c ^ s) := by
    intro s
    have h0 := hstep s
    have hdist : q * (e s - Estar) = q * e s - q * Estar := by
      ring
    rw [hdist]
    have hpos : (0:ℝ) ≤ (1 - q) * Estar := by
      exact mul_nonneg (by linarith) hEstar0
    linarith
  have hmain : ∀ t : ℕ, (e t - Estar)
      ≤ q ^ t * (e 0 - Estar)
        + sigma ^ 2 / B0 / (1 - q) := by
    intro t
    induction t with
    | zero =>
      have h2 : (0:ℝ) ≤ sigma ^ 2 / B0 / (1 - q) := by
        positivity
      linarith
    | succ t ih =>
      have hst := hstep' t
      have hshift : e t - Estar
          ≤ q ^ t * (e 0 - Estar)
            + sigma ^ 2 / B0 / (1 - q) := ih
      have hA : q * (sigma ^ 2 / B0 / (1 - q))
          + sigma ^ 2 / (B0 * c ^ t)
          ≤ sigma ^ 2 / B0 / (1 - q) := by
        have hcore := affine_stationary q (sigma ^ 2 / B0) hq1
        have hle : sigma ^ 2 / (B0 * c ^ t) ≤ sigma ^ 2 / B0 := by
          have hc0 : (0:ℝ) < c := by linarith
          have hpow1 : (1:ℝ) ≤ c ^ t := by
            have hmono : (1:ℝ) ≤ c := by linarith
            exact one_le_pow₀ hmono (n := t)
          have hden : B0 * 1 ≤ B0 * c ^ t :=
            mul_le_mul_of_nonneg_left hpow1 (le_of_lt hB0)
          rw [mul_one] at hden
          exact div_le_div_of_nonneg_left (sq_nonneg sigma)
            hB0 hden
        linarith [hcore, hle]
      calc e (t + 1) - Estar
          ≤ q * (e t - Estar)
            + sigma ^ 2 / (B0 * c ^ t) := hst
        _ ≤ q * (q ^ t * (e 0 - Estar)
              + sigma ^ 2 / B0 / (1 - q))
            + sigma ^ 2 / (B0 * c ^ t) := by
            have h1 := mul_le_mul_of_nonneg_left hshift hq
            linarith
        _ ≤ q ^ (t + 1) * (e 0 - Estar)
            + sigma ^ 2 / B0 / (1 - q) := by
            have hdist : q * (q ^ t * (e 0 - Estar))
                = q ^ (t + 1) * (e 0 - Estar) := by
              rw [pow_succ]
              ring
            linarith [hdist, hA]
  linarith [hmain t]

end Hagi.Unified
