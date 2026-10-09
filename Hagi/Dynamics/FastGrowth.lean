/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.TakeoffCounted
set_option linter.style.header false

/-!
# FastGrowth — нормированный на compute закон прироста capability

* `capability_cumulative`: при `Rext (t+1) ≤ Rext t − Gamma`
  и `c ≤ Gamma` — `Rext T ≤ Rext 0 − T·c`;
* `growth_efficiency_lower` / `growth_efficiency_div`:
  риск-снижение на единицу compute ≥ c/K
  (муль- и деление-формы);
* `capability_multiplicative`: при `C (t+1) ≥ C t·(1+α)` —
  `C T ≥ C 0·(1+α)^T` (T-кратная композиция пошагового
  закона — посылка, не вывод);
* `capability_takeoff_counted`: при
  `C (t+1) ≥ C t·(1+α)^(s t)` —
  `C T ≥ C 0·(1+α)^(Σ s t)` (экспонента по числу успехов);
* `capability_takeoff_floor`: при `N ≤ Σ s t` —
  `C T ≥ C 0·(1+α)^N`;
* `risk_takeoff_counted`: при
  `R (t+1) ≤ R t·(1−β)^(s t)` —
  `R T ≤ R 0·(1−β)^(Σ s t)`;
* `risk_epsilon_floor`: при
  `log(R0/eps)/log(1/(1−β)) ≤ N` —
  `R0·(1−β)^N ≤ eps` (замкнутая форма счётчика успехов
  до ε-пола).

Стохастическая половина (вероятностный слой успеха) —
открыта.
-/

open Real Finset

namespace Hagi

/-- При `Rext (t+1) ≤ Rext t − Gamma` и `c ≤ Gamma`:
`Rext T ≤ Rext 0 − Σ_{t<T} c`. -/
theorem capability_cumulative (Rext : ℕ → ℝ) (Gamma c : ℝ)
    (_hc : 0 < c)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) :
    Rext T ≤ Rext 0 - ∑ _t ∈ Finset.range T, c := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hstep T
      rw [Finset.sum_range_succ]
      calc Rext (T + 1) ≤ Rext T - Gamma := h1
        _ ≤ (Rext 0 - ∑ _t ∈ Finset.range T, c) - Gamma := by linarith
        _ ≤ Rext 0 - (∑ _t ∈ Finset.range T, c + c) := by linarith

/-- При посылках `capability_cumulative`, `0 < K` и
`T ≠ 0`: `(Rext 0 − Rext T)·K ≥ T·c·K`. -/
theorem growth_efficiency_lower (Rext : ℕ → ℝ) (Gamma c K : ℝ)
    (hc : 0 < c) (hK : 0 < K)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) (_hT : T ≠ 0) :
    (Rext 0 - Rext T) * K ≥ (T:ℝ) * c * K := by
  have hcum := capability_cumulative Rext Gamma c hc hstep hG T
  have hsumT : ∑ _t ∈ Finset.range T, c = (T:ℝ) * c := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsumT] at hcum
  have hmul : (Rext 0 - Rext T) * K ≥ ((T:ℝ) * c) * K :=
    mul_le_mul_of_nonneg_right (by linarith) hK.le
  linarith

/-- При посылках `capability_cumulative`, `0 < K < ∞` и
`0 < T`: `c/K ≤ (Rext 0 − Rext T)/(T·K)`. -/
theorem growth_efficiency_div (Rext : ℕ → ℝ) (Gamma c K : ℝ)
    (hc : 0 < c) (hK : 0 < K)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) (hT : (0:ℝ) < (T:ℝ)) :
    c / K ≤ (Rext 0 - Rext T) / ((T:ℝ) * K) := by
  have hTne : T ≠ 0 := by
    cases T with
    | zero => exact absurd hT (by simp)
    | succ n => exact fun h => Nat.succ_ne_zero n h
  have hmain := growth_efficiency_lower Rext Gamma c K hc hK hstep hG T hTne
  rw [div_le_div_iff₀ hK (mul_pos hT hK)]
  nlinarith [hmain, hK, hT]

/-- При `0 < α` и `C (t+1) ≥ C t·(1+α)` для всех t:
`C T ≥ C 0·(1+α)^T` (пошаговый мультипликативный закон —
посылка; заключение — его T-кратная композиция). -/
theorem capability_multiplicative (C : ℕ → ℝ) (_succ : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (_hC0 : 0 ≤ C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hbase : (1 + alpha) ^ (T + 1) = (1 + alpha) ^ T * (1 + alpha) := by
        rw [pow_succ]
      rw [hbase]
      calc C (T + 1) ≥ C T * (1 + alpha) := h1
        _ ≥ (C 0 * (1 + alpha) ^ T) * (1 + alpha) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            linarith
        _ = C 0 * ((1 + alpha) ^ T * (1 + alpha)) := by ring

/-- При `0 < α` и `C (t+1) ≥ C t·(1+α)^(s t)` для всех t:
`C T ≥ C 0·(1+α)^(Σ_{t<T} s t)` (делегация Foundations). -/
theorem capability_takeoff_counted (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) :=
  Hagi.Foundations.capability_takeoff_counted C s alpha halpha hmul T

/-- При `0 < α`, `0 ≤ C 0`, `C (t+1) ≥ C t·(1+α)^(s t)` и
`N ≤ Σ_{t<T} s t` — `C T ≥ C 0·(1+α)^N`. -/
theorem capability_takeoff_floor (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (hC0 : 0 ≤ C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T N : ℕ)
    (hcount : N ≤ ∑ t ∈ Finset.range T, s t) :
    C T ≥ C 0 * (1 + alpha) ^ N := by
  have hlaw := capability_takeoff_counted C s alpha halpha hmul T
  have hmono : (1 + alpha) ^ N ≤ (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) :=
    pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + alpha) hcount
  have hmul2 : C 0 * (1 + alpha) ^ N ≤ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) :=
    mul_le_mul_of_nonneg_left hmono hC0
  linarith

/-- При `β < 1` и `R (t+1) ≤ R t·(1−β)^(s t)`:
`R T ≤ R 0·(1−β)^(Σ_{t<T} s t)`. -/
theorem risk_takeoff_counted (R : ℕ → ℝ) (s : ℕ → ℕ)
    (beta : ℝ) (_hbeta : 0 < beta) (hbeta1 : beta < 1)
    (hmul : ∀ t, R (t + 1) ≤ R t * (1 - beta) ^ (s t))
    (T : ℕ) :
    R T ≤ R 0 * (1 - beta) ^ (∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hsum : ∑ t ∈ Finset.range (T + 1), s t
          = (∑ t ∈ Finset.range T, s t) + s T :=
        Finset.sum_range_succ s T
      have hpow : (1 - beta) ^ ((∑ t ∈ Finset.range T, s t) + s T)
          = (1 - beta) ^ (∑ t ∈ Finset.range T, s t) * (1 - beta) ^ (s T) :=
        pow_add _ _ _
      have hfac : (0:ℝ) ≤ (1 - beta) ^ (∑ t ∈ Finset.range T, s t) := by positivity
      rw [hsum, hpow]
      calc R (T + 1) ≤ R T * (1 - beta) ^ (s T) := h1
        _ ≤ (R 0 * (1 - beta) ^ (∑ t ∈ Finset.range T, s t)) * (1 - beta) ^ (s T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            positivity
        _ = R 0 * ((1 - beta) ^ (∑ t ∈ Finset.range T, s t) * (1 - beta) ^ (s T)) := by
            ring

/-- При `0 < eps`, `0 < R0`, `0 < β < 1` и
`log(R0/eps)/log(1/(1−β)) ≤ N` —
`R0·(1−β)^N ≤ eps`. -/
theorem risk_epsilon_floor (R0 eps beta : ℝ) (N : ℕ)
    (heps : 0 < eps) (hR0pos : 0 < R0) (_hR0e : eps ≤ R0)
    (hbeta : 0 < beta) (hbeta1 : beta < 1)
    (hN : Real.log (R0 / eps) / Real.log (1 / (1 - beta)) ≤ (N:ℝ)) :
    R0 * (1 - beta) ^ N ≤ eps := by
  have h1m1 : (0:ℝ) < 1 - beta := by linarith
  have hlt1 : 1 - beta < 1 := by linarith
  have hlnneg : Real.log (1 - beta) < 0 := Real.log_neg h1m1 hlt1
  have hinvgt1 : 1 < 1 / (1 - beta) := by
    rw [lt_div_iff₀ h1m1]; linarith
  have hlogpos : (0:ℝ) < Real.log (1 / (1 - beta)) := Real.log_pos hinvgt1
  -- key: N * (-ln(1-β)) ≥ ln(R0/ε) from hN
  have hkey : Real.log (R0 / eps) ≤ (N:ℝ) * (-Real.log (1 - beta)) := by
    have h3 : Real.log (1 / (1 - beta)) = -Real.log (1 - beta) := by
      rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by linarith : ((1:ℝ) - beta) ≠ 0)]
      simp
    have hmul : (Real.log (R0 / eps) / Real.log (1 / (1 - beta)))
        * Real.log (1 / (1 - beta)) ≤ (N:ℝ) * Real.log (1 / (1 - beta)) :=
      mul_le_mul_of_nonneg_right hN hlogpos.le
    have hcancel : (Real.log (R0 / eps) / Real.log (1 / (1 - beta)))
        * Real.log (1 / (1 - beta)) = Real.log (R0 / eps) := by
      field_simp
    rw [hcancel] at hmul
    rw [h3] at hmul
    exact hmul
  -- ln(R0·(1-β)^N) = ln R0 + N ln(1-β) ≤ ln ε
  have hpowpos : (0:ℝ) < (1 - beta) ^ N := by positivity
  have hlogmul : Real.log (R0 * (1 - beta) ^ N)
      = Real.log R0 + (N:ℝ) * Real.log (1 - beta) := by
    rw [Real.log_mul hR0pos.ne' hpowpos.ne', Real.log_pow]
  have hlogle : Real.log (R0 * (1 - beta) ^ N) ≤ Real.log eps := by
    rw [hlogmul]
    have hdiv : Real.log (R0 / eps) = Real.log R0 - Real.log eps :=
      Real.log_div hR0pos.ne' heps.ne'
    rw [hdiv] at hkey
    linarith
  exact (Real.log_le_log_iff (by positivity : (0:ℝ) < R0 * (1 - beta) ^ N) heps).mp hlogle

end Hagi
