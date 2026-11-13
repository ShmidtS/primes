/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.System.GrowthState
import Hagi.Probability.ConditionalSuccess
import Hagi.Probability.CertifiedEstimator
import Hagi.Growth.GainDecomposition

set_option linter.style.header false

/-!
# GrowthBridge — consolidated growth bridges (C238, A5 R3 slice 5)

Byte-identical merge of FastGrowth, WallClockTakeoff,
FrontierProduction, GrowthGate, ChainToCone, T3Ignition and the
former Unified.GrowthBridge. Namespace blocks and declaration
FQNs preserved; see .tmp/C238/ for the census receipt.
-/

section C238_fastgrowth
/-!
# Foundations.TakeoffCounted — считанный takeoff

Каноническое детерминированное ядро takeoff-подсчёта: чистая
индукция без Hagi-зависимостей.
-/

open Finset

namespace Hagi.Foundations

/-- Если каждый цикл даёт `C (t + 1) ≥ C t * (1 + alpha) ^ (s t)`
со счётчиками `s t ∈ ℕ`, то
`C T ≥ C 0 * (1 + alpha) ^ (∑ t < T, s t)`: рост
экспоненциален по числу успехов, неуспехи нейтральны. -/
theorem capability_takeoff_counted (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hsum : ∑ t ∈ Finset.range (T + 1), s t
          = (∑ t ∈ Finset.range T, s t) + s T :=
        Finset.sum_range_succ s T
      have hpow : (1 + alpha) ^ ((∑ t ∈ Finset.range T, s t) + s T)
          = (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T) :=
        pow_add _ _ _
      rw [hsum, hpow]
      have hpowpos : (0:ℝ) < (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
        positivity
      calc C (T + 1) ≥ C T * (1 + alpha) ^ (s T) := h1
        _ ≥ (C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t)) * (1 + alpha) ^ (s T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            positivity
        _ = C 0 * ((1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T)) := by
            ring

end Hagi.Foundations
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

namespace Hagi.Dynamics

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

/-- При `0 < α`, `0 ≤ C 0`, `C (t+1) ≥ C t·(1+α)^(s t)` и
`N ≤ Σ_{t<T} s t` — `C T ≥ C 0·(1+α)^N`. -/
theorem capability_takeoff_floor (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (hC0 : 0 ≤ C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T N : ℕ)
    (hcount : N ≤ ∑ t ∈ Finset.range T, s t) :
    C T ≥ C 0 * (1 + alpha) ^ N := by
  have hlaw := Hagi.Foundations.capability_takeoff_counted C s alpha halpha hmul T
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

end Hagi.Dynamics

namespace Hagi

end Hagi

end C238_fastgrowth
section C238_wallclock
/-!
# WallClockTakeoff — takeoff в астрономическом (wall-clock) времени

Пер-цикловый закон (посылка): цикл t стоит τ_t wall-clock и
умножает capability на `≥ (1 + k·τ_t)`.

* `log_one_add_ge_sub_half_sq` / `exp_le_one_add`:
  `x − x²/2 ≤ log(1+x)` и `exp(x − x²/2) ≤ 1 + x` при x ≥ 0
  (без ограничения x ≤ 1);
* `per_cycle_time_rate`: определение гипотезы;
* `wallclock_takeoff_product`: `C T ≥ C 0·∏(1 + k·τ t)`;
* `wallclock_takeoff`: `C T ≥ C 0·exp(k·Στ − (k²/2)·Στ²)` —
  экспонента с явным второпорядковым слэком;
* `wallclock_takeoff_small_steps`: при `k·τ t ≤ η` —
  `C T ≥ C 0·exp(k·T_wall·(1 − η/2))`;
* `counted_takeoff_exp`: при
  `C (t+1) ≥ C t·exp(a·s t)` — `C T ≥ C 0·exp(a·Σs t)`;
* `wallclock_rate_from_cone`: при пер-цикловом множителе
  `(1+α)^(s t)`, полу успеха `p₀·T − Δ ≤ Σ s t` и константном τ:
  `C T ≥ C 0·exp(k_eff·W − ln(1+α)·Δ)`,
  `k_eff = p₀·ln(1+α)/τ`, `W = T·τ`;
* `wallclock_rate_from_cone_concentrated`: Δ :=
  `concDelta T δ = √(2T·log(1/δ))` (гипотеза — концентрация
  R95, здесь не перепроверяется);
* `wallclock_rate_avg_tau`: версия с переменным τ_t при
  `Σ τ t ≤ T·τ̄`.
-/

open Real Finset

namespace Hagi.Dynamics

/-! ## Пер-факторное неравенство -/

/-- При `0 ≤ x`: `x − x²/2 ≤ log(1 + x)` (f(t) = log(1+t) − t
+ t²/2 монотонна, f(0) = 0; верно на всей неотрицательной
полупрямой). -/
theorem log_one_add_ge_sub_half_sq {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  -- the derivative fact: f' t = t²/(1+t) for t ≥ 0
  have hderivAt : ∀ t : ℝ, 0 ≤ t → HasDerivAt
      (fun t => Real.log (1 + t) - t + t ^ 2 / 2) (t ^ 2 / (1 + t)) t := by
    intro t ht
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
      have hc : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id' t).const_add 1
      have hl2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹ * 1) t := by
        have := (Real.hasDerivAt_log
          (ne_of_gt (by linarith : (0:ℝ) < 1 + t))).comp t hc
        exact this
      simpa [div_eq_inv_mul] using hl2
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    have hf' : HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
        (1 / (1 + t) - 1 + t) t := (hlog.sub (hasDerivAt_id' t)).add hsq
    have heq : 1 / (1 + t) - 1 + t = t ^ 2 / (1 + t) := by
      field_simp
      ring
    rw [heq] at hf'
    exact hf'
  -- continuity on the closed interval
  have hcont : ContinuousOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (Set.Icc 0 x) := by
    have h1 : ContinuousOn (fun t : ℝ => 1 + t) (Set.Icc 0 x) :=
      (continuous_const.add continuous_id).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc 0 x) :=
      ContinuousOn.comp Real.continuousOn_log h1
        (fun t ht => by
          change (1:ℝ) + t ∉ {(0:ℝ)}
          intro h
          simp only [Set.mem_singleton_iff] at h
          exact absurd h (by have := ht.1; linarith))
    have h3 : ContinuousOn (fun t : ℝ => t ^ 2 / 2) (Set.Icc 0 x) :=
      Continuous.continuousOn
        (Continuous.div (continuous_id.pow 2) continuous_const (by norm_num))
    exact (h2.sub continuous_id.continuousOn).add h3
  -- differentiability + nonneg derivative on the interior
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (interior (Set.Icc 0 x)) := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    exact (hderivAt t ht0).differentiableAt.differentiableWithinAt
  have hnn : ∀ t ∈ interior (Set.Icc 0 x),
      0 ≤ deriv (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) t := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    rw [(hderivAt t ht0).deriv]
    exact div_nonneg (sq_nonneg t) (by linarith : (0:ℝ) ≤ 1 + t)
  have hmono : MonotoneOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont hdiff hnn
  have m0 : (0:ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have mx : x ∈ Set.Icc 0 x := ⟨hx, le_rfl⟩
  have hfx := hmono m0 mx hx
  beta_reduce at hfx
  have hzero : Real.log (1 + 0) - 0 + 0 ^ 2 / 2 = (0:ℝ) := by
    simp [Real.log_one]
  rw [hzero] at hfx
  linarith

/-- При `0 ≤ x`: `exp(x − x²/2) ≤ 1 + x`. -/
theorem exp_le_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x - x ^ 2 / 2) ≤ 1 + x := by
  have h2 : Real.exp (x - x ^ 2 / 2) ≤ Real.exp (Real.log (1 + x)) :=
    Real.exp_le_exp.mpr (log_one_add_ge_sub_half_sq hx)
  exact h2.trans_eq (Real.exp_log (by linarith : (0:ℝ) < 1 + x))

/-! ## Гипотеза пер-цикловой ставки -/

/-- `per_cycle_time_rate C τ k`:
`∀ t, C (t+1) ≥ C t·(1 + k·τ t)` — гипотеза, композируемая
нижеследующими теоремами (не выводится здесь). -/
def per_cycle_time_rate (C τ : ℕ → ℝ) (k : ℝ) : Prop :=
  ∀ t, C (t + 1) ≥ C t * (1 + k * τ t)

/-! ## Закон произведения -/
/-- При `0 ≤ k`, `0 ≤ τ t` и `per_cycle_time_rate C τ k`:
`C T ≥ C 0·∏_{t<T}(1 + k·τ t)` (индукция). -/
theorem wallclock_takeoff_product (C τ : ℕ → ℝ) (k : ℝ)
    (hk : 0 ≤ k) (hτ : ∀ t, 0 ≤ τ t)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hstep T
      rw [Finset.prod_range_succ]
      have hpos : (0:ℝ) ≤ ∏ t ∈ Finset.range T, (1 + k * τ t) :=
        Finset.prod_nonneg fun t _ =>
          add_nonneg zero_le_one (mul_nonneg hk (hτ t))
      calc C (T + 1) ≥ C T * (1 + k * τ T) := h1
        _ ≥ (C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t)) * (1 + k * τ T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            exact add_nonneg zero_le_one (mul_nonneg hk (hτ T))
        _ = C 0 * ((∏ t ∈ Finset.range T, (1 + k * τ t)) * (1 + k * τ T)) := by
            ring

/-! ## Экспонента wall-clock (главная) -/

/-- Монотонность произведения (в mathlib 4.34 `Finset.prod_le_prod`
требует `MulLeftMono`, недоступного для `ℝ`). -/
private lemma prod_exp_le_prod_one_add (τ : ℕ → ℝ) (k : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hτ : ∀ t, 0 ≤ τ t) :
    ∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2)
      ≤ ∏ t ∈ Finset.range n, (1 + k * τ t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have hc := exp_le_one_add (mul_nonneg hk (hτ n))
      have hzc : 0 ≤ 1 + k * τ n := by
        have := exp_le_one_add (mul_nonneg hk (hτ n))
        linarith [Real.exp_nonneg (k * τ n - (k * τ n) ^ 2 / 2)]
      calc (∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2))
            * Real.exp (k * τ n - (k * τ n) ^ 2 / 2)
          ≤ (∏ t ∈ Finset.range n, Real.exp (k * τ t - (k * τ t) ^ 2 / 2))
            * (1 + k * τ n) :=
              mul_le_mul_of_nonneg_left hc
                (Finset.prod_nonneg fun t _ => Real.exp_nonneg _)
        _ ≤ (∏ t ∈ Finset.range n, (1 + k * τ t)) * (1 + k * τ n) :=
              mul_le_mul_of_nonneg_right ih hzc


/-- При `0 ≤ k`, `0 ≤ C 0`, `0 ≤ τ t` и `per_cycle_time_rate`:
`C T ≥ C 0·exp(k·Στ − (k²/2)·Στ²)` — экспонента с явным
второпорядковым слэком (из `exp_le_one_add` пофакторно и
`exp(Σ) = ∏exp`). -/
theorem wallclock_takeoff (C τ : ℕ → ℝ) (k : ℝ)
    (hk : 0 ≤ k) (hC0 : 0 ≤ C 0) (hτ : ∀ t, 0 ≤ τ t)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
      - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) := by
  have hprod := wallclock_takeoff_product C τ k hk hτ hstep T
  -- each factor dominates its slack-ed exponent
  have hf : ∀ t ∈ Finset.range T,
      Real.exp (k * τ t - (k * τ t) ^ 2 / 2) ≤ 1 + k * τ t := fun t _ =>
    exp_le_one_add (mul_nonneg hk (hτ t))
  have hprod' : ∏ t ∈ Finset.range T, Real.exp (k * τ t - (k * τ t) ^ 2 / 2)
      ≤ ∏ t ∈ Finset.range T, (1 + k * τ t) :=
    prod_exp_le_prod_one_add τ k T hk hτ
  rw [← Real.exp_sum] at hprod'
  -- the exponent collapses to k·Στ − (k²/2)·Στ²
  have hsum : ∑ t ∈ Finset.range T, (k * τ t - (k * τ t) ^ 2 / 2)
      = k * ∑ t ∈ Finset.range T, τ t - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ t ∈ Finset.range T, k * τ t = k * ∑ t ∈ Finset.range T, τ t :=
      (Finset.mul_sum _ _ _).symm
    have h2 : ∑ t ∈ Finset.range T, (k * τ t) ^ 2 / 2
        = (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
      have h3 : ∑ t ∈ Finset.range T, (k * τ t) ^ 2
          = k ^ 2 * ∑ t ∈ Finset.range T, (τ t) ^ 2 := by
        rw [show k ^ 2 * ∑ t ∈ Finset.range T, (τ t) ^ 2
            = ∑ t ∈ Finset.range T, k ^ 2 * (τ t) ^ 2 from Finset.mul_sum _ _ _]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [← Finset.sum_div, h3]
      ring
    rw [h1, h2]
  rw [hsum] at hprod'
  calc C T ≥ C 0 * ∏ t ∈ Finset.range T, (1 + k * τ t) := hprod
    _ ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod' hC0

/-! ## Режим малых шагов -/

/-- При посылках `wallclock_takeoff` и `k·τ t ≤ η` для всех t:
`C T ≥ C 0·exp(k·(Στ)·(1 − η/2))`. -/
theorem wallclock_takeoff_small_steps (C τ : ℕ → ℝ) (k η : ℝ)
    (hk : 0 ≤ k) (hC0 : 0 ≤ C 0) (hτ : ∀ t, 0 ≤ τ t)
    (hη : ∀ t, k * τ t ≤ η)
    (hstep : per_cycle_time_rate C τ k)
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2)) := by
  have hmain := wallclock_takeoff C τ k hk hC0 hτ hstep T
  -- the slack bound: (k²/2)Στ² ≤ (η/2)·k·Στ
  have hslack : (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2
      ≤ (η / 2) * (k * ∑ t ∈ Finset.range T, τ t) := by
    have hper : ∀ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2
        ≤ (η / 2) * (k * τ t) := by
      intro t _
      have hkτ : (0:ℝ) ≤ k * τ t := mul_nonneg hk (hτ t)
      have h1 : k ^ 2 * (τ t) ^ 2 = (k * τ t) * (k * τ t) := by ring
      have h2 : (k * τ t) * (k * τ t) ≤ η * (k * τ t) :=
        mul_le_mul_of_nonneg_right (hη t) hkτ
      nlinarith
    have hsum : (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2
        = ∑ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2 := Finset.mul_sum _ _ _
    rw [hsum]
    calc ∑ t ∈ Finset.range T, (k ^ 2 / 2) * (τ t) ^ 2
        ≤ ∑ t ∈ Finset.range T, (η / 2) * (k * τ t) := Finset.sum_le_sum hper
      _ = (η / 2) * ∑ t ∈ Finset.range T, (k * τ t) := (Finset.mul_sum _ _ _).symm
      _ = (η / 2) * (k * ∑ t ∈ Finset.range T, τ t) := by rw [← Finset.mul_sum]
  -- exponent comparison
  have hexp : Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2))
      ≤ Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [hslack])
  calc C T ≥ C 0 * Real.exp (k * ∑ t ∈ Finset.range T, τ t
        - (k ^ 2 / 2) * ∑ t ∈ Finset.range T, (τ t) ^ 2) := hmain
    _ ≥ C 0 * Real.exp (k * (∑ t ∈ Finset.range T, τ t) * (1 - η / 2)) :=
        mul_le_mul_of_nonneg_left hexp hC0

/-! ## Композиция с конус/успех-механизмом -/

/-- При `C (t+1) ≥ C t·exp(a·s t)` для всех t:
`C T ≥ C 0·exp(a·Σ s t)` (экспоненциальный двойник
`capability_takeoff_counted`; s t = 0 нейтрально). -/
theorem counted_takeoff_exp (C s : ℕ → ℝ) (a : ℝ)
    (hmul : ∀ t, C (t + 1) ≥ C t * Real.exp (a * s t))
    (T : ℕ) :
    C T ≥ C 0 * Real.exp (a * ∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      rw [Finset.sum_range_succ, mul_add, Real.exp_add]
      calc C (T + 1) ≥ C T * Real.exp (a * s T) := h1
        _ ≥ (C 0 * Real.exp (a * ∑ t ∈ Finset.range T, s t)) * Real.exp (a * s T) := by
            refine mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
        _ = C 0 * (Real.exp (a * ∑ t ∈ Finset.range T, s t) * Real.exp (a * s T)) := by
            ring

/-- При `0 < α`, `0 < τ`, `0 < C 0`, пер-цикловом множителе
`(1+α)^(s t)` и `p₀·T − Δ ≤ Σ (s t:ℝ)`:
`C T ≥ C 0·exp((p₀·log(1+α)/τ)·(T·τ) − log(1+α)·Δ)`. -/
theorem wallclock_rate_from_cone (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha tau p0 Delta : ℝ)
    (halpha : 0 < alpha) (htau : 0 < tau) (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (hcount : p0 * (T : ℝ) - Delta ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tau) * ((T : ℝ) * tau)
      - Real.log (1 + alpha) * Delta) := by
  set L := Real.log (1 + alpha) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  -- rewrite the per-cycle factor in exp form
  have hpowexp : ∀ t, (1 + alpha) ^ (s t) = Real.exp ((s t : ℝ) * L) := by
    intro t
    have h1 : Real.exp ((s t : ℝ) * L) = Real.exp (L) ^ (s t) := by
      rw [← Real.exp_nat_mul L (s t)]
    rw [h1, Real.exp_log (by linarith : (0:ℝ) < 1 + alpha)]
  have hmul' : ∀ t, C (t + 1) ≥ C t * Real.exp (L * (s t : ℝ)) := by
    intro t
    have h := hmul t
    rw [hpowexp t, mul_comm ((s t : ℝ)) L] at h
    exact h
  have hmain := counted_takeoff_exp C (fun t => (s t : ℝ)) L hmul' T
  -- the exponent with the concentration floor substituted
  have hcount' : L * (p0 * (T : ℝ) - Delta)
      ≤ L * ∑ t ∈ Finset.range T, (s t : ℝ) :=
    mul_le_mul_of_nonneg_left hcount hLpos.le
  have hexp : Real.exp ((p0 * L / tau) * ((T : ℝ) * tau) - L * Delta)
      ≤ Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have heq : L * (p0 * (T : ℝ) - Delta)
        = (p0 * L / tau) * ((T : ℝ) * tau) - L * Delta := by
      field_simp
    linarith [hcount', heq]
  calc C T ≥ C 0 * Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := hmain
    _ ≥ C 0 * Real.exp ((p0 * L / tau) * ((T : ℝ) * tau) - L * Delta) :=
        mul_le_mul_of_nonneg_left hexp hC0.le

/-- При посылках `wallclock_rate_from_cone` с Δ :=
`concDelta T δ` (концентрированный полу успеха — гипотеза;
вероятностная гарантия — `success_count_lower_p0`, не здесь):
`C T ≥ C 0·exp((p₀·log(1+α)/τ)·(T·τ) − log(1+α)·concDelta T δ)`. -/
theorem wallclock_rate_from_cone_concentrated (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha tau p0 delta : ℝ)
    (halpha : 0 < alpha) (htau : 0 < tau)
    (_hdelta : 0 < delta) (_hdelta1 : delta < 1)
    (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (hcount : p0 * (T : ℝ) - concDelta T delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tau) * ((T : ℝ) * tau)
      - Real.log (1 + alpha) * concDelta T delta) :=
  wallclock_rate_from_cone C s alpha tau p0 (concDelta T delta)
    halpha htau hC0 hmul T hcount


/-- При `0 < α`, `0 < τ̄`, `0 ≤ p₀`, `0 < C 0`, пер-цикловом
множителе `(1+α)^(s t)`, `T ≠ 0`, `Σ τ t ≤ T·τ̄` и
`p₀·T − Δ ≤ Σ (s t:ℝ)`:
`C T ≥ C 0·exp((p₀·log(1+α)/τ̄)·(Σ τ t) − log(1+α)·Δ)`
(версия с переменным временем цикла). -/
theorem wallclock_rate_avg_tau (C : ℕ → ℝ) (s : ℕ → ℕ) (tau : ℕ → ℝ)
    (alpha tauBar p0 Delta : ℝ)
    (halpha : 0 < alpha) (htauBar : 0 < tauBar) (hp0 : 0 ≤ p0)
    (hC0 : 0 < C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (htau : T ≠ 0)
    (havg : ∑ t ∈ Finset.range T, tau t ≤ (T : ℝ) * tauBar)
    (hcount : p0 * (T : ℝ) - Delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp ((p0 * Real.log (1 + alpha) / tauBar)
      * (∑ t ∈ Finset.range T, tau t) - Real.log (1 + alpha) * Delta) := by
  set L := Real.log (1 + alpha) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set W : ℝ := ∑ t ∈ Finset.range T, tau t with hW
  have hTw : W / tauBar ≤ (T : ℝ) := by
    rw [div_le_iff₀ htauBar]
    linarith
  have hsumfloor : p0 * (W / tauBar) - Delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ) := by
    have hpw : p0 * (W / tauBar) ≤ p0 * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hTw hp0
    linarith
  have hpowexp : ∀ t, (1 + alpha) ^ (s t) = Real.exp ((s t : ℝ) * L) := by
    intro t
    have h1 : Real.exp ((s t : ℝ) * L) = Real.exp (L) ^ (s t) := by
      rw [← Real.exp_nat_mul L (s t)]
    rw [h1, Real.exp_log (by linarith : (0:ℝ) < 1 + alpha)]
  have hmul' : ∀ t, C (t + 1) ≥ C t * Real.exp (L * (s t : ℝ)) := by
    intro t
    have h := hmul t
    rw [hpowexp t, mul_comm ((s t : ℝ)) L] at h
    exact h
  have hmain := counted_takeoff_exp C (fun t => (s t : ℝ)) L hmul' T
  have hexpfloor : Real.exp (L * (p0 * (W / tauBar) - Delta))
      ≤ Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsumfloor hLpos.le)
  have hexponent : (p0 * L / tauBar) * W - L * Delta
      = L * (p0 * (W / tauBar) - Delta) := by
    field_simp
    try ring
  rw [hexponent]
  calc C T ≥ C 0 * Real.exp (L * ∑ t ∈ Finset.range T, (s t : ℝ)) := hmain
    _ ≥ C 0 * Real.exp (L * (p0 * (W / tauBar) - Delta)) :=
        mul_le_mul_of_nonneg_left hexpfloor hC0.le

end Hagi.Dynamics

namespace Hagi
export Hagi.Dynamics (wallclock_rate_from_cone)
end Hagi


end C238_wallclock
section C238_frontprod
/-!
# FrontierProduction — сертифицированное производство frontier и семантика capability

* `injection_law_of_measured` (III-a): если `D (t+1) ≥ κ·dis t`
  и потребность обновления `ρ·D t + β·C t − ξ t ≤ κ·dis t`, то
  выполнен `InjectionLaw D C xi rho beta`.
* `certified_cycle_renewal` (III-b): если измеренная сумма n
  проб разногласия в [0,1] превышает `n·thr + 2n·ε` и
  `D (t+1) ≥ κ·disMean`, то renewal-закон одного цикла выполнен
  на этом событии с вероятностью `≥ 1 − 2e^{−2nε²}`.
  Посылка `hD` (разногласие ⇒ frontier) — архитектурная, не
  выводится здесь; многoцикловая версия не формализована.
* `CapabilitySound` (IV): `C t ≤ U t` для всех t; связка C с
  реальной моделью — посылка.
* `takeoff_lifts_utility`: если `CapabilitySound C U` и
  `C 0 * (1 + alpha) ^ T ≤ C T`, то `C 0 * (1 + alpha) ^ T ≤ U T`.
-/

open Finset Real

namespace Hagi.Growth

/-! ## III-a: детерминированная редукция β-посылки -/

/-- Абстрактный закон производства frontier:
`∀ t, D (t+1) ≥ ρ·D t + β·C t − ξ t`. -/
def InjectionLaw (D C xi : ℕ → ℝ) (rho beta : ℝ) : Prop :=
  ∀ t, D (t + 1) ≥ rho * D t + beta * C t - xi t

/-- Если `D (t+1) ≥ κ·dis t` для всех t и
`ρ·D t + β·C t − ξ t ≤ κ·dis t` для всех t, то
`InjectionLaw D C xi rho beta`. -/
theorem injection_law_of_measured (D C dis xi : ℕ → ℝ) (kappa rho beta : ℝ)
    (hD : ∀ t, D (t + 1) ≥ kappa * dis t)
    (h : ∀ t, rho * D t + beta * C t - xi t ≤ kappa * dis t) :
    InjectionLaw D C xi rho beta :=
  fun t => le_trans (h t) (hD t)

/-! ## III-b: статистическая сертификация одного цикла -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Среднее по n пробам координатных средних (значения в [0,1]). -/
noncomputable def disMean {n : ℕ} (p : Fin n → V → ℝ) (Y : Fin n → V → ℝ) : ℝ :=
  (∑ i, Hagi.coordMean p Y i) / (n : ℝ)

@[simp]
theorem coordMean_const {n : ℕ} (p : Fin n → V → ℝ) (hp : Hagi.IsProbSys p)
    (c : ℝ) (i : Fin n) : Hagi.coordMean p (fun _ _ => c) i = c := by
  unfold Hagi.coordMean
  rw [← Finset.sum_mul, (hp i).2, one_mul]

theorem const_probe_sum {n : ℕ} (c : ℝ) (ω : Fin n → V) :
    ∑ i, (fun _ _ => c) i (ω i) = (n : ℝ) * c := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Сертифицированное обновление одного цикла: при пробах
разногласия `Y` в [0,1], пороге `thr ∈ [0,1]`, `κ ≥ 0` и
посылках `D (t+1) ≥ κ·disMean p Y` и
`ρ·D t + β·C t − ξ t ≤ κ·thr`: с вероятностью
`≥ 1 − 2e^{−2nε²}` из измеренного события
`n·thr + 2n·ε ≤ Σ Y i (ω i)` следует
`D (t+1) ≥ ρ·D t + β·C t − ξ t`. -/
theorem certified_cycle_renewal {n : ℕ} (p : Fin n → V → ℝ)
    (hp : Hagi.IsProbSys p)
    (Y : Fin n → V → ℝ) (hY : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (D C : ℕ → ℝ) (kappa rho beta : ℝ) (xi : ℕ → ℝ) (t : ℕ) (thr : ℝ)
    (hthr01 : 0 ≤ thr ∧ thr ≤ 1) (hkappa : 0 ≤ kappa)
    (hD : D (t + 1) ≥ kappa * disMean p Y)
    (hthr : rho * D t + beta * C t - xi t ≤ kappa * thr) :
    1 - 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω =>
        (n : ℝ) * thr + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → D (t + 1) ≥ rho * D t + beta * C t - xi t) := by
  classical
  set X : Fin n → V → ℝ := fun _ _ => thr with hXdef
  have hXb : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1 :=
    fun _ _ => ⟨hthr01.1, hthr01.2⟩
  have hc := certified_premise p hp X Y hXb hY hn eps heps
  -- измеренная сумма константных проб = n·thr; их среднее тоже
  have hsumX : ∀ ω : Fin n → V, ∑ i, X i (ω i) = (n : ℝ) * thr :=
    fun ω => const_probe_sum thr ω
  have hmuX : (∑ i, Hagi.coordMean p X i) = (n : ℝ) * thr := by
    rw [hXdef]
    simp [coordMean_const p hp thr]
  -- μ-формула disMean
  have hdis : disMean p Y = (∑ i, Hagi.coordMean p Y i) / (n : ℝ) := rfl
  -- на хорошем событии hc: требование выполнено
  have hmono : prodPq p (fun ω =>
        ∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → ∑ i, Hagi.coordMean p X i ≤ ∑ i, Hagi.coordMean p Y i)
      ≤ prodPq p (fun ω =>
        (n : ℝ) * thr + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → D (t + 1) ≥ rho * D t + beta * C t - xi t) :=
    prodPq_mono p hp _ _ (by
      intro ω hfull hmeas
      -- hmeas : n·thr + 2nε ≤ ΣY; hfull ждёт ΣX + 2nε ≤ ΣY
      have hXle : ∑ i, X i (ω i) + 2 * (n : ℝ) * eps
          ≤ ∑ i, Y i (ω i) := by
        rw [hsumX ω]
        exact hmeas
      have hconcl := hfull hXle
      rw [hmuX] at hconcl
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hthr_le : thr ≤ disMean p Y := by
        rw [hdis, le_div_iff₀ hnpos, mul_comm thr]
        exact hconcl
      have hchain : kappa * thr ≤ kappa * disMean p Y :=
        mul_le_mul_of_nonneg_left hthr_le (by positivity)
      have hreq : kappa * thr ≥ rho * D t + beta * C t - xi t := hthr
      have hD2 : D (t + 1) ≥ kappa * disMean p Y := hD
      have hfin : D (t + 1) ≥ rho * D t + beta * C t - xi t := by
        nlinarith [hchain, hreq, hD2]
      exact hfin)
  exact le_trans hc hmono

/-! ## IV: CapabilitySemantics -/

/-- `CapabilitySound C U` означает `C t ≤ U t` для всех t
(`U` — полезность над семейством задач; связка с реальной
моделью остаётся посылкой). -/
def CapabilitySound (C U : ℕ → ℝ) : Prop := ∀ t, C t ≤ U t

/-- Если `CapabilitySound C U` и `C 0 * (1 + alpha) ^ T ≤ C T`,
то `C 0 * (1 + alpha) ^ T ≤ U T`. -/
theorem takeoff_lifts_utility (C U : ℕ → ℝ) (alpha : ℝ) (T : ℕ)
    (hsnd : CapabilitySound C U)
    (hgr : C 0 * (1 + alpha) ^ T ≤ C T) :
    C 0 * (1 + alpha) ^ T ≤ U T :=
  le_trans hgr (hsnd T)

end Hagi.Growth


end C238_frontprod
section C238_gate
/-!
# GrowthGate — вердикты двумерного контроллера (G_F, R_repr)

Вердикт-таблица роста как четыре непересекающиеся импликации
по ячейкам сетки решений `(G_F, R)` с порогом `eps > 0`:

* `verdict_ttt`: `eps ≤ G_F` и `R ≤ eps` дают `0 ≤ G_F − R` и
  `eps ≤ G_F`;
* `verdict_grow`: `eps < R` даёт `0 < R − eps`;
* `verdict_exhausted`: `G_F < eps` и `eps < R` дают
  `G_F < eps ∧ eps < R`.
-/

open Finset

namespace Hagi.Growth

section GrowthGate

variable {V : Type*} [Fintype V]

-- вердикт-таблица: четыре непересекающиеся импликации,
-- по одной на ячейку сетки решений (G_F, R)

/-- Ячейка 1: если `eps ≤ GF` и `R ≤ eps`, то `0 ≤ GF − R` и
`eps ≤ GF`. -/
theorem verdict_ttt (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : eps ≤ GF) (h2 : R ≤ eps) : (0 ≤ GF - R) ∧ (eps ≤ GF) := by
  constructor <;> linarith

/-- Ячейка 2: если `eps < R`, то `0 < R − eps`. -/
theorem verdict_grow (GF R eps : ℝ) (_heps : 0 < eps)
    (_h1 : eps ≤ GF) (h2 : eps < R) : 0 < R - eps := by linarith

/-- Ячейка 4: если `GF < eps` и `eps < R`, то `GF < eps ∧ eps < R`. -/
theorem verdict_exhausted (GF R eps : ℝ) (_heps : 0 < eps)
    (h1 : GF < eps) (h2 : eps < R) : GF < eps ∧ eps < R := ⟨h1, h2⟩

end GrowthGate

end Hagi.Growth


end C238_gate
section C238_chain
/-!
# ChainToCone — from the disagreement chain to the growth cone

* `chain_feeds_cone`: if each conversion factor of `s` is at least
  `β` and `κ * D ≤ s.E_raw` (all with `0 ≤ β`, `0 ≤ κ`, `0 ≤ D`),
  then `(β^4 * κ) * D ≤ s.G_cap`.
* `cone_two_sided_certificate`: if for all steps `gamma * D t ≤ G t ≤
  gbar * D t`, the step law `C (t+1) = C t + G t` holds, and the cone
  dynamics `rho * D t + beta * C t ≤ D (t+1)` hold with `gbar * k ≤ rho`
  and `gbar * k^2 + (1 - rho) * k ≤ beta`, then the cone invariant
  `k * C t ≤ D t` is preserved up to `T`.
  A one-sided lower certificate alone is not sufficient for this
  proof (the upper bound `G t ≤ gbar * D t` is a hypothesis).
* `takeoff_from_certificate`: combining per-step lower certificates
  via `chain_feeds_cone` with `cone_two_sided_certificate` yields
  `C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- If each conversion factor of `s` is at least `β`, `0 ≤ κ`,
`0 ≤ D`, and `κ * D ≤ s.E_raw`, then `(β^4 * κ) * D ≤ s.G_cap`. -/
theorem chain_feeds_cone (s : DisagreementStages)
    {β κ D : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hD : 0 ≤ D)
    (hcert : β ≤ s.α_align ∧ β ≤ s.α_trunc
      ∧ β ≤ s.α_safe ∧ β ≤ s.α_cap)
    (hdiv : κ * D ≤ s.E_raw) :
    (β^4 * κ) * D ≤ s.G_cap := by
  obtain ⟨h1, h2, h3, h4⟩ := hcert
  have ha1 : 0 ≤ s.α_align := le_trans hβ h1
  have ha2 : 0 ≤ s.α_trunc := le_trans hβ h2
  have ha3 : 0 ≤ s.α_safe := le_trans hβ h3
  have ha4 : 0 ≤ s.α_cap := le_trans hβ h4
  have hchain : s.G_cap
      = s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw :=
    disagreement_chain s
  have hb : 0 ≤ β * β := mul_nonneg hβ hβ
  have m1 : β * β ≤ s.α_align * s.α_trunc :=
    mul_le_mul h1 h2 hβ ha1
  have m2 : β * β ≤ s.α_safe * s.α_cap :=
    mul_le_mul h3 h4 hβ ha3
  have m3 : (β * β) * (β * β)
      ≤ (s.α_align * s.α_trunc) * (s.α_safe * s.α_cap) :=
    mul_le_mul m1 m2 hb (by positivity)
  have hprod : β^4 ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap := by
    nlinarith [m3]
  have hA : 0 ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap :=
    mul_nonneg (mul_nonneg (mul_nonneg ha1 ha2) ha3) ha4
  have hfinal : β^4 * (κ * D)
      ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw :=
    mul_le_mul hprod hdiv (mul_nonneg hκ hD) hA
  have hrew : β^4 * κ * D = β^4 * (κ * D) := by ring
  rw [hchain]
  nlinarith [hfinal, hrew]

/-- Cone invariant preservation under a two-sided certified
step: assuming `gamma * D t ≤ G t ≤ gbar * D t` for each step,
the exact step law `C (t + 1) = C t + G t`, nonnegativity of
`C` and `D`, the cone dynamics `rho * D t + beta * C t ≤ D (t+1)`,
and the parameter conditions `gbar * k ≤ rho`,
`gbar * k ^ 2 + (1 - rho) * k ≤ beta`, the invariant
`k * C t ≤ D t` (assumed at `t = 0`) is preserved for all
`t ≤ T`. -/
theorem cone_two_sided_certificate (C D G : ℕ → ℝ)
    (gamma gbar rho beta k : ℝ) (T : ℕ)
    (hk : 0 ≤ k)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hlow : ∀ t ∈ Finset.range T, gamma * D t ≤ G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ gbar * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + beta * C t ≤ D (t + 1))
    (hrhogk : gbar * k ≤ rho)
    (hbeta : gbar * k ^ 2 + (1 - rho) * k ≤ beta)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := by
  have hmain : ∀ t : ℕ, t ≤ T → k * C t ≤ D t := by
    intro t
    induction t with
    | zero => intro _; exact hcone0
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T := by
          rw [Finset.mem_range]; omega
        have htlte : t ∈ Finset.range (T + 1) := by
          rw [Finset.mem_range]; omega
        have hc := ih (by omega)
        have hDt : 0 ≤ D t := hD t htlte
        have hCt : 0 ≤ C t := hC t htlte
        have hGup := hup t htlt
        have hd := hdyn t htlt
        have hkey : rho * D t + beta * C t
            - k * (C t + gbar * D t)
            = (rho - gbar * k) * (D t - k * C t)
              + (beta - (gbar * k ^ 2 + (1 - rho) * k)) * C t := by
          field_simp
          ring
        have hnn1 : (0:ℝ) ≤ (rho - gbar * k) * (D t - k * C t) :=
          mul_nonneg (sub_nonneg.mpr hrhogk) (sub_nonneg.mpr hc)
        have hnn2 : (0:ℝ)
            ≤ (beta - (gbar * k ^ 2 + (1 - rho) * k)) * C t :=
          mul_nonneg (sub_nonneg.mpr hbeta) hCt
        -- k·G t ≤ k·γ̄·D t
        have hkle : k * G t ≤ k * (gbar * D t) :=
          mul_le_mul_of_nonneg_left hGup hk
        have hgoal : rho * D t + beta * C t - k * (C t + G t) ≥ 0 := by
          have := hnn1
          have := hnn2
          have hkey' : rho * D t + beta * C t
              - k * (C t + gbar * D t) ≥ 0 := by
            rw [hkey]; positivity
          linarith
        rw [hstep t htlt]
        linarith
  intro t ht
  exact hmain t (by rw [Finset.mem_range] at ht; omega)

/-- Takeoff from per-step certificates: if at every step the
conversion factors of `stages t` are at least `beta`,
`kappa * D t ≤ (stages t).E_raw`, `(stages t).G_cap = G t`,
the increments satisfy `G t ≤ gbar * D t`, and the hypotheses
of `cone_two_sided_certificate` hold, then
`C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`. -/
theorem takeoff_from_certificate
    (C D G : ℕ → ℝ) (stages : ℕ → DisagreementStages)
    (T : ℕ) (beta kappa gbar rho cbeta k : ℝ)
    (hβ : 0 ≤ beta) (hκ : 0 ≤ kappa) (hk : 0 ≤ k)
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
    (hup : ∀ t ∈ Finset.range T, G t ≤ gbar * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + cbeta * C t ≤ D (t + 1))
    (hrhogk : gbar * k ≤ rho)
    (hbeta' : gbar * k ^ 2 + (1 - rho) * k ≤ cbeta)
    (hcone0 : k * C 0 ≤ D 0) :
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T := by
  -- lower certificate: gamma·D t ≤ G t via chain_feeds_cone
  have hlow : ∀ t ∈ Finset.range T,
      (beta^4 * kappa) * D t ≤ G t := by
    intro t ht
    have hg := chain_feeds_cone (stages t) hβ hκ
      (hD t (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp ht))))
      (hcert t ht) (hdiv t ht)
    rw [hG t ht] at hg
    exact hg
  -- the cone holds under the two-sided certificate
  have hcone := cone_two_sided_certificate C D G
    (beta^4 * kappa) gbar rho cbeta k T hk hD hC
    hstep hlow hup hdyn hrhogk hbeta' hcone0
  -- takeoff via the elasticity spine (dedup it. 26): the
  -- manual induction collapses to
  -- TakeoffElasticity.elasticity_chain_horizon with the
  -- constant chain elasticity e t = (beta^4 * kappa) * k
  -- (the cone gives the per-step elasticity lower bound
  -- inside the horizon only — hence the horizon form).
  have hgammak : 0 ≤ (beta^4 * kappa) * k :=
    mul_nonneg (mul_nonneg (by positivity) hκ) hk
  have hstep' : ∀ t < T, (1 + (beta^4 * kappa) * k) * C t
      ≤ C (t + 1) := by
    intro t ht
    have htmem : t ∈ Finset.range T := Finset.mem_range.mpr ht
    have hlo := hlow t htmem
    have hs := hstep t htmem
    have hcone' := hcone t (Finset.mem_range.mpr
      (Nat.lt_succ_of_lt (Finset.mem_range.mp htmem)))
    rw [hs]
    have hmono : (beta^4 * kappa) * (k * C t)
        ≤ (beta^4 * kappa) * D t :=
      mul_le_mul_of_nonneg_left hcone'
        (mul_nonneg (by positivity) hκ)
    have hrew : C t + (beta^4 * kappa) * (k * C t)
        = (1 + (beta^4 * kappa) * k) * C t := by ring
    linarith [hmono, hrew]
  have hchain := elasticity_chain_horizon C
    (fun _ => (beta^4 * kappa) * k) T hstep'
    (fun t _ => by linarith)
  rwa [Finset.prod_const, Finset.card_range] at hchain

end Hagi.Growth

end C238_chain
section C238_t3
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

end C238_t3
section C238_unified
/-!
# FastGrowth ↔ GrowthState — the takeoff laws on the growth state

The bridge from the additive `grow` update to multiplicative
takeoff: `additive_as_multiplicative` reads the additive
capability increment as the factor `1 + growGain / capability`;
`growMul`/`growCycle` iterate the transition; `growCycle_capability`
gives the exact closed form `C₀ + t·G` (G invariant).

* `growth_state_takeoff`: with success indicators `sigma t ≤ 1`
  and per-cycle gate `alpha * C_t ≤ G` on successes,
  `(growCycle T S).capability ≥ S.capability * (1+alpha) ^ Σσ`.
* `growth_state_takeoff_window`: with a fixed gain, the success
  count and the certified factor are bounded by constants
  (`Σσ ≤ 1/alpha + 1 − C₀/G`, factor ≤ exp(1 + alpha −
  alpha·C₀/G)); sustained takeoff needs a capability-dependent
  gain and is not claimed here.
* `growth_state_takeoff_probabilistic`: with h_emp_ independent
  [0,1]-success indicators (mean ≥ p0) and a pointwise log-bridge,
  Pr[(growCycle T S ω).capability ≥ S ω.capability *
  exp(a·(p0·T − Δ(T,δ)) − Σε)] ≥ 1 − δ.
-/

open Real Finset MeasureTheory ProbabilityTheory

namespace Hagi.Unified

noncomputable section GrowthBridge

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- For `0 < S.capability`:
`(grow S).capability = S.capability * (1 + S.effects.growGain / S.capability)`. -/
theorem additive_as_multiplicative (S : GrowthState X)
    (hC : 0 < S.capability) :
    (grow S).capability
      = S.capability * (1 + S.effects.growGain / S.capability) := by
  change S.capability + S.effects.growGain = _
  field_simp

/-- The grow transition, to be read through
`growMul_step_multiplicative`: on a certified-success cycle the
capability multiplier is `1 + alpha`; otherwise capability is
non-decreasing. -/
def growMul (S : GrowthState X) : GrowthState X := grow S

theorem growMul_eq_grow (S : GrowthState X) : growMul S = grow S := rfl

/-- The T-fold iteration of the success-gated grow transition. -/
def growCycle : ℕ → GrowthState X → GrowthState X
  | 0, S => S
  | t + 1, S => growMul (growCycle t S)

theorem growCycle_succ (t : ℕ) (S : GrowthState X) :
    growCycle (t + 1) S = growMul (growCycle t S) := rfl

theorem growCycle_zero (S : GrowthState X) : growCycle 0 S = S := rfl

/-- If `0 < S.capability` and `alpha * S.capability ≤ S.effects.growGain`,
then `S.capability * (1 + alpha) ≤ (growMul S).capability`. -/
theorem growMul_step_multiplicative (S : GrowthState X) (alpha : ℝ)
    (hCpos : 0 < S.capability)
    (hsuccess : alpha * S.capability ≤ S.effects.growGain) :
    S.capability * (1 + alpha) ≤ (growMul S).capability := by
  have hbr := additive_as_multiplicative S hCpos
  have hd : alpha ≤ S.effects.growGain / S.capability := (le_div_iff₀ hCpos).mpr hsuccess
  have hm : S.capability * alpha
      ≤ S.capability * (S.effects.growGain / S.capability) :=
    mul_le_mul_of_nonneg_left hd hCpos.le
  rw [growMul_eq_grow, hbr]
  nlinarith

/-- The measured grow-gain field is INVARIANT under the grow
transition, hence constant along the growCycle trajectory. -/
theorem growCycle_growGain (t : ℕ) (S : GrowthState X) :
    (growCycle t S).effects.growGain = S.effects.growGain := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [growCycle_succ, growMul, grow, ih]

theorem growCycle_capability_succ (t : ℕ) (S : GrowthState X) :
    (growCycle (t + 1) S).capability
      = (growCycle t S).capability + S.effects.growGain := by
  rw [growCycle_succ, growMul, grow, growCycle_growGain]

/-- `(growCycle t S).capability = S.capability + t * S.effects.growGain`
(the gain field is invariant under `grow`). -/
theorem growCycle_capability (t : ℕ) (S : GrowthState X) :
    (growCycle t S).capability = S.capability + (t : ℝ) * S.effects.growGain := by
  induction t with
  | zero => rw [growCycle_zero]; ring
  | succ t ih => rw [growCycle_capability_succ, ih]; push_cast; ring

/-- With `0 < alpha`, `sigma t ≤ 1`, positive capability along the
trajectory, and the success gate `alpha * C_t ≤ S.effects.growGain` on
every successful cycle:
`(growCycle T S).capability ≥ S.capability * (1 + alpha) ^ Σσ`.
See `growth_state_takeoff_window`: with a fixed gain the
certified takeoff is bounded. -/
theorem growth_state_takeoff (S : GrowthState X) (sigma : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hgnonneg : 0 ≤ S.effects.growGain)
    (hCpos : ∀ t, 0 < (growCycle t S).capability)
    (hsuccess : ∀ t, sigma t = 1 →
      alpha * (growCycle t S).capability ≤ S.effects.growGain)
    (hsig : ∀ t, sigma t ≤ 1)
    (T : ℕ) :
    (growCycle T S).capability
      ≥ S.capability * (1 + alpha) ^ (∑ t ∈ Finset.range T, sigma t) := by
    -- per-cycle: C(t+1) ≥ C t · (1+α)^(σ t), case-split on σ t ∈ {0,1}
    have hmul : ∀ t, (growCycle (t + 1) S).capability
        ≥ (growCycle t S).capability * (1 + alpha) ^ (sigma t) := by
      intro t
      have hb := hsig t
      rcases Nat.lt_or_ge (sigma t) 1 with h0 | h0
      · -- failure: σ t = 0, multiplier 1
        have hs0 : sigma t = 0 := by omega
        rw [hs0, pow_zero, mul_one, growCycle_capability_succ]
        linarith
      · -- success: σ t = 1, the multiplicative law
        have hs1 : sigma t = 1 := by omega
        have hm := growMul_step_multiplicative (growCycle t S) alpha
          (hCpos t)
          (by rw [growCycle_growGain]; exact hsuccess t hs1)
        have hstep : (growCycle (t + 1) S).capability
            = (growMul (growCycle t S)).capability := rfl
        calc (growCycle (t + 1) S).capability
            = (growMul (growCycle t S)).capability := hstep
          _ ≥ (growCycle t S).capability * (1 + alpha) := hm
          _ = (growCycle t S).capability * (1 + alpha) ^ (sigma t) := by
              rw [hs1, pow_one]
    exact Hagi.Foundations.capability_takeoff_counted
      (fun t => (growCycle t S).capability) sigma alpha halpha hmul T

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- With `0 < alpha`, `0 < S.effects.growGain`, the t = 0 gate
`alpha * C₀ ≤ G`, and the gate `alpha * C_t ≤ G` on every
successful cycle (evaluated along the exact trajectory
`C_t = C₀ + t·G`): the success count obeys
`Σσ ≤ 1/alpha + 1 − C₀/G` and the certified factor obeys
`(1+alpha) ^ Σσ ≤ exp(1 + alpha − alpha·C₀/G)`. With a fixed
gain the certified takeoff is a bounded transient; sustained
takeoff would need a capability-dependent gain and is not
claimed. -/
theorem growth_state_takeoff_window (S : GrowthState X) (sigma : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hG : 0 < S.effects.growGain)
    (hgate0 : alpha * S.capability ≤ S.effects.growGain)
    (hgate : ∀ t, sigma t = 1 →
      alpha * (growCycle t S).capability ≤ S.effects.growGain)
    (hsig : ∀ t, sigma t ≤ 1)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, sigma t : ℝ)
      ≤ 1 / alpha + 1 - S.capability / S.effects.growGain
    ∧ (1 + alpha) ^ (∑ t ∈ Finset.range T, sigma t)
      ≤ Real.exp (1 + alpha - alpha * S.capability / S.effects.growGain) := by
  -- the exact additive trajectory: C_t = C₀ + t·G
  have hadd : ∀ t : ℕ, (growCycle t S).capability
      = S.capability + (t : ℝ) * S.effects.growGain := fun t =>
    growCycle_capability t S
  -- every success time obeys the gate in its additive form:
  -- α·(C₀ + t·G) ≤ G  ⟺  t ≤ 1/α − C₀/G
  have hpos : 0 < alpha * S.effects.growGain := mul_pos halpha hG
  have htime : ∀ t : ℕ, sigma t = 1 →
      (t : ℝ) ≤ 1 / alpha - S.capability / S.effects.growGain := by
    intro t hs
    have hg := hgate t hs
    rw [hadd] at hg
    have hkey : (t : ℝ) * (alpha * S.effects.growGain)
        ≤ S.effects.growGain - alpha * S.capability := by
      have e : (t : ℝ) * (alpha * S.effects.growGain)
          = alpha * ((t : ℝ) * S.effects.growGain) := by ring
      rw [e]
      linarith
    rw [show 1 / alpha - S.capability / S.effects.growGain
        = (S.effects.growGain - alpha * S.capability) / (alpha * S.effects.growGain) from by
      field_simp]
    exact (le_div_iff₀ hpos).mpr hkey
  -- the success count is the number of admissible times, and
  -- every admissible time is below ⌊window⌋ in ℕ
  set tmax : ℝ := 1 / alpha - S.capability / S.effects.growGain with htmax
  have htmax_nonneg : 0 ≤ tmax := by
    have h1 : S.capability * alpha ≤ S.effects.growGain := by
      rw [mul_comm]
      exact hgate0
    have h2 : S.capability / S.effects.growGain ≤ 1 / alpha := by
      rw [div_le_iff₀ hG, div_mul_eq_mul_div, one_mul, le_div_iff₀ halpha]
      exact h1
    rw [htmax]
    linarith
  have hcount : (∑ t ∈ Finset.range T, sigma t : ℝ) ≤ tmax + 1 := by
    have hle : ∀ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ (if (t : ℝ) ≤ tmax then 1 else 0) := by
      intro t ht
      rcases Nat.lt_or_ge (sigma t) 1 with h0 | h0
      · have hs0 : sigma t = 0 := by omega
        rw [hs0, Nat.cast_zero]
        split_ifs <;> norm_num
      · have hb := hsig t
        have hs1 : sigma t = 1 := by omega
        have h4 := htime t hs1
        have h5 : (t : ℝ) ≤ tmax := by rw [htmax]; exact h4
        simp [hs1, h5]
    have hsum : ∑ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ ∑ t ∈ Finset.range T, (if (t : ℝ) ≤ tmax then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun t ht => hle t ht
    have hfil : ∑ t ∈ Finset.range T, (if (t : ℝ) ≤ tmax then (1 : ℝ) else 0)
        = (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ) := by
      rw [← Finset.sum_filter (p := fun t : ℕ => (t : ℝ) ≤ tmax)]
      simp
    -- the integer ceiling of the window: every admissible t < K + 1
    have hfloornn : (0 : ℤ) ≤ ⌊tmax⌋ := Int.floor_nonneg.mpr htmax_nonneg
    set K : ℕ := Int.toNat ⌊tmax⌋ with hK
    have hKz : (K : ℤ) = ⌊tmax⌋ := Int.toNat_of_nonneg hfloornn
    have hlt : tmax < (K : ℝ) + 1 := by
      have h6 : tmax < (⌊tmax⌋ : ℝ) + 1 := by
        have := Int.lt_floor_add_one tmax
        exact_mod_cast this
      have h7 : ((K : ℤ) : ℝ) = (⌊tmax⌋ : ℝ) := by rw [hKz]
      have h8 : (K : ℝ) + 1 = ((K : ℤ) : ℝ) + 1 := by push_cast; ring
      rw [h8, h7]
      exact h6
    have hsub : (Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)
        ⊆ Finset.range (K + 1) := by
      intro t ht
      simp only [Finset.mem_filter] at ht
      refine Finset.mem_range.mpr ?_
      have h9 : (t : ℝ) < (K : ℝ) + 1 := lt_of_le_of_lt ht.2 hlt
      exact_mod_cast h9
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have hKle : (K : ℝ) ≤ tmax := by
      have h10 : (⌊tmax⌋ : ℝ) ≤ tmax := Int.floor_le tmax
      have h11 : (K : ℝ) ≤ (⌊tmax⌋ : ℝ) := by
        have h12 : (K : ℤ) ≤ ⌊tmax⌋ := by rw [hKz]
        exact_mod_cast h12
      linarith
    have hcardR : ((K + 1 : ℕ) : ℝ) ≤ tmax + 1 := by
      push_cast
      linarith
    have hsumR : ∑ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ) := by
      rw [← hfil]
      exact hsum
    have hcR : (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ)
        ≤ ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    linarith
  refine ⟨by
    have hc1 := hcount
    rw [htmax] at hc1
    linarith, ?_⟩
  -- (2): (1+α)^N ≤ e^{αN} (add_one_le_exp iterated), αN ≤ α·window
  have hpow : ∀ n : ℕ, (1 + alpha) ^ n ≤ Real.exp (alpha * (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : 1 + alpha ≤ Real.exp alpha := by
          have := Real.add_one_le_exp alpha
          linarith
        have hnn : 0 ≤ 1 + alpha := by linarith
        have hnnn : 0 ≤ (1 + alpha) ^ n := pow_nonneg hnn n
        rw [pow_succ]
        calc (1 + alpha) ^ n * (1 + alpha)
            ≤ Real.exp (alpha * (n : ℝ)) * (1 + alpha) :=
                mul_le_mul_of_nonneg_right ih hnn
          _ ≤ Real.exp (alpha * (n : ℝ)) * Real.exp alpha :=
                mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
          _ = Real.exp (alpha * ((n + 1 : ℕ) : ℝ)) := by
              have he : Real.exp (alpha * (n : ℝ)) * Real.exp alpha
                  = Real.exp (alpha * (n : ℝ) + alpha) :=
                (Real.exp_add _ _).symm
              rw [he]
              congr 1
              push_cast
              ring
  have hN := hpow (∑ t ∈ Finset.range T, sigma t)
  have hNle : alpha * ((∑ t ∈ Finset.range T, sigma t : ℕ) : ℝ)
      ≤ 1 + alpha - alpha * S.capability / S.effects.growGain := by
    have hc2 : ((∑ t ∈ Finset.range T, sigma t : ℕ) : ℝ) ≤ tmax + 1 := by
      push_cast
      exact hcount
    rw [htmax] at hc2
    have hEq : alpha * (1 / alpha - S.capability / S.effects.growGain + 1)
        = 1 + alpha - alpha * S.capability / S.effects.growGain := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_left hc2 halpha.le
    rw [hEq] at hmul
    exact hmul
  exact le_trans hN (Real.exp_le_exp.mpr hNle)

/-- With h_emp_ measurable independent [0,1]-valued indicators
`s t` (mean ≥ p0), positive capability along every trajectory, and
the pointwise log-bridge `log C_{t+1} − log C_t ≥ a·s t − eps t`,
the event
`(growCycle T S ω).capability ≥ S ω.capability *
exp(a·(p0·T − concDelta T delta) − Σ eps t)` has probability
≥ `1 − delta` (instantiates `takeoff_time_form`). -/
theorem growth_state_takeoff_probabilistic
    (S : Ω → GrowthState X) (s : ℕ → Ω → ℝ)
    {T : ℕ} {delta p0 a : ℝ} {eps : ℕ → ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (ha : 0 ≤ a)
    (hCpos : ∀ t ω, 0 < (growCycle t (S ω)).capability)
    (hbridge : ∀ t ω, Real.log ((growCycle (t + 1) (S ω)).capability)
        - Real.log ((growCycle t (S ω)).capability) ≥ a * s t ω - eps t)
    (h_emp_meas : ∀ t, Measurable (s t))
    (h_emp_01 : ∀ t ω, s t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun s μ)
    (h_emp_p : ∀ t, p0 ≤ μ[s t]) :
    μ.real {ω | (growCycle T (S ω)).capability ≥ (S ω).capability * Real.exp
      (a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t)}
      ≥ 1 - delta := by
  -- the capability trajectory of the random state, an Ω-indexed scalar path
  set C : ℕ → Ω → ℝ := fun t ω => (growCycle t (S ω)).capability with hC
  have hmain := takeoff_time_form (S := s) (C := C) (T := T) (delta := delta)
    (p0 := p0) (a := a) (eps := eps) hdelta hdelta1 ha
    (fun t ω => hCpos t ω) (fun t ω => hbridge t ω)
    h_emp_meas h_emp_01 h_emp_indep h_emp_p
  have hzero : C 0 = fun ω => (S ω).capability := rfl
  rw [hzero] at hmain
  exact hmain

end GrowthBridge

end Hagi.Unified

end C238_unified
