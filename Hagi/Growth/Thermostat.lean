/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

/-!
# Термостат селектора (R388) — сертифицированный горизонт остановки

Архитектурный идеал: HAGI как термодинамическая машина;
температура — измеряемая величина контроллера, а не
гиперпараметр. Термостат: расписание охлаждения
T_t = T₀·α^t; admission-порог и merge-гейт масштабируются
от T. Из закона концентрации Гиббса (R386/R387): эксплорация
останавливается ПО ЗАКОНУ — когда e^{−δ/T_t} ≤ θ.

`thermostat_stop`: замкнутый горизонт остановки

  N = ⌈ ln(δ/(T₀·ln(1/θ))) / ln α ⌉

(α ∈ (0,1), θ ∈ (0,1), δ > 0 — зазор энергий): для всех
t ≥ N: e^{−δ/(T₀·α^t)} ≤ θ. Stopping-by-law вместо
эвристики stop_condition: §1-селектор, liveness two-axis и
saturation объединяются в один физический контур.

Маршрут: t ≥ N ⟹ t·ln α ≤ ln c (знак!) ⟹ α^t ≤ c
= δ/(T₀·ln(1/θ)) ⟹ T₀α^t ≤ δ/ln(1/θ) ⟹ −δ/T_t ≤ ln θ
⟹ exp ≤ θ. -/
open Real

theorem thermostat_stop (α T0 δ θ : ℝ) (hα1 : 0 < α)
    (hα2 : α < 1) (hT0 : 0 < T0) (hδ : 0 < δ)
    (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∀ t : ℕ,
      (Nat.ceil (Real.log (δ/(T0 * Real.log (1/θ)))
        / Real.log α) : ℝ) ≤ t →
      Real.exp (-δ/(T0 * α^t)) ≤ θ := by
  intro t ht
  have hlθ : (0:ℝ) < Real.log (1/θ) :=
    Real.log_pos (by
      rw [lt_div_iff₀ hθ1]
      linarith)
  have hlnα : Real.log α < 0 := by
    rw [Real.log_neg_iff hα1]
    exact hα2
  set c : ℝ := δ/(T0 * Real.log (1/θ)) with hc
  have hcpos : (0:ℝ) < c := div_pos hδ (mul_pos hT0 hlθ)
  -- x := log c / log α <= (t : ℝ)
  have hN : Real.log c / Real.log α ≤ (t : ℝ) :=
    le_trans (Nat.le_ceil _) ht
  -- t * ln α <= ln c  (ln α < 0: multiply flips)
  have hkey : ((t : ℕ) : ℝ) * Real.log α ≤ Real.log c := by
    have hmul : (t : ℝ) * Real.log α
        ≤ (Real.log c / Real.log α) * Real.log α :=
      mul_le_mul_of_nonpos_right hN (le_of_lt hlnα)
    rw [div_mul_cancel₀ _ hlnα.ne] at hmul
    exact hmul
  -- alpha^t <= c
  have hαpos : (0:ℝ) < α ^ t := pow_pos hα1 t
  have hpow : α ^ t ≤ c :=
    (Real.log_le_log_iff hαpos hcpos).mp (by
      rw [Real.log_pow]
      exact hkey)
  -- T0 * α^t <= δ / ln(1/θ)
  have hTt : (0:ℝ) < T0 * α ^ t := mul_pos hT0 hαpos
  have hTle : T0 * α ^ t ≤ δ / Real.log (1/θ) := by
    rw [le_div_iff₀ hlθ]
    have hmul : T0 * α ^ t * Real.log (1/θ)
        ≤ T0 * c * Real.log (1/θ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (le_of_lt hT0))
        (le_of_lt hlθ)
    have hsimp : T0 * c * Real.log (1/θ) = δ := by
      rw [hc]
      field_simp
    rw [hsimp] at hmul
    exact hmul
  -- final: -δ/(T0 α^t) <= ln θ, then exp <= θ
  have hstep : Real.log (1/θ) ≤ δ / (T0 * α ^ t) := by
    rw [le_div_iff₀ hTt]
    have hmul := (le_div_iff₀ hlθ).mp hTle
    have hpos' : (0:ℝ) < Real.log (1/θ) * (T0 * α ^ t) :=
      mul_pos hlθ hTt
    calc Real.log (1/θ) * (T0 * α ^ t)
        = Real.log (1/θ) * (T0 * α ^ t) := rfl
      _ = T0 * α ^ t * Real.log (1/θ) := by ring
      _ ≤ δ := hmul
  have hneglog : -Real.log (1/θ) = Real.log θ := by
    rw [one_div, Real.log_inv]
    ring
  have hfinal : -δ / (T0 * α ^ t) ≤ Real.log θ := by
    rw [← hneglog, neg_div]
    exact neg_le_neg hstep
  exact (Real.exp_le_exp.mpr hfinal).trans_eq (Real.exp_log hθ1)

open Filter in
/-- **Merge-гейт: фазовый переход неизбежен (R389)**: при
охлаждении `T_t = T₀·α^t` любой положительный Jensen-зазор
`J > 0` рано или поздно проходит гейт `J ≥ θ·T_t` —
eventually-форма: слияние (конденсация листьев в корень)
происходит ПО ЗАКОНУ охлаждения, а не по эвристике.
Переиспользует `tendsto_pow_atTop_nhds_zero_of_lt_one`. -/
theorem merge_gate_eventually (α T0 J θ : ℝ) (hα1 : 0 < α)
    (hα2 : α < 1) (hT0 : 0 < T0) (hJ : 0 < J) (hθ : 0 < θ) :
    ∀ᶠ t in atTop, θ * (T0 * α^t) ≤ J := by
  have hpow : Tendsto (fun t => α^t) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hα1) hα2
  have hmul : Tendsto (fun t => T0 * α^t) atTop (nhds (T0 * 0)) :=
    hpow.const_mul T0
  have hz : (T0:ℝ) * 0 = 0 := by ring
  rw [hz] at hmul
  have hev := hmul.eventually (gt_mem_nhds
    (by positivity : (0:ℝ) < J / θ))
  filter_upwards [hev] with t ht
  have : θ * (T0 * α^t) ≤ θ * (J / θ) :=
    mul_le_mul_of_nonneg_left (le_of_lt ht) (le_of_lt hθ)
  rwa [mul_div_cancel₀ _ hθ.ne'] at this

open Filter in
/-- **Единая фазовая точка (R407)**: ∃ N, ∀ t ≥ N:
эксплорация остановлена (e^{−δ/T_t} ≤ θ, R388) ∧
merge-гейт открыт (θ·T_t ≤ J, R389) — контроллер
охлаждения сертифицированно достигает режима
«консолидация»: одна точка переключения для всего T-контура
(max двух горизонтов). -/
theorem thermostat_phase_point (α T0 δ J θ : ℝ)
    (hα1 : 0 < α) (hα2 : α < 1) (hT0 : 0 < T0) (hδ : 0 < δ)
    (hJ : 0 < J) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      Real.exp (-δ/(T0 * α ^ t)) ≤ θ
        ∧ θ * (T0 * α ^ t) ≤ J := by
  -- R388 stopping horizon
  have hstop := thermostat_stop α T0 δ θ hα1 hα2 hT0 hδ hθ1 hθ2
  -- R389 merge gate eventually: extract concrete bound
  have hgate := merge_gate_eventually α T0 J θ hα1 hα2 hT0 hJ hθ1
  rw [eventually_iff] at hgate
  obtain ⟨N2, hN2⟩ := mem_atTop_sets.mp hgate
  -- take N = max of the two bounds
  set N : ℕ := max (Nat.ceil (Real.log (δ/(T0 * Real.log (1/θ)))
      / Real.log α)) N2 with hNdef
  refine ⟨N, fun t ht => ?_⟩
  have hmax1 : ((Nat.ceil (Real.log (δ/(T0 * Real.log (1/θ)))
      / Real.log α)) : ℝ) ≤ ((N : ℕ) : ℝ) := by
    rw [hNdef]
    exact_mod_cast Nat.le_max_left _ _
  have hmax2 : ((N2 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
    rw [hNdef]
    exact_mod_cast Nat.le_max_right _ _
  exact ⟨hstop t (hmax1.trans ht), hN2 t (Nat.cast_le.mp (hmax2.trans ht))⟩

