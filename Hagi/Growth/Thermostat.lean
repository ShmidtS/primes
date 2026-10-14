/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.GibbsConcentration
import Hagi.Ensemble.Hoeffding
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

open Finset in
/-- **Концентрация после фазовой точки (R408)**: ∃N,
∀t ≥ N: share(T_t) ≥ 1 − C·θ — после единой точки
переключения (R407) система не только останавливает
эксплорацию, но и СКОНЦЕНТРИРОВАНА на минимизаторе
(R386-оценка с e^{−δ/T_t} ≤ θ). Режим
«консолидация» = сконцентрированное состояние: термостат
× Гиббс-концентрация в одном утверждении. -/
theorem phase_concentration {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      1 - (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ
        ≤ Real.exp (-(E vstar)/(T0 * α ^ t))
          / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) := by
  obtain ⟨N, hN⟩ := thermostat_phase_point α T0 δ 1 θ hα1 hα2 hT0 hδ
    (by norm_num) hθ1 hθ2
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨hstop, _⟩ := hN t ht
  have hTpos : (0:ℝ) < T0 * α ^ t :=
    mul_pos hT0 (pow_pos hα1 t)
  have hb := gibbs_concentration E δ vstar hgap (T0 * α ^ t) hTpos
  -- C * e^{-δ/T} <= C * theta
  have hC : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hscale : (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-δ/(T0 * α ^ t))
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ :=
    mul_le_mul_of_nonneg_left hstop hC
  linarith

open Finset in
/-- **Сертификат консолидации (R412)** — капстоун
контроллера: ∃N, ∀t ≥ N: эксплорация остановлена ∧
merge-гейт открыт ∧ Гиббс-концентрация ≥ 1 − Cθ. Одна
точка, три свойства: физический режим «консолидация»
HAGI формально наступает и поддерживается (max двух
горизонтов R407/R408). -/
theorem consolidation_certificate {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      Real.exp (-δ/(T0 * α ^ t)) ≤ θ
        ∧ θ * (T0 * α ^ t) ≤ θ
        ∧ 1 - (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ
          ≤ Real.exp (-(E vstar)/(T0 * α ^ t))
            / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) := by
  -- phase point from R407 (J := θ)
  obtain ⟨N, hN⟩ := thermostat_phase_point α T0 δ θ θ hα1 hα2 hT0 hδ
    hθ1 hθ1 hθ2
  -- concentration from R408
  obtain ⟨N2, hN2⟩ := phase_concentration E vstar α T0 δ hα1 hα2 hT0 hδ
    hgap θ hθ1 hθ2
  refine ⟨max N N2, fun t ht => ?_⟩
  have h1 : ((N : ℕ) : ℝ) ≤ ((max N N2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left _ _
  have h2 : ((N2 : ℕ) : ℝ) ≤ ((max N N2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right _ _
  obtain ⟨hstop, hgate⟩ := hN t (h1.trans ht)
  exact ⟨hstop, hgate, hN2 t (h2.trans ht)⟩

open Finset in
/-- **Третий мост: Гиббс × Хёфдинг (R413)**: при центрировании d по
Гиббс-мере p_T и 2|K|θ < 1 существует равномерно
ε_θ-хорошая точка — выборка из охлаждённого ансамбля
репрезентативна для всего класса (Гиббс-веса —
вероятностная мера: exp_pos + div_self; R411 напрямую).
Треугольник мостов замкнут: термостат ↔ Гиббс
(R408), термостат ↔ Хёфдинг (R409–411), Гиббс ↔
Хёфдинг (R413). -/
theorem gibbs_representative {V K : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype K]
    (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (d : K → V → ℝ) (a b : ℝ)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T)) * d k v = 0)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1)
    (hsmall : 2 * (Fintype.card K : ℝ) * θ < 1) :
    ∃ v : V, ∀ k : K,
      |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hw : ∀ v, 0 < Real.exp (-(E v)/T)
      / ∑ v, Real.exp (-(E v)/T) :=
    fun v => div_pos (exp_pos _) hZpos
  have hw1 : ∑ v, Real.exp (-(E v)/T)
      / ∑ v, Real.exp (-(E v)/T) = 1 := by
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  exact Hagi.Ensemble.calibrated_good_point
    (fun v => Real.exp (-(E v)/T) / ∑ v, Real.exp (-(E v)/T))
    d a b hw hw1 hlt hbd hc θ hθ1 hθ2 hsmall

