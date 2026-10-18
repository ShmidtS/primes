/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.GibbsConcentration
import Hagi.Probability.MWU
import Hagi.Ensemble.Hoeffding
import Hagi.Ensemble.UniformCert
set_option linter.style.header false

namespace Hagi.Growth


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

open Finset in
/-- **Сертифицированное состояние HAGI (R414)** — супер-капстоун
сети: ∃N, ∀t ≥ N: эксплорация остановлена ∧
merge-гейт открыт ∧ Гиббс-концентрация
≥ 1−Cθ ∧ существует равномерно
ε_θ-репрезентативная точка для
всего класса оценок (R412 + R413).
Три вертикали + три моста в одном
утверждении: термодинамическая машина
HAGI сертифицирована целиком. -/
theorem hagi_certified_state {V K : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype K]
    (E : V → ℝ) (vstar : V)
    (d : K → V → ℝ) (a b : ℝ)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hbd : ∀ k v, d k v ∈ Set.Icc a b) (hlt : a < b)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1)
    (hsmall : 2 * (Fintype.card K : ℝ) * θ < 1)
    (hcent : ∀ k : K, ∀ t : ℕ, ∑ v, (Real.exp (-(E v)/(T0 * α ^ t))
        / ∑ v, Real.exp (-(E v)/(T0 * α ^ t))) * d k v = 0) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      Real.exp (-δ/(T0 * α ^ t)) ≤ θ
        ∧ θ * (T0 * α ^ t) ≤ θ
        ∧ 1 - (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ
          ≤ Real.exp (-(E vstar)/(T0 * α ^ t))
            / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
        ∧ ∃ v : V, ∀ k : K,
            |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
  -- the good point does not depend on t: obtain once
  have hpt : ∃ v : V, ∀ k : K,
      |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
    -- at t = 0 the Gibbs measure is a probability measure
    have hTpos : (0:ℝ) < T0 * α ^ 0 := by
      rw [pow_zero, mul_one]; exact hT0
    exact gibbs_representative E (T0 * α ^ 0) hTpos d a b hlt hbd
      (fun k => hcent k 0) θ hθ1 hθ2 hsmall
  obtain ⟨v0, hv0⟩ := hpt
  -- controller certificate from R412
  obtain ⟨N, hN⟩ := consolidation_certificate E vstar α T0 δ hα1 hα2
    hT0 hδ hgap θ hθ1 hθ2
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN t ht
  exact ⟨h1, h2, h3, v0, hv0⟩

open Finset in
/-- **TV-следствие сертифицированного состояния (R415)**:
∃N, ∀t ≥ N: TV(p_{T_t}, δ_{v*}) ≤ C·θ — после
фазовой точки охлаждённое состояние метрически
близко к минимизатору (R408-концентрация
+ R395-TV-идентификация). -/
theorem certified_state_tv {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      (1/2) * ∑ v, |Real.exp (-(E v)/(T0 * α ^ t))
          / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
          - if v = vstar then (1:ℝ) else 0|
        ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ := by
  obtain ⟨N, hN⟩ := phase_concentration E vstar α T0 δ hα1 hα2 hT0 hδ
    hgap θ hθ1 hθ2
  refine ⟨N, fun t ht => ?_⟩
  have hTpos : (0:ℝ) < T0 * α ^ t :=
    mul_pos hT0 (pow_pos hα1 t)
  -- TV identification
  have htv := gibbs_tv_eq E (T0 * α ^ t) hTpos vstar
  -- concentration
  have hconc := hN t ht
  rw [htv]
  linarith

open Finset in
/-- **Энергетическое следствие сертифицированного состояния
(R416)**: ∃N, ∀t ≥ N: ⟨E⟩_{T_t} ≤ E* + Δ·C·θ —
энергия охлаждённого состояния прижата к
основному с θ-точностью (R393 × R407). -/
theorem certified_state_energy {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ Δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      ≤ E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * θ := by
  obtain ⟨N, hN⟩ := thermostat_phase_point α T0 δ 1 θ hα1 hα2 hT0 hδ
    (by norm_num) hθ1 hθ2
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨hstop, _⟩ := hN t ht
  have hTpos : (0:ℝ) < T0 * α ^ t :=
    mul_pos hT0 (pow_pos hα1 t)
  -- R393
  have hb := gibbs_expected_energy_bound E δ (T0 * α ^ t) hTpos
    vstar Δ hmin hgap hΔ
  -- scale the exp by theta
  have hC : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hscale : (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-δ/(T0 * α ^ t))
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ :=
    mul_le_mul_of_nonneg_left hstop hC
  -- hb RHS: E* + Δ * (C * e^{-δ/T}) <= E* + Δ * (C * θ)
  have hΔ0 : (0:ℝ) ≤ Δ := by
    have h0 := hΔ vstar
    simp only [sub_self] at h0
    linarith
  have hR : Δ * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-δ/(T0 * α ^ t)))
      ≤ Δ * ((((Finset.univ.erase vstar).card : ℕ) : ℝ) * θ) :=
    mul_le_mul_of_nonneg_left hscale hΔ0
  linarith [hb, hR]

open Finset in
/-- **Калориметрический избыток сертифицированного состояния
(R417)**: ∃N, ∀t ≥ N: ⟨E⟩_t − F_t ≤ (Δ+T₀)·C·θ —
энергетическая и свободная энергия
согласованы: избыток − тепло, запасённое в
охлаждённом состоянии, ≤ θ-масштаба
(R416 + R398: F ≥ E* − T·Cθ, T ≤ T₀). -/
theorem certified_state_excess {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ Δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    ∃ N : ℕ, ∀ t : ℕ, (N : ℝ) ≤ t →
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
        - (-(T0 * α ^ t)
          * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))))
      ≤ (Δ + T0) * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * θ := by
  obtain ⟨N1, hN1⟩ := thermostat_phase_point α T0 δ 1 θ hα1 hα2 hT0 hδ
    (by norm_num) hθ1 hθ2
  obtain ⟨N2, hN2⟩ := certified_state_energy E vstar α T0 δ Δ hα1 hα2
    hT0 hδ hmin hgap hΔ θ hθ1 hθ2
  refine ⟨max N1 N2, fun t ht => ?_⟩
  have h1 : ((N1 : ℕ) : ℝ) ≤ ((max N1 N2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left _ _
  have h2 : ((N2 : ℕ) : ℝ) ≤ ((max N1 N2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right _ _
  obtain ⟨hstop, _⟩ := hN1 t (h1.trans ht)
  have hE := hN2 t (h2.trans ht)
  set T := T0 * α ^ t with hTdef
  have hTpos : (0:ℝ) < T := mul_pos hT0 (pow_pos hα1 t)
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  -- T <= T0
  have hTle : T ≤ T0 := by
    rw [hTdef]
    have hp := pow_le_one₀ (n := t) hα1.le (le_of_lt hα2)
    calc T0 * α ^ t ≤ T0 * 1 := mul_le_mul_of_nonneg_left hp hT0.le
      _ = T0 := by ring
  -- F sharp lower, log term scaled by theta
  have hF := free_energy_sharp_lower E δ T hTpos vstar hgap
  have hC0 : (0:ℝ) ≤ C := Nat.cast_nonneg _
  have hln : Real.log (1 + C * Real.exp (-δ/T)) ≤ C * θ := by
    have hx : (0:ℝ) ≤ C * Real.exp (-δ/T) :=
      mul_nonneg hC0 (le_of_lt (exp_pos _))
    have hexp : (1:ℝ) + C * Real.exp (-δ/T)
        ≤ Real.exp (C * Real.exp (-δ/T)) := by
      linarith [Real.add_one_le_exp (C * Real.exp (-δ/T))]
    have hle := Real.log_le_log (by linarith) hexp
    rw [Real.log_exp] at hle
    calc Real.log (1 + C * Real.exp (-δ/T))
        ≤ C * Real.exp (-δ/T) := hle
      _ ≤ C * θ := mul_le_mul_of_nonneg_left hstop hC0
  -- numerator: E_mean - F <= Δ*C*θ + T*(C*θ) <= (Δ+T0)*C*θ
  have hF' : E vstar - T * (C * θ) ≤ -T * Real.log Z := by
    have hTln : T * Real.log (1 + C * Real.exp (-δ/T)) ≤ T * (C*θ) :=
      mul_le_mul_of_nonneg_left hln hTpos.le
    linarith [hF, hTln]
  have hring : Δ * C * θ + T0 * C * θ = (Δ + T0) * C * θ := by ring
  have hT2 : T * (C * θ) = T * C * θ := by ring
  rw [hT2] at hF'
  have hCθ : (0:ℝ) ≤ C * θ := mul_nonneg hC0 hθ1.le
  have hprod : T * C * θ ≤ T0 * C * θ := by nlinarith
  linarith [hE, hF', hring, hprod]

open Filter in
/-- **График охлаждения → 0 (R425)**:
T_t = T₀·α^t → 0 — семантика
термостата: температура
убывает до абсолютного
нуля (квази-нуль термостата).
Фундирует все tendsto-результаты
вертикали (R387–400 вели это
инлайн). -/
theorem thermostat_tendsto_zero (α T0 : ℝ) (hα1 : 0 < α)
    (hα2 : α < 1) :
    Tendsto (fun t : ℕ => T0 * α ^ t) atTop (nhds 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hα1) hα2
  simpa using Tendsto.const_mul T0 hp

open Finset Real Filter in
/-- **TV → 0 вдоль отжига (R426)**: сертифицированное
состояние сходится к минимизатору метрически:
TV(p_{T_t}, δ*) → 0. Сжатие: TV ≤ C·e^{−δ/T_t} ≤
C·T_t/(T_t+δ) → 0 (R386 × R395 × R425;
e^{−x} ≤ 1/(1+x) через inv_le_inv₀). Фазовый
переход R415 — не только наступает, но и
знутри всё чище: асимптотическая
чистота. -/
theorem certified_state_tv_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    Tendsto (fun t : ℕ => (1/2) * ∑ v,
        |Real.exp (-(E v)/(T0 * α ^ t))
          / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
          - if v = vstar then (1:ℝ) else 0|) atTop (nhds 0) := by
  have hTpos : ∀ t : ℕ, (0:ℝ) < T0 * α ^ t :=
    fun t => mul_pos hT0 (pow_pos hα1 t)
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  -- exp tail bound: e^{-x} <= 1/(1+x)
  have hexpb : ∀ t : ℕ, Real.exp (-δ/(T0 * α ^ t))
      ≤ 1/(1 + δ/(T0 * α ^ t)) := by
    intro t
    have hx : (0:ℝ) < δ/(T0 * α ^ t) := div_pos hδ (hTpos t)
    have h := Real.add_one_le_exp (δ/(T0 * α ^ t))
    have hinv : Real.exp (-δ/(T0 * α ^ t))
        = (Real.exp (δ/(T0 * α ^ t)))⁻¹ := by
      rw [neg_div, Real.exp_neg]
    rw [hinv, one_div, inv_le_inv₀ (by linarith) (by linarith)]
    linarith
  -- fraction equals schedule/(schedule+delta)
  have hfrac : ∀ t : ℕ, 1/(1 + δ/(T0 * α ^ t))
      = (T0 * α ^ t)/(T0 * α ^ t + δ) := by
    intro t
    field_simp
  -- pointwise: TV_t <= C * fraction
  have hbound : ∀ t : ℕ, (1/2) * ∑ v,
      |Real.exp (-(E v)/(T0 * α ^ t))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
        - if v = vstar then (1:ℝ) else 0|
      ≤ C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) := by
    intro t
    have htv := gibbs_tv_eq E (T0 * α ^ t) (hTpos t) vstar
    have hconc := gibbs_concentration E δ vstar hgap (T0 * α ^ t) (hTpos t)
    rw [htv]
    have hle1 : 1 - Real.exp (-(E vstar)/(T0*α^t))
        / (∑ v, Real.exp (-(E v)/(T0*α^t)))
        ≤ C * Real.exp (-δ/(T0*α^t)) := by linarith
    have hf : (T0*α^t)/(T0*α^t+δ)
        = 1/(1 + δ/(T0*α^t)) := (hfrac t).symm
    calc 1 - Real.exp (-(E vstar)/(T0*α^t))
          / (∑ v, Real.exp (-(E v)/(T0*α^t)))
        ≤ C * Real.exp (-δ/(T0*α^t)) := hle1
      _ ≤ C * ((T0*α^t)/(T0*α^t+δ)) := by
          rw [hf]
          exact mul_le_mul_of_nonneg_left (hexpb t) (Nat.cast_nonneg _)
  -- fraction tends to 0 (schedule -> 0, denom -> delta > 0)
  have hA := thermostat_tendsto_zero α T0 hα1 hα2
  have hB : Tendsto (fun t : ℕ => T0 * α ^ t + δ) atTop (nhds δ) := by
    simpa using hA.add tendsto_const_nhds
  have hdiv : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds ((0:ℝ)/δ)) :=
    Tendsto.div hA hB (ne_of_gt hδ)
  have hdiv0 : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds 0) := by simpa using hdiv
  have htail : Tendsto (fun t : ℕ =>
      C * ((T0 * α ^ t)/(T0 * α ^ t + δ))) atTop (nhds 0) := by
    simpa using hdiv0.const_mul C
  -- squeeze
  exact squeeze_zero (fun t =>
    mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      (Finset.sum_nonneg (fun v _ => abs_nonneg _))) hbound htail

open Finset Real Filter in
/-- **Энергия → E* вдоль термостатного
графика (R427)**: ⟨E⟩_{T_t} → E* при
T_t = T₀·α^t (аналог R394 для
δ/(n+1)-графика). Сжатие:
0 ≤ ⟨E⟩−E* ≤ ΔC·T_t/(T_t+δ) → 0
(R420 × R393 × R426-хвост). Энергетическая
чистота сертифицированного
состояния наряду с метрической (R426). -/
theorem certified_state_energy_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ Δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun t : ℕ => (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))) atTop
      (nhds (E vstar)) := by
  have hTpos : ∀ t : ℕ, (0:ℝ) < T0 * α ^ t :=
    fun t => mul_pos hT0 (pow_pos hα1 t)
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  -- tail bound (as in R426)
  have hexpb : ∀ t : ℕ, Real.exp (-δ/(T0 * α ^ t))
      ≤ (T0 * α ^ t)/(T0 * α ^ t + δ) := by
    intro t
    have hx : (0:ℝ) < δ/(T0 * α ^ t) := div_pos hδ (hTpos t)
    have h := Real.add_one_le_exp (δ/(T0 * α ^ t))
    have hinv : Real.exp (-δ/(T0 * α ^ t))
        = (Real.exp (δ/(T0 * α ^ t)))⁻¹ := by
      rw [neg_div, Real.exp_neg]
    have hf : (T0*α^t)/(T0*α^t+δ)
        = 1/(1 + δ/(T0 * α ^ t)) := by field_simp
    rw [hinv, hf, one_div, inv_le_inv₀ (by linarith) (by linarith)]
    linarith
  -- upper: <E>_t <= E* + ΔC frac
  have hupper : ∀ t : ℕ,
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      ≤ E vstar + Δ * C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) := by
    intro t
    have hb := gibbs_expected_energy_bound E δ (T0 * α ^ t) (hTpos t)
      vstar Δ hmin hgap hΔ
    have hC0 : (0:ℝ) ≤ C := Nat.cast_nonneg _
    calc (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
        ≤ E vstar + Δ * C * Real.exp (-δ/(T0 * α ^ t)) := hb
      _ ≤ E vstar + Δ * C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) := by
          have hΔ0 : (0:ℝ) ≤ Δ := by
            have h0 := hΔ vstar
            simp only [sub_self] at h0
            linarith
          have hX : Δ * C * Real.exp (-δ/(T0 * α ^ t))
              ≤ Δ * C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) :=
            mul_le_mul_of_nonneg_left (hexpb t)
              (mul_nonneg hΔ0 hC0)
          linarith
  -- lower: E* <= <E>_t (R420)
  have hlower : ∀ t : ℕ, E vstar ≤ (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) :=
    fun t => gibbs_expected_energy_lower E (T0 * α ^ t) (hTpos t) vstar hmin
  -- tail tends to 0 (as in R426)
  have hA := thermostat_tendsto_zero α T0 hα1 hα2
  have hB : Tendsto (fun t : ℕ => T0 * α ^ t + δ) atTop (nhds δ) := by
    simpa using hA.add tendsto_const_nhds
  have hdiv : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds ((0:ℝ)/δ)) :=
    Tendsto.div hA hB (ne_of_gt hδ)
  have hdiv0 : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds 0) := by simpa using hdiv
  -- squeeze on difference
  have hdiff : Tendsto (fun t : ℕ =>
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) - E vstar)
      atTop (nhds 0) := by
    refine squeeze_zero
      (g := fun t => Δ * C * ((T0 * α ^ t)/(T0 * α ^ t + δ))) ?_ ?_ ?_
    · intro t
      have := hlower t
      linarith
    · intro t
      have := hupper t
      have hΔ0 : (0:ℝ) ≤ Δ := by
        have h0 := hΔ vstar
        simp only [sub_self] at h0
        linarith
      have hC0 : (0:ℝ) ≤ C := Nat.cast_nonneg _
      have hfrac : (0:ℝ) ≤ (T0 * α ^ t)/(T0 * α ^ t + δ) := by
        apply div_nonneg (le_of_lt (hTpos t))
        linarith [hTpos t]
      have hpos : (0:ℝ) ≤ Δ * C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) :=
        mul_nonneg (mul_nonneg hΔ0 hC0) hfrac
      linarith
    · simpa using hdiv0.const_mul (Δ * C)
  have heq : (fun t : ℕ => (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))))
      = (fun t : ℕ => ((∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) - E vstar) + E vstar) := by
    funext t
    ring
  rw [heq]
  simpa using hdiff.add (tendsto_const_nhds (x := E vstar))

open Finset Real Filter in
/-- **F → E* вдоль термостатного графика (R428)**:
свободная энергия сходится к
основному состоянию при
T_t = T₀·α^t (аналог R399 для
δ/(n+1)-графика). Сжатие:
0 ≤ E*−F ≤ T_t·C·T_t/(T_t+δ) → 0
(R398 × ln(1+x) ≤ x × R421). Триада
чистоты завершена: метрика
(R426) + энергетика (R427) +
свободная энергия (R428). -/
theorem certified_state_free_energy_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    Tendsto (fun t : ℕ => -(T0 * α ^ t)
      * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))))
      atTop (nhds (E vstar)) := by
  have hTpos : ∀ t : ℕ, (0:ℝ) < T0 * α ^ t :=
    fun t => mul_pos hT0 (pow_pos hα1 t)
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  have hC0 : (0:ℝ) ≤ C := Nat.cast_nonneg _
  -- exp tail bound (R426-style)
  have hexpb : ∀ t : ℕ, Real.exp (-δ/(T0 * α ^ t))
      ≤ (T0 * α ^ t)/(T0 * α ^ t + δ) := by
    intro t
    have hx : (0:ℝ) < δ/(T0 * α ^ t) := div_pos hδ (hTpos t)
    have h := Real.add_one_le_exp (δ/(T0 * α ^ t))
    have hinv : Real.exp (-δ/(T0 * α ^ t))
        = (Real.exp (δ/(T0 * α ^ t)))⁻¹ := by
      rw [neg_div, Real.exp_neg]
    have hf : (T0*α^t)/(T0*α^t+δ)
        = 1/(1 + δ/(T0 * α ^ t)) := by field_simp
    rw [hinv, hf, one_div, inv_le_inv₀ (by linarith) (by linarith)]
    linarith
  -- log(1 + C e) <= C * frac
  have hlogb : ∀ t : ℕ, Real.log (1 + C * Real.exp (-δ/(T0 * α ^ t)))
      ≤ C * ((T0 * α ^ t)/(T0 * α ^ t + δ)) := by
    intro t
    have h1 : Real.log (1 + C * Real.exp (-δ/(T0 * α ^ t)))
        ≤ C * Real.exp (-δ/(T0 * α ^ t)) := by
      have hpos : (0:ℝ) < 1 + C * Real.exp (-δ/(T0 * α ^ t)) := by
        have hnn : (0:ℝ) ≤ C * Real.exp (-δ/(T0 * α ^ t)) :=
          mul_nonneg hC0 (le_of_lt (exp_pos _))
        linarith
      have h2 := Real.log_le_sub_one_of_pos hpos
      linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_left (hexpb t) hC0)
  -- sharp lower bound scaled
  have hFge : ∀ t : ℕ, E vstar - (T0 * α ^ t)
      * (C * ((T0 * α ^ t)/(T0 * α ^ t + δ)))
      ≤ -(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) := by
    intro t
    have hF := free_energy_sharp_lower E δ (T0 * α ^ t) (hTpos t) vstar hgap
    have hlog := hlogb t
    have hTnn : (0:ℝ) ≤ T0 * α ^ t := le_of_lt (hTpos t)
    have hmul : (T0 * α ^ t)
        * Real.log (1 + C * Real.exp (-δ/(T0 * α ^ t)))
        ≤ (T0 * α ^ t) * (C * ((T0 * α ^ t)/(T0 * α ^ t + δ))) :=
      mul_le_mul_of_nonneg_left hlog hTnn
    linarith
  -- upper: F <= E*
  have hFle : ∀ t : ℕ, -(T0 * α ^ t)
      * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      ≤ E vstar :=
    fun t => free_energy_upper E (T0 * α ^ t) (hTpos t) vstar
  -- tail: T_t * C * frac -> 0
  have hA := thermostat_tendsto_zero α T0 hα1 hα2
  have hB : Tendsto (fun t : ℕ => T0 * α ^ t + δ) atTop (nhds δ) := by
    simpa using hA.add tendsto_const_nhds
  have hdiv : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds ((0:ℝ)/δ)) :=
    Tendsto.div hA hB (ne_of_gt hδ)
  have hdiv0 : Tendsto (fun t : ℕ => (T0 * α ^ t)/(T0 * α ^ t + δ))
      atTop (nhds 0) := by simpa using hdiv
  have htail : Tendsto (fun t : ℕ => (T0 * α ^ t)
      * (C * ((T0 * α ^ t)/(T0 * α ^ t + δ)))) atTop (nhds 0) := by
    simpa using Tendsto.mul hA (hdiv0.const_mul C)
  -- squeeze on E* - F
  have hdiff : Tendsto (fun t : ℕ => E vstar - (-(T0 * α ^ t)
      * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))))
      atTop (nhds 0) := by
    refine squeeze_zero
      (g := fun t => (T0 * α ^ t)
        * (C * ((T0 * α ^ t)/(T0 * α ^ t + δ)))) ?_ ?_ htail
    · intro t
      have := hFle t
      linarith
    · intro t
      have := hFge t
      linarith
  -- final: F = E* - (E* - F)
  have heq : (fun t : ℕ => -(T0 * α ^ t)
      * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))))
      = (fun t : ℕ => E vstar - (E vstar - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))))) := by
    funext t
    ring
  rw [heq]
  simpa using (tendsto_const_nhds (x := E vstar)).sub hdiff

private lemma exp_div_tail (T δ e : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (he0 : 0 ≤ e)
    (he : e ≤ (2*T/(2*T+δ))*(2*T/(2*T+δ))) :
    e / T ≤ (4:ℝ) * T / δ^2 := by
  have hu : (0:ℝ) < 2*T + δ := by linarith
  have h1 : (2*T/(2*T+δ))*(2*T/(2*T+δ))
      = (2*T)*(2*T)/((2*T+δ)*(2*T+δ)) := by
    field_simp
  rw [h1] at he
  have huu : (0:ℝ) < (2*T+δ)*(2*T+δ) := by positivity
  rw [le_div_iff₀ huu] at he
  have h3 : δ*δ ≤ (2*T+δ)*(2*T+δ) := by
    nlinarith [hu]
  have hstep : e * (δ*δ) ≤ e * ((2*T+δ)*(2*T+δ)) :=
    mul_le_mul_of_nonneg_left h3 he0
  rw [div_le_div_iff₀ hT (by positivity : (0:ℝ) < δ^2)]
  linarith

open Finset Real Filter in
/-- **Нернст на термостатном графике (R429)**:
S_t = (⟨E⟩−F)/T_t → 0 при T_t = T₀·α^t — третий закон на
реальном охлаждении. Ключ: острыह хвост
e^{−δ/T} = (e^{−δ/2T})² ≤ (2T/(2T+δ))² ⟹ e/T ≤ 4T/δ².
ЧЕТВЕРТА чистоты: метрика (R426) + энергетика (R427) +
свободная энергия (R428) + энтропия (R429). -/
theorem certified_state_entropy_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ Δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun t : ℕ => (
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))))
      / (T0 * α ^ t)) atTop (nhds 0) := by
  have hTpos : ∀ t : ℕ, (0:ℝ) < T0 * α ^ t :=
    fun t => mul_pos hT0 (pow_pos hα1 t)
  have hCnn : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hΔ0 : (0:ℝ) ≤ Δ := by
    have h0 := hΔ vstar
    simp only [sub_self] at h0
    linarith
  -- half-tail
  have hhalf : ∀ t : ℕ, Real.exp (-(δ/(T0 * α ^ t)/2))
      ≤ (2*(T0 * α ^ t))/(2*(T0 * α ^ t) + δ) := by
    intro t
    have h1 : Real.exp (-(δ/(T0 * α ^ t)/2))
        = (Real.exp (δ/(T0 * α ^ t)/2))⁻¹ := by
      rw [Real.exp_neg]
    have h2 : δ/(T0 * α ^ t)/2 + 1
        ≤ Real.exp (δ/(T0 * α ^ t)/2) :=
      Real.add_one_le_exp (δ/(T0 * α ^ t)/2)
    have hxp : (0:ℝ) < δ/(T0 * α ^ t) := div_pos hδ (hTpos t)
    have h3 : (0:ℝ) < δ/(T0 * α ^ t)/2 + 1 := by linarith
    have hiv : (Real.exp (δ/(T0 * α ^ t)/2))⁻¹
        ≤ (δ/(T0 * α ^ t)/2 + 1)⁻¹ := by
      exact (inv_le_inv₀ (exp_pos _) h3).mpr (by linarith)
    have h4 : (δ/(T0 * α ^ t)/2 + 1)⁻¹
        = (2*(T0 * α ^ t))/(2*(T0 * α ^ t) + δ) := by
      field_simp
      ring
    rw [h4] at hiv
    rw [h1]
    exact hiv
  -- squared tail
  have hsq : ∀ t : ℕ, Real.exp (-δ/(T0 * α ^ t))
      ≤ ((2*(T0 * α ^ t))/(2*(T0 * α ^ t) + δ))
        * ((2*(T0 * α ^ t))/(2*(T0 * α ^ t) + δ)) := by
    intro t
    have hsplit : Real.exp (-δ/(T0 * α ^ t))
        = Real.exp (-(δ/(T0 * α ^ t)/2))
          * Real.exp (-(δ/(T0 * α ^ t)/2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    exact mul_self_le_mul_self (le_of_lt (exp_pos _)) (hhalf t)
  -- F lower with log(1+x) <= x
  have hFge : ∀ t : ℕ, E vstar - (T0 * α ^ t)
      * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/(T0 * α ^ t)))
      ≤ -(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))) := by
    intro t
    have hF := free_energy_sharp_lower E δ (T0 * α ^ t) (hTpos t) vstar hgap
    have hln : Real.log (1
        + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t)))
        ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t)) := by
      have hpos : (0:ℝ) < 1
          + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-δ/(T0 * α ^ t)) := by
        have hnn : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-δ/(T0 * α ^ t)) :=
          mul_nonneg hCnn (le_of_lt (exp_pos _))
        linarith
      have h2 := Real.log_le_sub_one_of_pos hpos
      linarith
    have hTnn : (0:ℝ) ≤ T0 * α ^ t := le_of_lt (hTpos t)
    have hmul : (T0 * α ^ t)
        * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t)))
        ≤ (T0 * α ^ t)
          * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-δ/(T0 * α ^ t))) :=
      mul_le_mul_of_nonneg_left hln hTnn
    linarith
  -- energy upper
  have hEup : ∀ t : ℕ, (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
      / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      ≤ E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/(T0 * α ^ t)) :=
    fun t => gibbs_expected_energy_bound E δ (T0 * α ^ t) (hTpos t) vstar Δ
      hmin hgap hΔ
  -- F <= E*
  have hFle : ∀ t : ℕ, -(T0 * α ^ t)
      * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      ≤ E vstar :=
    fun t => free_energy_upper E (T0 * α ^ t) (hTpos t) vstar
  -- numerator bound: 0 <= num <= (ΔC + T0C)*exp
  have hnum : ∀ t : ℕ,
      (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t))))
      ≤ (Δ + T0) * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/(T0 * α ^ t)) := by
    intro t
    -- T*C*exp <= T0*C*exp
    have hTle : T0 * α ^ t ≤ T0 := by
      have hp := pow_le_one₀ (n := t) hα1.le (le_of_lt hα2)
      calc T0 * α ^ t ≤ T0 * 1 := mul_le_mul_of_nonneg_left hp hT0.le
        _ = T0 := by ring
    have h1 := hEup t
    have h2 := hFge t
    have hsplit : (Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/(T0 * α ^ t))
        = Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t))
        + (T0 * α ^ t)
          * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-δ/(T0 * α ^ t)))
        + (T0 - T0 * α ^ t)
          * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-δ/(T0 * α ^ t))) := by
      have hC : (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t)) ≥ 0 :=
        mul_nonneg hCnn (le_of_lt (exp_pos _))
      nlinarith [hTle, hC]
    rw [hsplit]
    have hpos : (0:ℝ) ≤ (T0 - T0 * α ^ t)
        * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/(T0 * α ^ t))) := by
      apply mul_nonneg _ (mul_nonneg hCnn (le_of_lt (exp_pos _)))
      linarith
    linarith
  -- pointwise bound via scalar lemma
  have hS : ∀ t : ℕ,
      ((∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))))
      / (T0 * α ^ t)
      ≤ ((Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * (4:ℝ)/δ^2) * (T0 * α ^ t) := by
    intro t
    have htail := exp_div_tail (T0 * α ^ t) δ
      (Real.exp (-δ/(T0 * α ^ t))) (hTpos t) hδ
      (le_of_lt (exp_pos _)) (hsq t)
    -- num/T <= (Δ+T0)C * (exp/T) <= (Δ+T0)C * 4T/δ²
    rw [div_le_iff₀ (hTpos t)]
    have hexp4 : Real.exp (-δ/(T0 * α ^ t))
        ≤ (4:ℝ)/δ^2 * (T0 * α ^ t) * (T0 * α ^ t) := by
      have h0 := htail
      rw [div_le_iff₀ (hTpos t)] at h0
      calc Real.exp (-δ/(T0 * α ^ t))
          ≤ (4:ℝ)*(T0 * α ^ t)/δ^2 * (T0 * α ^ t) := h0
        _ = (4:ℝ)/δ^2 * (T0 * α ^ t) * (T0 * α ^ t) := by
            field_simp
    have hM : (0:ℝ) ≤ (Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ) := by
      apply mul_nonneg (by linarith) hCnn
    have hMstep := mul_le_mul_of_nonneg_left hexp4 hM
    have hring2 : ((Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
        * ((4:ℝ)/δ^2 * (T0 * α ^ t) * (T0 * α ^ t))
      = ((Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * (4:ℝ)/δ^2) * (T0 * α ^ t) * (T0 * α ^ t) := by
      field_simp
    linarith [hnum t, hMstep, hring2]
  -- squeeze
  refine squeeze_zero
    (g := fun t => ((Δ + T0)
      * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * (4:ℝ)/δ^2) * (T0 * α ^ t)) ?_ hS ?_
  · intro t
    have h1 := hEup t
    have h2 := hFle t
    have hlow := gibbs_expected_energy_lower E (T0 * α ^ t) (hTpos t)
      vstar hmin
    have hnn : (0:ℝ) ≤ (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))) := by
      linarith
    exact div_nonneg hnn (le_of_lt (hTpos t))
  · simpa using (thermostat_tendsto_zero α T0 hα1 hα2).const_mul
      (((Δ + T0)
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * (4:ℝ)/δ^2))

open Finset Real Filter in
/-- **Калориметрический нуль (R430)**:
⟨E⟩_t − F_t → 0 вдоль термостата
(мгновенная композиция R427 + R428
через Tendsto.sub): запасённое тепло
исчезает — асимптотическая
версия R417. -/
theorem certified_state_excess_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (vstar : V)
    (α T0 δ Δ : ℝ) (hα1 : 0 < α) (hα2 : α < 1)
    (hT0 : 0 < T0) (hδ : 0 < δ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun t : ℕ => (∑ v, E v * Real.exp (-(E v)/(T0 * α ^ t)))
        / (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))
      - (-(T0 * α ^ t)
        * Real.log (∑ v, Real.exp (-(E v)/(T0 * α ^ t)))))
      atTop (nhds 0) := by
  have hE := certified_state_energy_tendsto E vstar α T0 δ Δ hα1 hα2
    hT0 hδ hmin hgap hΔ
  have hF := certified_state_free_energy_tendsto E vstar α T0 δ hα1 hα2
    hT0 hδ hgap
  simpa using hE.sub hF

/-- **Монотонность охлаждения (R431)**:
T_{t+1} = T₀·α^{t+1} ≤ T₀·α^t = T_t —
температура не растёт
(семантический кирпич
для всех тендст-результатов
вертикали). -/
theorem thermostat_monotone (α T0 : ℝ) (hα1 : 0 < α)
    (hα2 : α < 1) (hT0 : 0 < T0) (t : ℕ) :
    T0 * α ^ (t+1) ≤ T0 * α ^ t := by
  have hp : (0:ℝ) ≤ α ^ t := pow_nonneg (le_of_lt hα1) t
  have hkey : α ^ (t+1) = α ^ t * α := pow_succ α t
  rw [hkey]
  have hinner : α ^ t * α ≤ α ^ t * 1 :=
    mul_le_mul_of_nonneg_left (le_of_lt hα2) hp
  have hfin : T0 * (α ^ t * α) ≤ T0 * (α ^ t * 1) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt hT0)
  linarith [hfin]

open Finset in
/-- **Хёфдинг ↔ MWU: последний
мост (R442)**: выборка из
hedge-распределения
w_T ∝ e^{−ηL} репрезентативна
для всего класса оценок при
2|K|θ < 1 (R413 при E := L, T := 1/η —
тождество весов). ПОЛНЫЙ
ГРАФ МОСТОВ: 4 вертикали,
все 6 пар соединены. -/
theorem mwu_representative {V K : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] [Fintype K]
    (L : V → ℝ) (η : ℝ) (hη : 0 < η)
    (d : K → V → ℝ) (a b : ℝ)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k : K, ∑ v, (Real.exp (-(η * L v))
        / ∑ v, Real.exp (-(η * L v))) * d k v = 0)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1)
    (hsmall : 2 * (Fintype.card K : ℝ) * θ < 1) :
    ∃ v : V, ∀ k : K,
      |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
  have hkey : ∀ v : V, Real.exp (-(η * L v))
      = Real.exp (-(L v)/(1/η)) := by
    intro v
    congr 1
    field_simp
  have hc' : ∀ k : K, ∑ v, (Real.exp (-(L v)/(1/η))
      / ∑ v, Real.exp (-(L v)/(1/η))) * d k v = 0 := by
    intro k
    have hsum : ∑ v, Real.exp (-(L v)/(1/η))
        = ∑ v, Real.exp (-(η * L v)) :=
      Finset.sum_congr rfl (fun v _ => (hkey v).symm)
    have := hc k
    rw [← hsum] at this
    rw [Finset.sum_congr rfl (fun v _ => by rw [hkey v])] at this
    exact this
  have hT : (0:ℝ) < 1/η := by positivity
  exact gibbs_representative L (1/η) hT d a b hlt hbd hc' θ hθ1 hθ2 hsmall

end Hagi.Growth

export Hagi.Growth (certified_state_energy certified_state_energy_tendsto certified_state_entropy_tendsto certified_state_excess certified_state_excess_tendsto certified_state_free_energy_tendsto certified_state_tv certified_state_tv_tendsto consolidation_certificate exp_div_tail gibbs_representative hagi_certified_state merge_gate_eventually mwu_representative phase_concentration thermostat_monotone thermostat_phase_point thermostat_stop thermostat_tendsto_zero)
