/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

/-!
# Концентрация меры Гиббса при T → 0 (R386)

Термодинамический закон для обучения: при температуре T
распределение Гиббса p_T(v) ∝ exp(−E(v)/T) концентрируется
на глобальном минимуме энергии при охлаждении T → 0⁺ —
фундамент simulated annealing, temperature scaling и
softmax-охлаждения в обучении HAGI.

Формально: при δ-зазоре (E(v*) + δ ≤ E(v) для всех
конкурентов) доля веса минимума

  e^{−E*/T} / Σ_v e^{−E(v)/T}  ≥  1 − (|V|−1)·e^{−δ/T}.

Маршрут: сдвиг энергий (доля = 1/(1+S), S — сумма весов
конкурентов относительно e^{−E*/T}), S ≤ (n−1)e^{−δ/T}
(поточечная экспоненциальная оценка), и 1/(1+x) ≥ 1−x.

Связь с вертикалью: ThermoAxes (оси охлаждения) +
GibbsConcentration (куда сходится охлаждение) —
термодинамический каркас обучения. -/
open Finset Real

theorem gibbs_concentration {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Real.exp (-(E vstar) / T) / ∑ v, Real.exp (-(E v) / T)
      ≥ 1 - ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T) := by
  -- shift energies: numerator/denominator divided by e^{-E*/T}
  have hpos : (0:ℝ) < ∑ v, Real.exp (-(E v) / T) :=
    Finset.sum_pos (fun v _ => exp_pos _) (⟨Classical.arbitrary V, Finset.mem_univ _⟩)
  -- denominator = e^{-E*/T} * (1 + S), S = sum over competitors
  set S : ℝ := ∑ v ∈ Finset.univ.erase vstar,
      Real.exp (-(E v - E vstar) / T) with hS
  have hden : ∑ v, Real.exp (-(E v) / T)
      = Real.exp (-(E vstar) / T) * (1 + S) := by
    have hsplit : ∑ v, Real.exp (-(E v) / T)
        = ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v) / T)
          + Real.exp (-(E vstar) / T) := by
      rw [Finset.sum_erase_add (Finset.univ : Finset V)
        (fun v => Real.exp (-(E v) / T))
        (Finset.mem_univ vstar)]
    rw [hsplit]
    have hfact : ∑ v ∈ Finset.univ.erase vstar,
        Real.exp (-(E v) / T)
        = Real.exp (-(E vstar) / T) * S := by
      calc ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v) / T)
          = ∑ v ∈ Finset.univ.erase vstar,
              Real.exp (-(E vstar) / T)
                * Real.exp (-(E v - E vstar) / T) :=
            Finset.sum_congr rfl (fun v _ => by
              rw [← Real.exp_add]
              congr 1
              field_simp
              ring)
        _ = Real.exp (-(E vstar) / T) * S := by
            rw [Finset.mul_sum]
    rw [hfact]
    ring
  -- bound S
  have hSpos : (0:ℝ) ≤ S := Finset.sum_nonneg
    (fun v _ => le_of_lt (exp_pos _))
  have hSbound : S ≤ ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) := by
    have hterm : ∀ v ∈ Finset.univ.erase vstar,
        Real.exp (-(E vstar + δ - E vstar) / T)
          = Real.exp (-δ / T) := by
      intro v _
      congr 1
      congr 1
      ring
    calc S ≤ ∑ v ∈ Finset.univ.erase vstar,
          Real.exp (-(E vstar + δ - E vstar) / T) := by
          refine Finset.sum_le_sum ?_
          intro v hv
          have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
          have hE : E vstar + δ - E vstar ≤ E v - E vstar :=
            by
            have := hgap v hvne
            linarith
          exact Real.exp_le_exp.mpr (by
            rw [div_le_div_iff₀ hT hT]
            nlinarith [hT])
      _ = ∑ v ∈ Finset.univ.erase vstar,
          Real.exp (-δ / T) :=
            Finset.sum_congr rfl (fun v hv => hterm v hv)
      _ = ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T) := by
          rw [Finset.sum_const]
          norm_num
  -- final: share = 1/(1+S) >= 1 - card*e^{-δ/T}
  set Ce : ℝ := ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) with hCe
  have hCenn : (0:ℝ) ≤ Ce := mul_nonneg
    (by positivity) (le_of_lt (exp_pos _))
  have hdiv : Real.exp (-(E vstar) / T)
      / (Real.exp (-(E vstar) / T) * (1 + S)) = 1 / (1 + S) := by
    field_simp
  rw [hden, hdiv]
  have hmono1 : 1 / (1 + Ce) ≤ 1 / (1 + S) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hmono2 : 1 - Ce ≤ 1 / (1 + Ce) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 + Ce)]
    nlinarith [mul_self_nonneg Ce]
  exact hmono2.trans hmono1

open Filter in
/-- **Предел концентрации при охлаждении (R387)**: вдоль
annealing-графика T_n = δ/(n+1) доля глобального минимума
стремится к 1 — закон охлаждения в предельной форме.
Маршрут: R386-оценка при T = T_n (показатель −δ/T_n = −(n+1)
— точное сокращение через field_simp), share ≤ 1
(`Finset.single_le_sum`), и двусторонний squeeze с
exp(−(n+1)) → 0 (`Tendsto.add_atBot` + `Real.tendsto_exp_atBot`). -/
theorem gibbs_concentration_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    Tendsto (fun n => Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) atTop (nhds 1) := by
  -- temperature schedule T_n = δ/(n+1) > 0
  have hTnpos : ∀ n, (0:ℝ) < δ/((n+1 : ℕ) : ℝ) := fun n =>
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  have hδT : ∀ n, -δ / (δ/((n+1 : ℕ) : ℝ)) = -((n+1 : ℕ) : ℝ) := by
    intro n
    field_simp
  -- per-n bound from R386
  have hbound : ∀ n, (1:ℝ)
      - ((Finset.univ.erase vstar).card : ℝ) * Real.exp (-((n+1 : ℕ) : ℝ))
      ≤ Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) := by
    intro n
    have hge := gibbs_concentration E δ vstar hgap _ (hTnpos n)
    rw [hδT n] at hge
    exact hge
  -- share <= 1
  have hle : ∀ n, Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) ≤ 1 := by
    intro n
    have hpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) :=
      Finset.sum_pos (fun v _ => exp_pos _)
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    have hsingle := Finset.single_le_sum
      (f := fun v => Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vstar)
    rw [div_le_one hpos]
    exact hsingle
  -- exp(-(n+1)) -> 0
  have hexp0 : Tendsto (fun n => Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hnat : Tendsto (fun n => -((n+1 : ℕ) : ℝ)) atTop atBot := by
      have hbase : Tendsto (fun n => -((n:ℕ):ℝ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
      have hstep : Tendsto (fun n => -(1:ℝ) + -((n:ℕ):ℝ)) atTop atBot :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => -(1:ℝ)) atTop
          (nhds (-(1:ℝ)))).add_atBot hbase
      have hconv : (fun n => -(1:ℝ) + -((n:ℕ):ℝ))
          = fun n => -((n+1 : ℕ) : ℝ) := by
        funext n
        push_cast
        ring
      exact hconv ▸ hstep
    exact Real.tendsto_exp_atBot.comp hnat
  -- lower bound -> 1
  have hlow : Tendsto (fun n => (1:ℝ)
      - ((Finset.univ.erase vstar).card : ℝ) * Real.exp (-((n+1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
    have hstep : Tendsto (fun n => (1:ℝ)
        - ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))) atTop
        (nhds (1 - ((Finset.univ.erase vstar).card : ℝ) * 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds (1:ℝ))).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ((Finset.univ.erase vstar).card : ℝ))
          atTop (nhds ((Finset.univ.erase vstar).card : ℝ))).mul hexp0)
    have hlim : (1:ℝ) - ((Finset.univ.erase vstar).card : ℝ) * 0 = 1 := by ring
    rw [hlim] at hstep
    exact hstep
  -- squeeze
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => hbound n) (fun n => hle n)

/-- **Сэндвич свободной энергии (R390)**: F(T) = −T·ln Z
зажат между `E* − T·ln|V|` (энтропийный пол: Z ≤ n·e^{−E*/T})
и `E(v)` для любого v (вариационная верхняя: Z ≥ e^{−E(v)/T}
через single-член). Ядро границ simulated annealing:
F(0⁺) → E* с энтропийной ценой T·ln n — второй закон этой
системы: описание не дешевле энтропии данных. -/
theorem free_energy_sandwich {V : Type*} [Fintype V] [Nonempty V]
    (E : V → ℝ) (T : ℝ) (hT : 0 < T) (vstar : V)
    (hmin : ∀ v, E vstar ≤ E v) :
    E vstar - T * Real.log (Fintype.card V : ℝ)
      ≤ -T * Real.log (∑ v, Real.exp (-(E v)/T))
      ∧ -T * Real.log (∑ v, Real.exp (-(E v)/T)) ≤ E vstar := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- upper bound: F <= E*
  have hZge : Real.exp (-(E vstar)/T) ≤ Z :=
    Finset.single_le_sum (f := fun v => Real.exp (-(E v)/T))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vstar)
  have hlogge : Real.log (Real.exp (-(E vstar)/T)) ≤ Real.log Z :=
    Real.log_le_log (exp_pos _) hZge
  rw [Real.log_exp] at hlogge
  have hupper : -T * Real.log Z ≤ E vstar := by
    have hstep : -T * Real.log Z ≤ -T * (-(E vstar)/T) :=
      mul_le_mul_of_nonpos_left hlogge (by linarith)
    have hcancel : -T * (-(E vstar)/T) = E vstar := by
      field_simp
    rw [hcancel] at hstep
    exact hstep
  -- lower bound: F >= E* - T ln n
  have hterm : ∀ v, Real.exp (-(E v)/T) ≤ Real.exp (-(E vstar)/T) :=
    fun v => Real.exp_le_exp.mpr (by
      rw [div_le_div_iff₀ hT hT]
      nlinarith [hmin v])
  have hZle : Z ≤ (Fintype.card V : ℝ) * Real.exp (-(E vstar)/T) := by
    calc Z ≤ ∑ v : V, Real.exp (-(E vstar)/T) :=
          Finset.sum_le_sum (fun v _ => hterm v)
      _ = (Fintype.card V : ℝ) * Real.exp (-(E vstar)/T) := by
          rw [Finset.sum_const]
          norm_num
  have hlogle : Real.log Z ≤ Real.log ((Fintype.card V : ℝ)
      * Real.exp (-(E vstar)/T)) :=
    Real.log_le_log hZpos hZle
  rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero (α := V)) (exp_pos _).ne'] at hlogle
  rw [Real.log_exp] at hlogle
  have hlower : E vstar - T * Real.log (Fintype.card V : ℝ)
      ≤ -T * Real.log Z := by
    have hstep : -T * (Real.log (Fintype.card V : ℝ) + -(E vstar)/T)
        ≤ -T * Real.log Z :=
      mul_le_mul_of_nonpos_left hlogle (by linarith)
    have hcancel : -T * (Real.log (Fintype.card V : ℝ) + -(E vstar)/T)
        = E vstar - T * Real.log (Fintype.card V : ℝ) := by
      field_simp
      ring
    rw [hcancel] at hstep
    exact hstep
  exact ⟨hlower, hupper⟩

open Filter in
/-- **KL к минимизатору стремится к нулю (R391)**:
`−ln share(T_n) → 0` вдоль annealing-графика —
`KL(p_{T_n} ‖ δ_{vstar})` ( KL на точечную меру = −ln p(v*)
) экспоненциально гаснет: охлаждение = поток информации.
Мост Гиббс-вертикали к KL/Pinsker-конвейеру (R375–R377):
R387 + непрерывность log. -/
theorem gibbs_neg_log_share_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    Tendsto (fun n => -Real.log (Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) atTop (nhds 0) := by
  have hshare := gibbs_concentration_tendsto E δ hδ vstar hgap
  have hpos : ∀ n, (0:ℝ) < Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) := by
    intro n
    apply div_pos (exp_pos _)
    exact Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hlog : Tendsto (fun n => Real.log (Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) atTop (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hshare
  have hone : Real.log 1 = 0 := Real.log_one
  rw [hone] at hlog
  simpa using hlog.neg

/-- **Избыточная энергия Гиббс-состояния (R392)**:
Σ (E v − E*)·e^{−Ev/T} ≤ Δ·(Z − w_*) — ядро физического
смысла охлаждения (без нормализации): ожидаемая энергия
над основным состоянием ограничена зазором Δ на массу
конкурентов; вместе с R386 (масса конкурентов ≤
(n−1)e^{−δ/T}) — экспоненциальное гашение избыточной
энергии при охлаждении. -/
theorem gibbs_excess_energy_bound {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    ∑ v, (E v - E vstar) * Real.exp (-(E v)/T)
      ≤ Δ * (∑ v, Real.exp (-(E v)/T)
        - Real.exp (-(E vstar)/T)) := by
  -- LHS: star term zero
  have hsplit : ∑ v, (E v - E vstar) * Real.exp (-(E v)/T)
      = ∑ v ∈ Finset.univ.erase vstar,
          (E v - E vstar) * Real.exp (-(E v)/T) := by
    rw [← Finset.sum_erase_add _ (fun v =>
      (E v - E vstar) * Real.exp (-(E v)/T))
      (Finset.mem_univ vstar)]
    have hz : (E vstar - E vstar)
        * Real.exp (-(E vstar)/T) = 0 := by
      rw [sub_self, zero_mul]
    rw [hz, add_zero]
  -- RHS: univ = erase + star
  have hR : Δ * (∑ v, Real.exp (-(E v)/T)
        - Real.exp (-(E vstar)/T))
      = Δ * ∑ v ∈ Finset.univ.erase vstar,
          Real.exp (-(E v)/T) := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset V)
      (fun v => Real.exp (-(E v)/T)) (Finset.mem_univ vstar)
    conv_lhs => rw [← hsum]
    rw [add_sub_cancel_right]
  rw [hsplit, hR, Finset.mul_sum]
  refine Finset.sum_le_sum (f := fun v => (E v - E vstar) * Real.exp (-(E v)/T))
    (g := fun v => Δ * Real.exp (-(E v)/T)) (fun v hv => ?_)
  have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
  have h1 : (0:ℝ) ≤ Real.exp (-(E v)/T) := le_of_lt (exp_pos _)
  exact mul_le_mul_of_nonneg_right (hΔ v) h1

/-- **Капстоун охлаждения (R393)**: нормализованная
ожидаемая энергия Гиббс-состояния

  ⟨E⟩_T = (∑ E v·e^{−Ev/T})/Z ≤ E* + Δ·(n−1)·e^{−δ/T}

— композиция R392 (избыточная энергия ≤ зазор × масса
конкурентов) и R386 (масса конкурентов ≤ (n−1)e^{−δ/T}):
при охлаждении T → 0 ожидаемая энергия экспоненциально
прижимается к энергии основного состояния. Полный
физический сертификат T-контура. -/
theorem gibbs_expected_energy_bound {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (T : ℝ) (hT : 0 < T) (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    (∑ v, E v * Real.exp (-(E v)/T))
      / (∑ v, Real.exp (-(E v)/T))
      ≤ E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/T) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  set wstar : ℝ := Real.exp (-(E vstar)/T) with hw
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- R386: share = wstar/Z >= 1 - C e
  have hshare := gibbs_concentration E δ vstar hgap T hT
  -- R392: excess
  have hexcess := gibbs_excess_energy_bound E T hT vstar Δ hmin hΔ
  -- decompose A = sum E v w = E* Z + sum (Ev-E*) w
  have hA : ∑ v, E v * Real.exp (-(E v)/T)
      = E vstar * Z + ∑ v, (E v - E vstar)
          * Real.exp (-(E v)/T) := by
    have hexp : ∀ v : V, E v * Real.exp (-(E v)/T)
        = E vstar * Real.exp (-(E v)/T)
          + (E v - E vstar) * Real.exp (-(E v)/T) := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => (hexp v))]
    simp only [Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
  rw [hA, add_div]
  have hzcancel : E vstar * Z / Z = E vstar := by field_simp
  rw [hzcancel]
  -- chain: excess/Z <= Delta*(Z-wstar)/Z <= Delta*C*e
  have hstep1 : (∑ v, (E v - E vstar) * Real.exp (-(E v)/T)) / Z
      ≤ Δ * ((Z - wstar) / Z) := by
    have hassoc : Δ * ((Z - wstar) / Z) = Δ * (Z - wstar) / Z := by ring
    rw [hassoc, div_le_div_iff₀ hZpos hZpos, hZ, hw]
    nlinarith [hexcess, hZpos]
  -- share >= 1 - C e  =>  (Z - wstar)/Z <= C e
  have hstep2 : (Z - wstar) / Z
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/T) := by
    rw [div_le_iff₀ hZpos]
    have hshare' : 1 - (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/T) ≤ wstar / Z := hshare
    rw [le_div_iff₀ hZpos] at hshare'
    nlinarith [hZpos]
  -- combine
  have hΔ0 : (0:ℝ) ≤ Δ := by
    have := hΔ vstar
    simp only [sub_self] at this
    linarith
  have hstep3 : Δ * ((Z - wstar) / Z)
      ≤ Δ * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/T)) :=
    mul_le_mul_of_nonneg_left hstep2 hΔ0
  -- excess/Z <= Delta (Z-w)/Z: reassociate
  have hfin : (∑ v, (E v - E vstar) * Real.exp (-(E v)/T)) / Z
      ≤ Δ * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ/T)) := hstep1.trans hstep3
  linarith

open Filter in
/-- **Предел ожидаемой энергии (R394)**: вдоль
annealing-графика T_n = δ/(n+1) ожидаемая энергия
Гиббс-состояния стремится к энергии основного состояния:
⟨E⟩_{T_n} → E*. Двусторонний squeeze: нижняя — взвешенное
среднее не ниже минимума; верхняя — R393 с
e^{−δ/T_n} = e^{−(n+1)} → 0. Предельная форма физики
охлаждения: энергия системы прижимается к основному
состоянию по закону, а не по эвристике. -/
theorem gibbs_expected_energy_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun n => (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
      / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
      atTop (nhds (E vstar)) := by
  set Tn : ℕ → ℝ := fun n => δ/((n+1 : ℕ) : ℝ) with hTn
  have hTnpos : ∀ n, (0:ℝ) < Tn n := fun n =>
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  have hδT : ∀ n, -δ / Tn n = -((n+1 : ℕ) : ℝ) := by
    intro n
    rw [hTn]
    field_simp
  -- lower: <E> >= E*
  have hlower : ∀ n, E vstar ≤ (∑ v, E v * Real.exp (-(E v)/Tn n))
      / (∑ v, Real.exp (-(E v)/Tn n)) := by
    intro n
    have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/Tn n) :=
      Finset.sum_pos (fun v _ => exp_pos _)
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [le_div_iff₀ hZpos]
    calc E vstar * ∑ v, Real.exp (-(E v)/Tn n)
        = ∑ v, E vstar * Real.exp (-(E v)/Tn n) := Finset.mul_sum _ _ _
      _ ≤ ∑ v, E v * Real.exp (-(E v)/Tn n) :=
          Finset.sum_le_sum (fun v _ =>
            mul_le_mul_of_nonneg_right (hmin v) (le_of_lt (exp_pos _)))
  -- upper from R393
  have hupper : ∀ n, (∑ v, E v * Real.exp (-(E v)/Tn n))
      / (∑ v, Real.exp (-(E v)/Tn n))
      ≤ E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) := by
    intro n
    have hb := gibbs_expected_energy_bound E δ (Tn n) (hTnpos n)
      vstar Δ hmin hgap hΔ
    rw [hδT n] at hb
    exact hb
  -- squeeze: upper - E* -> 0
  have hexp0 : Tendsto (fun n => Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
      have hnat : Tendsto (fun n => -((n+1 : ℕ) : ℝ)) atTop atBot := by
        have hbase : Tendsto (fun n => -((n:ℕ):ℝ)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
        have hstep : Tendsto (fun n => -(1:ℝ) + -((n:ℕ):ℝ)) atTop atBot :=
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => -(1:ℝ)) atTop (nhds (-(1:ℝ)))).add_atBot hbase
        have hconv : (fun n => -(1:ℝ) + -((n:ℕ):ℝ))
            = fun n => -((n+1 : ℕ) : ℝ) := by
          funext n
          push_cast
          ring
        exact hconv ▸ hstep
      exact Real.tendsto_exp_atBot.comp hnat
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
        atTop (nhds (Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)))).mul h1
  -- combine via squeeze
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => E vstar) (f := fun n => (∑ v, E v * Real.exp (-(E v)/Tn n))
      / (∑ v, Real.exp (-(E v)/Tn n)))
    (h := fun n => E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-((n+1 : ℕ) : ℝ)))
    tendsto_const_nhds
    (show Tendsto (fun n => E vstar + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds (E vstar)) by
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => E vstar) atTop (nhds (E vstar))).add hexp0)
    (fun n => hlower n) (fun n => hupper n)

open Filter in
open Filter in
/-- **TV-идентификация (R395)**: (1/2)·∑|p_T(v) − δ_{v*}(v)|
= 1 − share(T) — TV-расстояние Гиббс-меры до точечной массы
минимизатора равно массе конкурентов. Вместе с R387:
TV(p_{T_n}, δ_{v*}) → 0 — метрическое замыкание Гиббс-
вертикали (охлаждение сходится в TV). -/
theorem gibbs_tv_eq {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T) (vstar : V) :
    (1/2) * ∑ v, |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
        - if v = vstar then (1:ℝ) else 0|
      = 1 - Real.exp (-(E vstar)/T)
        / (∑ v, Real.exp (-(E v)/T)) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- split the sum: star + competitors
  have hsplit : ∑ v, |Real.exp (-(E v)/T) / Z
        - if v = vstar then (1:ℝ) else 0|
      = ∑ v ∈ Finset.univ.erase vstar,
            Real.exp (-(E v)/T) / Z
        + |Real.exp (-(E vstar)/T) / Z - 1| := by
    have hsum2 : ∑ v ∈ Finset.univ.erase vstar,
        |Real.exp (-(E v)/T) / Z - if v = vstar then (1:ℝ) else 0|
        + |Real.exp (-(E vstar)/T) / Z
          - if vstar = vstar then (1:ℝ) else 0|
        = ∑ v, |Real.exp (-(E v)/T) / Z
          - if v = vstar then (1:ℝ) else 0| :=
      Finset.sum_erase_add (Finset.univ : Finset V)
        (fun v => |Real.exp (-(E v)/T) / Z
          - if v = vstar then (1:ℝ) else 0|)
        (Finset.mem_univ vstar)
    rw [← hsum2]
    have hstar : |Real.exp (-(E vstar)/T) / Z
        - if vstar = vstar then (1:ℝ) else 0|
        = |Real.exp (-(E vstar)/T) / Z - 1| := by
      rw [if_pos rfl]
    rw [hstar]
    have hcong : ∑ v ∈ Finset.univ.erase vstar,
        |Real.exp (-(E v)/T) / Z - if v = vstar then (1:ℝ) else 0|
        = ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v)/T) / Z := by
      refine Finset.sum_congr (f := fun v => |Real.exp (-(E v)/T) / Z
          - if v = vstar then (1:ℝ) else 0|)
        (g := fun v => Real.exp (-(E v)/T) / Z) rfl ?_
      intro v hv
      have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
      rw [if_neg hvne, sub_zero]
      exact abs_of_nonneg (div_nonneg
        (le_of_lt (exp_pos _)) (le_of_lt hZpos))
    rw [hcong]
  -- star abs = 1 - share
  have hsharele : Real.exp (-(E vstar)/T) / Z ≤ 1 := by
    have hge : Real.exp (-(E vstar)/T) ≤ Z :=
      Finset.single_le_sum (f := fun v => Real.exp (-(E v)/T))
        (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vstar)
    rw [div_le_one hZpos]
    exact hge
  rw [hsplit, abs_of_nonpos (by nlinarith [hsharele])]
  -- goal: 1/2 * ((share - 1) + Sum_erase w/Z) = 1 - share
  have hsumerase : ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v)/T)
      = Z - Real.exp (-(E vstar)/T) := by
    have hsum : ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v)/T)
        + Real.exp (-(E vstar)/T) = Z := by
      rw [hZ]
      exact Finset.sum_erase_add (Finset.univ : Finset V)
        (fun v => Real.exp (-(E v)/T)) (Finset.mem_univ vstar)
    linarith
  rw [← Finset.sum_div, hsumerase]
  field_simp
  ring

open Filter in
/-- TV-следствие (R395): вдоль annealing-графика TV → 0. -/
theorem gibbs_tv_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    Tendsto (fun n => (1/2) * ∑ v, |Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - if v = vstar then (1:ℝ) else 0|) atTop (nhds 0) := by
  have hshare := gibbs_concentration_tendsto E δ hδ vstar hgap
  have hkey : ∀ n, (1/2) * ∑ v, |Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - if v = vstar then (1:ℝ) else 0|
      = 1 - Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) :=
    fun n => gibbs_tv_eq E (δ/((n+1 : ℕ) : ℝ))
      (div_pos hδ (Nat.cast_pos.mpr n.succ_pos)) vstar
  rw [show (fun n => (1/2) * ∑ v, |Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - if v = vstar then (1:ℝ) else 0|)
      = fun n => (1:ℝ) - Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) from
    funext hkey]
  have hlim : Tendsto (fun n => (1:ℝ) - Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
      / ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) atTop (nhds 0) := by
    have hstep := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds (1:ℝ))).sub hshare
    have hzero : (1:ℝ) - 1 = 0 := by ring
    rw [hzero] at hstep
    exact hstep
  exact hlim
/-- **TV-треугольник (R396)**: TV(p_T, p_S) ≤ (1 − share_T)
+ (1 − share_S) — взаимная сходимость: обе Гиббс-меры
прижимаются к одной точечной массе, поэтому прижимаются
друг к другу (Коши-свойство охлаждения). Поточечный
треугольник через δ_{v*} (abs_add_le) + tv-идентификация
R395. -/
theorem gibbs_tv_mutual {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (T S : ℝ) (hT : 0 < T) (hS : 0 < S)
    (vstar : V) :
    (1/2) * ∑ v, |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
        - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))|
      ≤ (1 - Real.exp (-(E vstar)/T) / (∑ v, Real.exp (-(E v)/T)))
        + (1 - Real.exp (-(E vstar)/S) / (∑ v, Real.exp (-(E v)/S))) := by
  -- pointwise triangle through the point mass
  have htri : ∀ v : V,
      |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
          - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))|
      ≤ |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
          - if v = vstar then (1:ℝ) else 0|
        + |(if v = vstar then (1:ℝ) else 0)
          - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))| := by
    intro v
    have hsplit : Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
        - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))
        = (Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
            - if v = vstar then (1:ℝ) else 0)
          + ((if v = vstar then (1:ℝ) else 0)
            - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  -- sum up
  have hsum : (1/2) * ∑ v, |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
        - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))|
      ≤ (1/2) * ∑ v, (|Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
          - if v = vstar then (1:ℝ) else 0|
        + |(if v = vstar then (1:ℝ) else 0)
          - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))|) :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun v _ => htri v)) (by positivity)
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib]
  -- identify via gibbs_tv_eq (second with if-flip)
  have heq1 := gibbs_tv_eq E T hT vstar
  have hflip : ∀ v : V,
      |(if v = vstar then (1:ℝ) else 0)
        - Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))|
      = |Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))
        - if v = vstar then (1:ℝ) else 0| :=
    fun v => abs_sub_comm _ _
  rw [Finset.sum_congr rfl (fun v _ => hflip v)]
  rw [← heq1]
  have heq2 := gibbs_tv_eq E S hS vstar
  rw [← heq2]
  have hA : (0:ℝ) ≤ ∑ v, |Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
      - if v = vstar then (1:ℝ) else 0| :=
    Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hB : (0:ℝ) ≤ ∑ v, |Real.exp (-(E v)/S) / (∑ v, Real.exp (-(E v)/S))
      - if v = vstar then (1:ℝ) else 0| :=
    Finset.sum_nonneg (fun v _ => abs_nonneg _)
  linarith

/-- **Количественный Коши (R397)**: вдоль annealing-графика
TV(p_n, p_m) ≤ C·(e^{−(n+1)} + e^{−(m+1)}) — явная
экспоненциальная скорость взаимного сближения Гиббс-мер
(R396 × R386): последовательность охлаждения Коши со
скоростью e^{−n}. -/
theorem gibbs_tv_mutual_bound {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (vstar : V) (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (n m : ℕ) :
    (1/2) * ∑ v, |Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - Real.exp (-(E v)/(δ/((m+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((m+1 : ℕ) : ℝ))))|
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * (Real.exp (-((n+1 : ℕ) : ℝ))
          + Real.exp (-((m+1 : ℕ) : ℝ))) := by
  have hTn : (0:ℝ) < δ/((n+1 : ℕ) : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  have hTm : (0:ℝ) < δ/((m+1 : ℕ) : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr m.succ_pos)
  have hδTn : -δ / (δ/((n+1 : ℕ) : ℝ)) = -((n+1 : ℕ) : ℝ) := by
    rw []
    field_simp
  have hδTm : -δ / (δ/((m+1 : ℕ) : ℝ)) = -((m+1 : ℕ) : ℝ) := by
    field_simp
  -- triangle
  have htri := gibbs_tv_mutual E _ _ hTn hTm vstar
  -- share bounds from R386
  have hb1 := gibbs_concentration E δ vstar hgap _ hTn
  have hb2 := gibbs_concentration E δ vstar hgap _ hTm
  rw [hδTn] at hb1
  rw [hδTm] at hb2
  -- combine
  have hcomb : (1 - Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
      + (1 - Real.exp (-(E vstar)/(δ/((m+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((m+1 : ℕ) : ℝ)))))
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * (Real.exp (-((n+1 : ℕ) : ℝ))
          + Real.exp (-((m+1 : ℕ) : ℝ))) := by
    have h1 : Real.exp (-(E vstar)/(δ/((n+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) ≥ 1
        - (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)) := hb1
    have h2 : Real.exp (-(E vstar)/(δ/((m+1 : ℕ) : ℝ)))
        / (∑ v, Real.exp (-(E v)/(δ/((m+1 : ℕ) : ℝ)))) ≥ 1
        - (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((m+1 : ℕ) : ℝ)) := hb2
    have hC : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hexp1 : (0:ℝ) ≤ Real.exp (-((n+1 : ℕ) : ℝ)) :=
      le_of_lt (exp_pos _)
    have hexp2 : (0:ℝ) ≤ Real.exp (-((m+1 : ℕ) : ℝ)) :=
      le_of_lt (exp_pos _)
    nlinarith [h1, h2, hC, hexp1, hexp2,
      mul_nonneg hC hexp1, mul_nonneg hC hexp2,
      sq_nonneg (((Finset.univ.erase vstar).card : ℕ) : ℝ)]
  exact htri.trans hcomb

/-- **Острая нижняя граница свободной энергии (R398)**:
F(T) = −T·ln Z ≥ E* − T·ln(1 + (n−1)·e^{−δ/T}) — при
малых T зазор δ улучшает энтропийный пол T·ln|R390| до
T·ln(1+(n−1)e^{−δ/T}) ≈ T(n−1)e^{−δ/T} — экспоненциально
малая поправка. Маршрут: Z ≤ w*·(1+C·e^{−δ/T}) (per-v
экспоненциальная оценка веса конкурентов) + log-монотонность. -/
theorem free_energy_sharp_lower {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (T : ℝ) (hT : 0 < T) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    E vstar - T * Real.log (1
        + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-δ/T))
      ≤ -T * Real.log (∑ v, Real.exp (-(E v)/T)) := by
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  set wstar : ℝ := Real.exp (-(E vstar)/T) with hw
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- per-competitor weight bound
  have hterm : ∀ v ∈ Finset.univ.erase vstar,
      Real.exp (-(E v)/T) ≤ Real.exp (-δ/T) * wstar := by
    intro v hv
    have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
    have hE : E vstar + δ ≤ E v := hgap v hvne
    have hmul : (E vstar + δ) * T ≤ E v * T :=
      mul_le_mul_of_nonneg_right hE (le_of_lt hT)
    have hkey : -(E v)/T ≤ -(E vstar + δ)/T := by
      rw [div_le_div_iff₀ hT hT]
      nlinarith [hmul]
    have hexp : Real.exp (-(E v)/T)
        ≤ Real.exp (-(E vstar + δ)/T) :=
      Real.exp_le_exp.mpr hkey
    have hsplit2 : Real.exp (-(E vstar + δ)/T)
        = Real.exp (-δ/T) * wstar := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [← hsplit2]
    exact hexp
  -- sum: Z <= wstar * (1 + C e)
  have hsum : Z ≤ wstar * (1 + C * Real.exp (-δ/T)) := by
    have hsumE : ∑ v ∈ Finset.univ.erase vstar,
        Real.exp (-(E v)/T) ≤ C * Real.exp (-δ/T) * wstar := by
      calc ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v)/T)
          ≤ ∑ v ∈ Finset.univ.erase vstar,
              Real.exp (-δ/T) * wstar :=
            Finset.sum_le_sum hterm
        _ = (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * (Real.exp (-δ/T) * wstar) := by
            rw [Finset.sum_const]
            norm_num
        _ = C * Real.exp (-δ/T) * wstar := by
            rw [hC]
            ring
    rw [hZ, hw]
    calc ∑ v, Real.exp (-(E v)/T)
        = ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v)/T)
          + Real.exp (-(E vstar)/T) := by
          refine (Finset.sum_erase_add (Finset.univ : Finset V)
            (fun v => Real.exp (-(E v)/T)) (Finset.mem_univ vstar)).symm
      _ ≤ C * Real.exp (-δ/T) * wstar + Real.exp (-(E vstar)/T) :=
          add_le_add_left hsumE _
      _ = Real.exp (-(E vstar)/T) * (1 + C * Real.exp (-δ/T)) := by ring
  -- logs
  have hwpos : (0:ℝ) < wstar := exp_pos _
  have hfactpos : (0:ℝ) < 1 + C * Real.exp (-δ/T) := by
    have : (0:ℝ) ≤ C * Real.exp (-δ/T) :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (exp_pos _))
    linarith
  have hlog : Real.log Z ≤ Real.log wstar
      + Real.log (1 + C * Real.exp (-δ/T)) := by
    have h1 : Real.log Z
        ≤ Real.log (wstar * (1 + C * Real.exp (-δ/T))) :=
      Real.log_le_log hZpos hsum
    rw [Real.log_mul hwpos.ne' hfactpos.ne'] at h1
    exact h1
  -- final scaling by -T
  have hstep : -T * (Real.log wstar
      + Real.log (1 + C * Real.exp (-δ/T)))
      ≤ -T * Real.log Z :=
    mul_le_mul_of_nonpos_left hlog (by linarith)
  have hlogw : Real.log wstar = -(E vstar)/T := by
    rw [hw, Real.log_exp]
  rw [hlogw] at hstep
  have hcancel : -T * (-(E vstar)/T
      + Real.log (1 + C * Real.exp (-δ/T)))
      = E vstar - T * Real.log (1 + C * Real.exp (-δ/T)) := by
    field_simp
    ring
  rw [hcancel] at hstep
  exact hstep

open Filter in
/-- **Предел свободной энергии (R399)**: вдоль
annealing-графика F(T_n) = −T_n·ln Z_n → E* — свободная
энергия прижимается к энергии основного состояния.
Двусторонний squeeze: верхняя R390 (F ≤ E*), нижняя R398
(F ≥ E* − T_n·ln(1+Ce^{−(n+1)})) с ошибкой ≤
δ·C·e^{−(n+1)}/(n+1) → 0 (ln(1+x) ≤ x через
`Real.add_one_le_exp`). Nernst-стиль: при T → 0 свободная
энергия вырождается в основное состояние. -/
theorem free_energy_tendsto {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hmin : ∀ v, E vstar ≤ E v) :
    Tendsto (fun n => -(δ/((n+1 : ℕ) : ℝ))
        * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
      atTop (nhds (E vstar)) := by
  have hTnpos : ∀ n, (0:ℝ) < δ/((n+1 : ℕ) : ℝ) := fun n =>
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  have hδT : ∀ n, -δ / (δ/((n+1 : ℕ) : ℝ)) = -((n+1 : ℕ) : ℝ) := by
    intro n
    field_simp
  -- upper: F <= E* (R390 upper part with vstar)
  have hupper : ∀ n, -(δ/((n+1 : ℕ) : ℝ))
        * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
      ≤ E vstar := by
    intro n
    have hR390 := (free_energy_sandwich E (δ/((n+1 : ℕ) : ℝ))
      (hTnpos n) vstar hmin).2
    exact hR390
  -- lower from R398
  have hlower0 : ∀ n, E vstar - (δ/((n+1 : ℕ) : ℝ))
        * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)))
      ≤ -(δ/((n+1 : ℕ) : ℝ))
        * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) := by
    intro n
    have hR := free_energy_sharp_lower E δ (δ/((n+1 : ℕ) : ℝ))
      (hTnpos n) vstar hgap
    rw [hδT n] at hR
    exact hR
  -- error bound -> 0: T_n * ln(1+Ce) <= T_n * C * e <= delta*C/(n+1)
  have hlnle : ∀ n, Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)))
      ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) := by
    intro n
    have hx : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (exp_pos _))
    have h1 : 1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))
        ≤ Real.exp ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))) := by
      rw [add_comm]
      exact Real.add_one_le_exp _
    have h2 : Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)))
        ≤ Real.log (Real.exp ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)))) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_exp] at h2
    exact h2
  -- squeeze delta*C/(n+1) -> 0
  have hkey : Tendsto (fun n => (δ/((n+1 : ℕ) : ℝ))
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hle : ∀ n, (0:ℝ) ≤ (δ/((n+1 : ℕ) : ℝ))
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) := by
      intro n
      have hcast : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hcard : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      have hexpm : (0:ℝ) ≤ Real.exp (-((n+1 : ℕ) : ℝ)) :=
        le_of_lt (exp_pos _)
      have hd0 : (0:ℝ) ≤ δ/((n+1 : ℕ) : ℝ) :=
        div_nonneg (le_of_lt hδ) hcast
      exact mul_nonneg (mul_nonneg hd0 hcard) hexpm
    have hb : ∀ n, (δ/((n+1 : ℕ) : ℝ))
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))
      ≤ δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        / ((n+1 : ℕ) : ℝ) := by
      intro n
      have hexp1 : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ 1 := by
        have : (-((n+1 : ℕ) : ℝ)) ≤ 0 := by
          have hcast : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have h1 : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ Real.exp (0:ℝ) :=
          Real.exp_le_exp.mpr this
        rw [Real.exp_zero] at h1
        exact h1
      calc (δ/((n+1 : ℕ) : ℝ))
          * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))
          ≤ (δ/((n+1 : ℕ) : ℝ))
            * (((Finset.univ.erase vstar).card : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            / ((n+1 : ℕ) : ℝ) := by
            rw [mul_one]
            field_simp
    have hinv : Tendsto (fun n => δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        / ((n+1 : ℕ) : ℝ)) atTop (nhds 0) := by
      have hnat2 : Tendsto (fun n => ((n+1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_atTop_mono (fun n => by
          have hcast : ((n:ℕ):ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
            push_cast
            linarith
          exact le_trans hcast (le_refl _))
          tendsto_natCast_atTop_atTop
      have hdiv := tendsto_inv_atTop_zero.comp hnat2
      have hmul : Tendsto (fun n => (δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          * (((n+1 : ℕ) : ℝ))⁻¹) atTop (nhds (δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ) * 0)) :=
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          atTop (nhds (δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)))).mul hdiv
      have hform : (fun n => (δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          * (((n+1 : ℕ) : ℝ))⁻¹)
          = fun n => δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            / ((n+1 : ℕ) : ℝ) := by
        funext n
        rw [div_eq_inv_mul]
        ring
      rw [hform] at hmul
      simpa using hmul
    exact squeeze_zero hle hb hinv
  -- err -> 0
  have herr : Tendsto (fun n => (δ/((n+1 : ℕ) : ℝ))
      * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)))) atTop (nhds 0) := by
    have hge : ∀ n, (0:ℝ) ≤ (δ/((n+1 : ℕ) : ℝ))
        * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))) := by
      intro n
      have hln : (0:ℝ) ≤ Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))) := by
        have hcard : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have hexpm : (0:ℝ) ≤ Real.exp (-((n+1 : ℕ) : ℝ)) :=
          le_of_lt (exp_pos _)
        have hprod : (0:ℝ) ≤ (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)) :=
          mul_nonneg hcard hexpm
        apply Real.log_nonneg
        linarith
      exact mul_nonneg (div_nonneg (le_of_lt hδ)
        (Nat.cast_nonneg _)) hln
    have hle : ∀ n, (δ/((n+1 : ℕ) : ℝ))
        * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)))
      ≤ (δ/((n+1 : ℕ) : ℝ))
        * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))) :=
      fun n => by
        have h1 : (δ/((n+1 : ℕ) : ℝ))
            * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
              * Real.exp (-((n+1 : ℕ) : ℝ)))
            ≤ (δ/((n+1 : ℕ) : ℝ))
            * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
              * Real.exp (-((n+1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hlnle n)
            (div_nonneg (le_of_lt hδ)
              (Nat.cast_nonneg (n+1)))
        have h2 : ((δ/((n+1 : ℕ) : ℝ))
            * ((((Finset.univ.erase vstar).card : ℕ) : ℝ)
              * Real.exp (-((n+1 : ℕ) : ℝ))))
            = (δ/((n+1 : ℕ) : ℝ))
            * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
            * Real.exp (-((n+1 : ℕ) : ℝ)) := by ring
        linarith
    exact squeeze_zero hge hle (by simpa only [mul_assoc] using hkey)
  -- final squeeze
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => E vstar - (δ/((n+1 : ℕ) : ℝ))
      * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))))
    (f := fun n => -(δ/((n+1 : ℕ) : ℝ))
        * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
    (h := fun n => E vstar)
    (show Tendsto (fun n => E vstar - (δ/((n+1 : ℕ) : ℝ))
        * Real.log (1 + (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ)))) atTop (nhds (E vstar)) by
      have hstep := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => E vstar) atTop (nhds (E vstar))).sub herr
      have hz : (E vstar : ℝ) - 0 = E vstar := by ring
      simpa [hz] using hstep)
    tendsto_const_nhds
    (fun n => hlower0 n) (fun n => hupper n)

open Filter in
/-- **Нернст для Гиббс-ансамбля (R400)**: энтропия
S_n = (⟨E⟩_{T_n} − F(T_n))/T_n → 0 — остаточная энтропия
исчезает при охлаждении. Двусторонний squeeze из R393/R394
(⟨E⟩-эксцесс ≤ ΔCe^{−(n+1)}) и R398 (F-дефект ≤
T_n·ln(1+Ce^{−(n+1)})) с полиномиально-экспоненциальной
оценкой (n+1)e^{−(n+1)} ≤ 2e^{−(n+1)/2} (из e^x ≥ 1+x,
`Real.add_one_le_exp`). Третий закон термодинамики HAGI:
при T → 0 система вырождается в основное состояние БЕЗ
остаточной энтропии. -/
theorem gibbs_entropy_tendsto_zero {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun n => ( (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - (-(δ/((n+1 : ℕ) : ℝ))
          * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) )
      / (δ/((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
  have hTnpos : ∀ n, (0:ℝ) < δ/((n+1 : ℕ) : ℝ) := fun n =>
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  set C : ℝ := (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hC
  -- 0 <= <E> - E*  (weighted mean >= min)
  have hlower : ∀ n, (0:ℝ) ≤ (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) - E vstar := by
    intro n
    have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) :=
      Finset.sum_pos (fun v _ => exp_pos _)
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [sub_nonneg, le_div_iff₀ hZpos]
    calc E vstar * ∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        = ∑ v, E vstar * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum (fun v _ =>
            mul_le_mul_of_nonneg_right (hmin v) (le_of_lt (exp_pos _)))
  -- <E> - E* <= Delta * C * e^{-(n+1)}  (R393)
  have hδT : ∀ n, -δ / (δ/((n+1 : ℕ) : ℝ)) = -((n+1 : ℕ) : ℝ) := by
    intro n
    field_simp
  have hupperE : ∀ n, (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) - E vstar
      ≤ Δ * C * Real.exp (-((n+1 : ℕ) : ℝ)) := by
    intro n
    have hb := gibbs_expected_energy_bound E δ (δ/((n+1 : ℕ) : ℝ))
      (hTnpos n) vstar Δ hmin hgap hΔ
    rw [hδT n] at hb
    have hCeq : Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))
        = Δ * C * Real.exp (-((n+1 : ℕ) : ℝ)) := by
      rw [hC]
    rw [hCeq] at hb
    linarith
  -- 0 <= E* - F <= T * ln(1 + C e^{-(n+1)})  (R398)
  have hupperF : ∀ n, (0:ℝ) ≤ E vstar
        - (-(δ/((n+1 : ℕ) : ℝ))
          * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
      ∧ E vstar
        - (-(δ/((n+1 : ℕ) : ℝ))
          * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))))
      ≤ (δ/((n+1 : ℕ) : ℝ))
        * Real.log (1 + C * Real.exp (-((n+1 : ℕ) : ℝ))) := by
    intro n
    have hlo := free_energy_sharp_lower E δ (δ/((n+1 : ℕ) : ℝ))
      (hTnpos n) vstar hgap
    rw [hδT n, ← hC] at hlo
    have hhi := (free_energy_sandwich E (δ/((n+1 : ℕ) : ℝ))
      (hTnpos n) vstar hmin).2
    exact ⟨by linarith, by linarith⟩
  -- bound the ratio
  have hcomb : ∀ n, (0:ℝ) ≤ ( (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - (-(δ/((n+1 : ℕ) : ℝ))
          * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) )
      / (δ/((n+1 : ℕ) : ℝ))
      ∧ ( (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
        - (-(δ/((n+1 : ℕ) : ℝ))
          * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) )
      / (δ/((n+1 : ℕ) : ℝ))
      ≤ Δ * C * Real.exp (-((n+1 : ℕ) : ℝ)) / (δ/((n+1 : ℕ) : ℝ))
        + Real.log (1 + C * Real.exp (-((n+1 : ℕ) : ℝ))) := by
    intro n
    have h1 := hlower n
    have h2 := hupperE n
    have h3 := hupperF n
    have hT := hTnpos n
    constructor
    · apply div_nonneg
      · linarith [h3.1, h1]
      · exact le_of_lt hT
    · rw [div_le_iff₀ hT]
      have hXeq : ( (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
          / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
          - (-(δ/((n+1 : ℕ) : ℝ))
            * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) )
          = ( (∑ v, E v * Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))
          / (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))) - E vstar )
          + (E vstar - (-(δ/((n+1 : ℕ) : ℝ))
            * Real.log (∑ v, Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ))))) ) := by ring
      rw [hXeq]
      have hT2 := hTnpos n
      have hA := mul_le_mul_of_nonneg_right h2 (le_of_lt hT)
      have hB := mul_le_mul_of_nonneg_right h3.2 (le_of_lt hT)
      have hR : (Δ * C * Real.exp (-((n+1 : ℕ) : ℝ))
          / (δ/((n+1 : ℕ) : ℝ))
          + Real.log (1 + C * Real.exp (-((n+1 : ℕ) : ℝ)))) * (δ/((n+1 : ℕ) : ℝ))
          = Δ * C * Real.exp (-((n+1 : ℕ) : ℝ))
          + (δ/((n+1 : ℕ) : ℝ)) * Real.log (1 + C * Real.exp (-((n+1 : ℕ) : ℝ))) := by
        rw [add_mul, div_mul_cancel₀ _ hT.ne']
        ring
      rw [hR]
      nlinarith [hA, hB, hT2]

  -- e^{-(n+1)} * (n+1) -> 0 via e^{m} >= 1 + m
  have hnat2 : Tendsto (fun n => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have hcast : ((n:ℕ):ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact hcast) tendsto_natCast_atTop_atTop
  have hexnat : Tendsto (fun n => Real.exp (-((n+1 : ℕ) : ℝ)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnat2)
  have hexpmul : Tendsto (fun n => ((n+1 : ℕ) : ℝ)
      * Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hbound : ∀ n, ((n+1 : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ))
      ≤ 2 * Real.exp (-((n+1 : ℕ) : ℝ) / 2) := by
      intro n
      have hcast : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : ((n+1 : ℕ) : ℝ) / 2 + 1
          ≤ Real.exp (((n+1 : ℕ) : ℝ) / 2) := by
        have := Real.add_one_le_exp (((n+1 : ℕ) : ℝ) / 2)
        linarith [this]
      -- (n+1) <= 2 e^{m/2} - 2
      have h2 : ((n+1 : ℕ) : ℝ) ≤ 2 * Real.exp (((n+1 : ℕ) : ℝ) / 2) - 2 := by linarith
      have hexp : (0:ℝ) < Real.exp (-((n+1 : ℕ) : ℝ)) := exp_pos _
      have hhalf : (0:ℝ) < Real.exp (((n+1 : ℕ) : ℝ) / 2) := exp_pos _
      have hkey : ((n+1 : ℕ) : ℝ) * Real.exp (-((n+1 : ℕ) : ℝ))
          ≤ 2 * Real.exp (((n+1 : ℕ) : ℝ) / 2) * Real.exp (-((n+1 : ℕ) : ℝ)) := by
        nlinarith [h2, hhalf]
      have hinner : Real.exp (((n+1 : ℕ) : ℝ) / 2)
          * Real.exp (-((n+1 : ℕ) : ℝ))
          = Real.exp (-((n+1 : ℕ) : ℝ) / 2) := by
        rw [← Real.exp_add]
        congr 1
        field_simp
        ring
      have hregroup : 2 * Real.exp (((n+1 : ℕ) : ℝ) / 2)
          * Real.exp (-((n+1 : ℕ) : ℝ))
          = 2 * (Real.exp (((n+1 : ℕ) : ℝ) / 2)
            * Real.exp (-((n+1 : ℕ) : ℝ))) := by ring
      rw [hregroup, hinner] at hkey
      exact hkey
    have hge : ∀ n, (0:ℝ) ≤ ((n+1 : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) := by
      intro n
      exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (exp_pos _))
    have hhalf : Tendsto (fun n => 2 * Real.exp (-((n+1 : ℕ) : ℝ) / 2))
        atTop (nhds 0) := by
      have hpre : Tendsto (fun n => (1/2:ℝ) * (-(((n+1 : ℕ) : ℝ)))) atTop atBot :=
        Tendsto.const_mul_atBot (by norm_num : (0:ℝ) < 1/2)
          (tendsto_neg_atTop_atBot.comp hnat2)
      have hconv : (fun n => (1/2:ℝ) * (-(((n+1 : ℕ) : ℝ))))
          = fun n => -(((n+1 : ℕ) : ℝ) / 2) := by
        funext n
        field_simp
      rw [hconv] at hpre
      have hexp2 := Real.tendsto_exp_atBot.comp hpre
      have hfin := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2:ℝ)) atTop (nhds (2:ℝ))).mul hexp2
      simp only [Function.comp_apply, mul_zero] at hfin
      convert hfin using 3
      congr 1
      ring
    exact squeeze_zero hge hbound hhalf
  -- final: ratio -> 0 by squeeze with hcomb parts
  -- part 1: Delta*C*e^{-(n+1)} / T_n = Delta*C/δ * (n+1) e^{-(n+1)} -> 0
  have hpart1 : Tendsto (fun n => Δ * C * Real.exp (-((n+1 : ℕ) : ℝ))
      / (δ/((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hform : (fun n => Δ * C * Real.exp (-((n+1 : ℕ) : ℝ))
        / (δ/((n+1 : ℕ) : ℝ)))
        = fun n => (Δ * C / δ) * (((n+1 : ℕ) : ℝ)
          * Real.exp (-((n+1 : ℕ) : ℝ))) := by
      funext n
      field_simp
    rw [hform]
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Δ * C / δ) atTop (nhds (Δ * C / δ))).mul hexpmul
  -- part 2: ln(1 + C e^{-(n+1)}) -> 0
  have hpart2 : Tendsto (fun n => Real.log (1 + C
      * Real.exp (-((n+1 : ℕ) : ℝ)))) atTop (nhds 0) := by
    have hcard : (0:ℝ) ≤ C := Nat.cast_nonneg _
    have hge : ∀ n, (0:ℝ) ≤ Real.log (1 + C
        * Real.exp (-((n+1 : ℕ) : ℝ))) := by
      intro n
      apply Real.log_nonneg
      have hcard : (0:ℝ) ≤ C := Nat.cast_nonneg _
      have hexpm : (0:ℝ) ≤ Real.exp (-((n+1 : ℕ) : ℝ)) :=
        le_of_lt (exp_pos _)
      exact le_add_of_nonneg_right (mul_nonneg hcard hexpm)
    have hle : ∀ n, Real.log (1 + C
        * Real.exp (-((n+1 : ℕ) : ℝ)))
      ≤ C * Real.exp (-((n+1 : ℕ) : ℝ)) := by
      intro n
      have h1 : 1 + C * Real.exp (-((n+1 : ℕ) : ℝ))
          ≤ Real.exp (C * Real.exp (-((n+1 : ℕ) : ℝ))) := by
        rw [add_comm]
        exact Real.add_one_le_exp _
      have hpos : (0:ℝ) < 1 + C * Real.exp (-((n+1 : ℕ) : ℝ)) := by
        have hcard : (0:ℝ) ≤ C := Nat.cast_nonneg _
        have hexpm : (0:ℝ) ≤ Real.exp (-((n+1 : ℕ) : ℝ)) :=
          le_of_lt (exp_pos _)
        have hnn : (0:ℝ) ≤ C * Real.exp (-((n+1 : ℕ) : ℝ)) :=
          mul_nonneg hcard hexpm
        linarith
      have h2 : Real.log (1 + C * Real.exp (-((n+1 : ℕ) : ℝ)))
          ≤ Real.log (Real.exp (C * Real.exp (-((n+1 : ℕ) : ℝ)))) :=
        Real.log_le_log hpos h1
      rwa [Real.log_exp] at h2
    have hexpz : Tendsto (fun n => C * Real.exp (-((n+1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => C) atTop (nhds C)).mul hexnat
    exact squeeze_zero hge hle hexpz
  exact squeeze_zero (fun n => (hcomb n).1)
    (fun n => (hcomb n).2) (by simpa using hpart1.add hpart2)


/-- **Апостериорное отношение (R401)**: для конкурента с
δ-зазором p_v ≤ e^{−δ/T}·p_{v*} — likelihood-ratio
сертификат: относительный вес проигравшего экспоненциально
гасится температурой. Основа admission-гейта T-контура
(какой вес может претендовать на место в корне). -/
theorem gibbs_posterior_ratio {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (T : ℝ) (hT : 0 < T) (vstar v : V)
    (hgap : E vstar + δ ≤ E v) :
    Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
      ≤ Real.exp (-δ/T)
        * (Real.exp (-(E vstar)/T)
          / (∑ v, Real.exp (-(E v)/T))) := by
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- numerator comparison
  have hkey : -(E v)/T ≤ -(E vstar + δ)/T := by
    have hmul : (E vstar + δ) * T ≤ E v * T :=
      mul_le_mul_of_nonneg_right hgap (le_of_lt hT)
    rw [div_le_div_iff₀ hT hT]
    nlinarith [hmul]
  have hexp : Real.exp (-(E v)/T)
      ≤ Real.exp (-(E vstar + δ)/T) :=
    Real.exp_le_exp.mpr hkey
  have hsplit : Real.exp (-(E vstar + δ)/T)
      = Real.exp (-δ/T) * Real.exp (-(E vstar)/T) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit] at hexp
  -- scale by 1/Z
  calc Real.exp (-(E v)/T) / (∑ v, Real.exp (-(E v)/T))
      = (1 / (∑ v, Real.exp (-(E v)/T))) * Real.exp (-(E v)/T) := by ring
    _ ≤ (1 / (∑ v, Real.exp (-(E v)/T)))
        * (Real.exp (-δ/T) * Real.exp (-(E vstar)/T)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (-δ/T)
        * (Real.exp (-(E vstar)/T)
          / (∑ v, Real.exp (-(E v)/T))) := by ring

open Finset in
/-- **Второй закон: неотрицательность
энтропии Гиббса (R418)**: S(p_T) =
∑ w·(−ln w) ≥ 0 — почленно: w ≤ 1 (как
вес вероятностной меры, single_le_sum) ⟹
−ln w ≥ 0 ⟹ каждый член ≥ 0. Вместе с R400
(Нернст S→0) даёт 0 ≤ S_n → 0 — полный
третий закон в обеих сторонах. -/
theorem gibbs_entropy_nonneg {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    (0:ℝ) ≤ ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      * (-Real.log (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set w : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hw
  have hwpos : ∀ v, 0 < w v := fun v => div_pos (exp_pos _) hZpos
  have hw1 : ∑ v, w v = 1 := by
    rw [hw]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  -- each w v <= 1 (probability)
  have hwle : ∀ v, w v ≤ 1 := by
    intro v
    have := single_le_sum (f := w) (fun x _ => le_of_lt (hwpos x))
      (Finset.mem_univ v)
    rw [hw1] at this
    exact this
  -- termwise nonneg
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (le_of_lt (hwpos v))
  apply neg_nonneg.mpr
  exact Real.log_nonpos (le_of_lt (hwpos v)) (hwle v)

open Finset in
/-- **Нижняя грань энергии (R420)**: E* ≤ ⟨E⟩_T
почленно (E* · w_v ≤ E_v · w_v). Вместе с R393
полный сэндвич:
E* ≤ ⟨E⟩_T ≤ E* + Δ·(n−1)·e^{−δ/T} —
энергия Гиббса зажата между
основным состоянием и хвостом. -/
theorem gibbs_expected_energy_lower {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vstar : V) (hmin : ∀ v, E vstar ≤ E v) :
    E vstar ≤ (∑ v, E v * Real.exp (-(E v)/T))
        / (∑ v, Real.exp (-(E v)/T)) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- E* = (sum E* * e) / Z  <=  (sum E * e) / Z
  have hnum : (∑ v, E vstar * Real.exp (-(E v)/T))
      ≤ ∑ v, E v * Real.exp (-(E v)/T) := by
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_right (hmin v) (le_of_lt (exp_pos _))
  -- rewrite numerator: sum E* * e = E* * Z
  have hsplit : ∑ v, E vstar * Real.exp (-(E v)/T)
      = E vstar * Z := by
    rw [hZ, Finset.mul_sum]
  rw [hsplit] at hnum
  rwa [le_div_iff₀ hZpos]

open Finset in
/-- **Верхняя грань свободной энергии (R421)**:
F(T) = −T·ln Z ≤ E* поточено (Z ≥ w*,
логарифм монотонен, −T < 0). Вместе с R398
полный сэндвич свободной энергии:
E* − T·ln(1+(n−1)e^{−δ/T}) ≤ F(T) ≤ E* —
сжимается к E* при охлаждении. -/
theorem free_energy_upper {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (vstar : V) :
    -T * Real.log (∑ v, Real.exp (-(E v)/T)) ≤ E vstar := by
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  -- Z >= w* : single_le_sum
  have hw : Real.exp (-(E vstar)/T)
      ≤ ∑ v, Real.exp (-(E v)/T) :=
    single_le_sum (f := fun v => Real.exp (-(E v)/T))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vstar)
  -- log mono
  have hlog : Real.log (Real.exp (-(E vstar)/T))
      ≤ Real.log (∑ v, Real.exp (-(E v)/T)) :=
    Real.log_le_log (exp_pos _) hw
  rw [Real.log_exp] at hlog
  -- -T * log Z <= -T * (-(E vstar)/T) = E vstar
  have hmul : -T * Real.log (∑ v, Real.exp (-(E v)/T))
      ≤ -T * (-(E vstar)/T) :=
    mul_le_mul_of_nonpos_left hlog (by linarith : (-T:ℝ) ≤ 0)
  have : -T * (-(E vstar)/T) = E vstar := by
    field_simp
  linarith

open Finset in
/-- **Разложение перекрёстной энтропии (R422)**:
∑ w·ln(w·n) = ∑ w·ln w + ln n — тождество
энтропия/KL: KL(pḟ‖u) =
−S + ln n. Вместе с R418 (S ≥ 0) даёт
KL(pḟ‖u) ≤ ln n; мост к Пинскеру на
Гиббс-парах: охлаждение убивает энтропию
→ KL к равномерному растёт до ln n (порядок
максимальной энтропии обращается). -/
theorem gibbs_kl_uniform_split {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      * Real.log ((Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ))
    = ∑ v, (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v, Real.exp (-(E v)/T))
      + Real.log (Fintype.card V : ℝ) := by
  set Z : ℝ := ∑ v, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set w : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hw
  have hwpos : ∀ v, 0 < w v := fun v => div_pos (exp_pos _) hZpos
  have hw1 : ∑ v, w v = 1 := by
    rw [hw]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hcard : (0:ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      ⟨Classical.arbitrary V⟩)
  -- per-term: log (w * n) = log w + log n
  have hterm : ∀ v ∈ Finset.univ,
      w v * Real.log (w v * (Fintype.card V : ℝ))
        = w v * Real.log (w v)
          + w v * Real.log (Fintype.card V : ℝ) := by
    intro v _
    have hsplit : Real.log (w v * (Fintype.card V : ℝ))
        = Real.log (w v) + Real.log (Fintype.card V : ℝ) :=
      (Real.log_mul (ne_of_gt (hwpos v)) (ne_of_gt hcard))
    rw [hsplit, mul_add]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hsecond : ∑ v, w v * Real.log (Fintype.card V : ℝ)
      = Real.log (Fintype.card V : ℝ) := by
    have hcomm : ∑ v, w v * Real.log (Fintype.card V : ℝ)
        = ∑ v, Real.log (Fintype.card V : ℝ) * w v :=
      Finset.sum_congr rfl (fun v _ => by rw [mul_comm])
    rw [hcomm, ← Finset.mul_sum, hw1, mul_one]
  rw [hsecond]

open Finset in
/-- **Элементарный зазор Гиббса (R432)** —
первый кирпич моста к multiplicative
weights (RAG-опора: arXiv 2608.09389,
EW-regret ≤ M√(2 ln A·T)):
⟨E⟩_T ≤ E_min + T·n для ЛЮБЫх E
(без гэп-предположений!).
Доказательство:
x + T ≤ T·e^{x/T} почленно +
свёртка w·e^{(E−Emin)/T} = e^{−Emin/T}
тожденственно. При температуре
η = T/шаг это без-regret зона
экспоненциальных весов. -/
theorem gibbs_energy_gap_crude {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    ∃ vmin : V, (∑ v, E v * Real.exp (-(E v)/T))
        / (∑ v, Real.exp (-(E v)/T)) - E vmin
      ≤ T * (Fintype.card V : ℝ) := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, E vmin ≤ E v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) E
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  have hZpos : (0:ℝ) < ∑ v, Real.exp (-(E v)/T) :=
    Finset.sum_pos (fun v _ => exp_pos _) ⟨vmin, Finset.mem_univ _⟩
  -- numerator identity
  have hterm : ∀ v : V, Real.exp (-(E v)/T) * (E v - E vmin)
      = E v * Real.exp (-(E v)/T)
        - Real.exp (-(E v)/T) * E vmin := fun v => by ring
  have hnum : (∑ v, E v * Real.exp (-(E v)/T))
      / (∑ v, Real.exp (-(E v)/T)) - E vmin
      = (∑ v, Real.exp (-(E v)/T) * (E v - E vmin))
        / (∑ v, Real.exp (-(E v)/T)) := by
    have hsumEq : ∑ v, Real.exp (-(E v)/T) * (E v - E vmin)
        = ∑ v, E v * Real.exp (-(E v)/T)
          - E vmin * ∑ v, Real.exp (-(E v)/T) := by
      rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun v _ => mul_comm (Real.exp (-(E v)/T)) (E vmin)),
        ← Finset.mul_sum]
    rw [hsumEq, sub_div, mul_div_cancel_right₀ (E vmin) (ne_of_gt hZpos)]
  rw [hnum]
  -- per-point exponential identity (folded form)
  have hident : ∀ v : V, Real.exp (-(E v)/T)
      * Real.exp ((E v - E vmin)/T) = Real.exp (-(E vmin)/T) := by
    intro v
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  -- per-point bound: x <= T*exp(x/T) - T... via add_one_le_exp
  have hpt : ∀ v : V, Real.exp (-(E v)/T) * (E v - E vmin)
      ≤ Real.exp (-(E v)/T) * (T * Real.exp ((E v - E vmin)/T)) := by
    intro v
    have hnn : (0:ℝ) ≤ E v - E vmin := sub_nonneg.mpr (hvmin v)
    have hmult := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp ((E v - E vmin)/T)) (le_of_lt hT)
    have hrew : T * ((E v - E vmin)/T + 1)
        = (E v - E vmin) + T := by
      rw [mul_add]
      have hd : T * ((E v - E vmin)/T) = E v - E vmin := by
        field_simp
      rw [hd, mul_one]
    have hkey2 : E v - E vmin
        ≤ T * Real.exp ((E v - E vmin)/T) := by linarith [hmult, hrew]
    exact mul_le_mul_of_nonneg_left hkey2 (exp_pos _).le
  -- sum bound
  have h1 : (∑ v : V, Real.exp (-(E v)/T) * (E v - E vmin))
      ≤ ∑ v : V, Real.exp (-(E v)/T)
        * (T * Real.exp ((E v - E vmin)/T)) :=
    Finset.sum_le_sum (fun v _ => hpt v)
  have hterm2 : ∀ v : V, Real.exp (-(E v)/T)
      * (T * Real.exp ((E v - E vmin)/T))
      = T * Real.exp (-(E vmin)/T) := by
    intro v
    calc Real.exp (-(E v)/T) * (T * Real.exp ((E v - E vmin)/T))
        = T * (Real.exp (-(E v)/T)
          * Real.exp ((E v - E vmin)/T)) := by ring
      _ = T * Real.exp (-(E vmin)/T) := by rw [hident v]
  have h2 : ∑ v : V, Real.exp (-(E v)/T)
        * (T * Real.exp ((E v - E vmin)/T))
      = T * (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
    rw [Finset.sum_congr rfl (fun v _ => hterm2 v), Finset.sum_const]
    norm_num
    ring
  have hsum : (∑ v : V, Real.exp (-(E v)/T) * (E v - E vmin))
      ≤ T * (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) :=
    h1.trans_eq h2
  have hC : Real.exp (-(E vmin)/T)
      ≤ ∑ v, Real.exp (-(E v)/T) :=
    single_le_sum (f := fun v => Real.exp (-(E v)/T))
      (fun v _ => le_of_lt (exp_pos _)) (Finset.mem_univ vmin)
  rw [div_le_iff₀ hZpos]
  have hn : (0:ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hC (mul_nonneg (le_of_lt hT) hn)
  linarith [hsum, hmul]

open Finset in
/-- **Log-декомпозиция Гиббс-веса
(R445)** (PAC-Bayes/Катони, RAG arXiv
2609.12891): ln(ρ_v·n) = ln n − ln Z −
E_v/T — вес = сложение
случайности,
нормировки и
энергии. Кирпич
KL-тождества Катони
(λ⟨r⟩ + KL = −ln Z_π):
суммирование по
v даёт тождество
в целом. -/
theorem gibbs_weight_log_decomp {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (v : V) :
    Real.log ((Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ))
    = Real.log (Fintype.card V : ℝ)
      - Real.log (∑ v : V, Real.exp (-(E v)/T))
      - (E v)/T := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnn : (0:ℝ) < n :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hsplit : (Real.exp (-(E v)/T) / Z) * n
      = n * Real.exp (-(E v)/T) / Z := by
    field_simp
  have hexpne : Real.exp (-(E v)/T) ≠ 0 := by positivity
  rw [hsplit, Real.log_div (by positivity) hZpos.ne',
    Real.log_mul hnn.ne' hexpne, Real.log_exp]
  ring

open Finset in
/-- **KL-тождество Катони (R446)**:
KL(ρḟ‖unif) = −ln Z − ⟨E⟩/T + ln n —
суммарование
log-декомпозиции
R445: λ⟨r⟩ + KL(ρḟ‖π) =
−ln Z_π в uniform-случае.
Связь с известным:
вместе с R422 (KL = ln n − S)
даёт F = ⟨E⟩ − T·S — гибсовская
свободная энергия из
PAC-Bayes-тожества. Мост
термодинамика ↔
PAC-Bayes формально замкнут. -/
theorem gibbs_katoni_kl {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) :
    (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log ((Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T))
        * (Fintype.card V : ℝ)))
    = Real.log (Fintype.card V : ℝ)
      - Real.log (∑ v : V, Real.exp (-(E v)/T))
      - (1/T) * (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)) * E v) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set ρ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hρ
  have hρsum : ∑ v : V, ρ v = 1 := by
    rw [hρ]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  -- per-term split
  have hterm : ∀ v : V, ρ v * Real.log (ρ v * n)
      = ρ v * (Real.log n - Real.log Z)
        - (ρ v * E v)/T := by
    intro v
    rw [gibbs_weight_log_decomp E T hT v, mul_sub, mul_div_assoc]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib]
  -- part 1: sum(rho * c) = c
  rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v)
      (Real.log n - Real.log Z)), ← Finset.mul_sum, hρsum, mul_one]
  -- part 2: sum (rho E / T) = (sum rho E)/T
  rw [← Finset.sum_div]
  ring

open Finset in
/-- **Общий второй закон (R447)**:
KL(ρḟ‖γ) ≥ 0 для любых
двух распределений
на конечном носителе:
ln u ≤ u−1 почленно с
u := γ/ρ даёт ρ·ln(ρ/γ) ≥ ρ−γ;
телескоп даёт 0.
Обобщение R418 (Гибс-случай)
на произвольные пары;
основа для вариационного
принципа Гиббса. -/
theorem finite_kl_nonneg {V : Type*} [Fintype V] [Nonempty V]
    (ρ γ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1)
    (hγ : ∀ v, 0 < γ v) (hγ1 : ∑ v : V, γ v = 1) :
    (0:ℝ) ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) := by
  -- per-v: ln(gamma/rho) <= gamma/rho - 1
  have hln : ∀ v : V, Real.log (γ v / ρ v) ≤ γ v / ρ v - 1 :=
    fun v => Real.log_le_sub_one_of_pos (div_pos (hγ v) (hρ v))
  -- negate: rho * log(rho/gamma) >= rho - gamma
  have hterm : ∀ v : V, ρ v - γ v
      ≤ ρ v * Real.log (ρ v / γ v) := by
    intro v
    have hneg : Real.log (ρ v / γ v) = -(Real.log (γ v / ρ v)) := by
      rw [Real.log_div (hρ v).ne' (hγ v).ne',
        Real.log_div (hγ v).ne' (hρ v).ne']
      ring
    rw [hneg]
    have hc : ρ v * (γ v / ρ v) = γ v := by
      field_simp [(hρ v).ne']
    -- -rho*log(gamma/rho) >= rho - gamma
    nlinarith [hln v, hρ v, hc]
  -- sum telescope
  have hsum : ∑ x : V, (ρ x - γ x) = 0 := by
    rw [Finset.sum_sub_distrib, hρ1, hγ1, sub_self]
  calc (0:ℝ)
      = ∑ v : V, (ρ v - γ v) := by rw [hsum]
    _ ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) :=
      Finset.sum_le_sum (fun v _ => hterm v)

open Finset in
/-- **Вариационный
принцип Гиббса (R448)**:
для любого распределения ρ:
⟨E⟩_ρ + T·Σρ ln ρ ≥ −T·ln Z —
свободная энергия
любого ρ (⟨E⟩ − T·S
с S = −Σρ ln ρ) не меньше
гиббсовой F = −T ln Z.
Вывод: R447 (KL ≥ 0) на
Гиббс-мере γ с
разворачиванием
T·KL почленно
(T·KL = T·Σρ ln ρ + ⟨E⟩ + T ln Z).
Равенство на Гиббсе —
R446. Минимум свободной
энергии достигается
равновесным
распределением. -/
theorem gibbs_variational {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    -T * Real.log (∑ v : V, Real.exp (-(E v)/T))
      ≤ (∑ v : V, ρ v * E v)
        + T * (∑ v : V, ρ v * Real.log (ρ v)) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZdef
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set γ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hγ
  have hγpos : ∀ v, 0 < γ v := fun v => by
    rw [hγ]; positivity
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]
    simp only
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  have hlogγ : ∀ v : V, Real.log (γ v)
      = -(E v)/T - Real.log Z := by
    intro v
    rw [hγ, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
  -- T * KL = T*S-form + <E> + T log Z
  have hTKL : T * (∑ v : V, ρ v * Real.log (ρ v / γ v))
      = T * (∑ v : V, ρ v * Real.log (ρ v))
        + (∑ v : V, ρ v * E v) + T * Real.log Z := by
    have hsplit : ∀ v : V,
        T * (ρ v * Real.log (ρ v / γ v))
        = ρ v * (T * Real.log (ρ v)) + ρ v * E v
          + ρ v * (T * Real.log Z) := by
      intro v
      rw [Real.log_div (hρ v).ne' (hγpos v).ne', hlogγ v]
      field_simp
      ring
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun v _ =>
      mul_left_comm (ρ v) T (Real.log (ρ v)))]
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v) (T * Real.log Z))]
    rw [← Finset.mul_sum, hρ1, mul_one]
  have hKL' : (0:ℝ) ≤ T * (∑ v : V, ρ v * Real.log (ρ v / γ v)) :=
    mul_nonneg (le_of_lt hT) hKL
  rw [hTKL] at hKL'
  linarith

open Finset in
/-- **Нижняя грань свободной энергии (R449)**:
E_min − T·ln n ≤ F = −T·ln Z.
Вместе с R421 (F ≤ E*) — сэндвич свободной энергии:
E_min − T·ln n ≤ F ≤ E_min.
Классическая термодинамика: свободная энергия
зажата между основанием с энтропийным
запасом T·ln n и насыщением E_min.
Метод: Z ≤ n·e^{−E_min/T} почленно + монотонность ln
+ умножение на −T < 0. -/
theorem gibbs_free_energy_lower {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vmin : V) (hmin : ∀ v : V, E vmin ≤ E v) :
    (E vmin) - T * Real.log ((Fintype.card V : ℝ))
      ≤ -T * Real.log (∑ v : V, Real.exp (-(E v)/T)) := by
  have hZ : ∑ v : V, Real.exp (-(E v)/T)
      ≤ (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
    have hexp : ∀ v : V, Real.exp (-(E v)/T)
        ≤ Real.exp (-(E vmin)/T) := by
      intro v
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div]
      exact neg_le_neg ((div_le_div_iff_of_pos_right hT).mpr (hmin v))
    calc ∑ v : V, Real.exp (-(E v)/T)
        ≤ ∑ v : V, Real.exp (-(E vmin)/T) :=
          Finset.sum_le_sum (fun v _ => hexp v)
      _ = (Fintype.card V : ℝ) * Real.exp (-(E vmin)/T) := by
          simp [Finset.sum_const]
  have hn : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hexpmin : (0:ℝ) < Real.exp (-(E vmin)/T) := exp_pos _
  have hlog : Real.log (∑ v : V, Real.exp (-(E v)/T))
      ≤ Real.log ((Fintype.card V : ℝ)) - (E vmin)/T := by
    have h1 := Real.log_le_log (Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩) hZ
    rw [Real.log_mul hn.ne' hexpmin.ne', Real.log_exp, neg_div] at h1
    exact h1
  have h3 : -T * (Real.log ((Fintype.card V : ℝ)) - (E vmin)/T)
      = (E vmin) - T * Real.log ((Fintype.card V : ℝ)) := by
    field_simp
    ring
  have h4 := mul_le_mul_of_nonpos_left hlog (by linarith : (-T:ℝ) ≤ 0)
  rw [h3] at h4
  exact h4

open Finset in
/-- **Максимальная энтропия (R450)**:
S(ρ) = −Σρ ln ρ ≤ ln n для любого
распределения на n-точечном
носителе — равновесие
(uniform) максимизирует энтропию.
Вывод: R447 с γ = uniform:
KL(ρḟ‖unif) ≥ 0 ⇔ S ≤ ln n.
Вместе с R418 (S ≥ 0) и R429 (Нернст
на термостате) — полный
энтропийный контур любого
распределения: 0 ≤ S ≤ ln n. -/
theorem finite_max_entropy {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (ρ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    -(∑ v : V, ρ v * Real.log (ρ v))
      ≤ Real.log ((Fintype.card V : ℝ)) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnne : n ≠ 0 := by positivity
  set γ : V → ℝ := fun _ => 1/n with hγ
  have hγpos : ∀ v, 0 < γ v := by
    intro v; rw [hγ]; positivity
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, one_div]
    rw [← hn]
    exact mul_inv_cancel₀ hnne
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  -- expand KL: sum rho (log rho + log n)
  have hexp : ∑ v : V, ρ v * Real.log (ρ v / γ v)
      = (∑ v : V, ρ v * Real.log (ρ v))
        + Real.log n := by
    have hsplit : ∀ v : V, ρ v * Real.log (ρ v / γ v)
        = ρ v * Real.log (ρ v) + ρ v * Real.log n := by
      intro v
      rw [hγ, one_div, div_inv_eq_mul,
        Real.log_mul (hρ v).ne' hnne]
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (ρ v) (Real.log n))]
    rw [← Finset.mul_sum, hρ1, mul_one]
  rw [hexp] at hKL
  linarith

open Finset in
/-- **Log-sum неравенство (R451)**:
A·ln(A/B) ≤ Σ a·ln(a/b) для
положительных a, b
(A = Σa, B = Σb).
Вывод: нормализация
a/A, b/B в распределения +
R447 (KL ≥ 0); без Коши-Энгеля.
Классический кирпич
Энтропийной неравенств
цепи и основа
Пинскера/Гиббса-Дюгема. -/
theorem log_sum_ineq {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (a b : V → ℝ)
    (ha : ∀ v, 0 < a v) (hb : ∀ v, 0 < b v) :
    (∑ v : V, a v) * Real.log ((∑ v : V, a v) / (∑ v : V, b v))
      ≤ ∑ v : V, a v * Real.log (a v / b v) := by
  set A : ℝ := ∑ v : V, a v with hA
  set B : ℝ := ∑ v : V, b v with hB
  have hApos : 0 < A :=
    Finset.sum_pos (fun v _ => ha v)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hBpos : 0 < B :=
    Finset.sum_pos (fun v _ => hb v)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set ρ : V → ℝ := fun v => a v / A with hρ
  set γ : V → ℝ := fun v => b v / B with hγ
  have hρpos : ∀ v, 0 < ρ v :=
    fun v => by rw [hρ]; exact div_pos (ha v) hApos
  have hγpos : ∀ v, 0 < γ v :=
    fun v => by rw [hγ]; exact div_pos (hb v) hBpos
  have hρ1 : ∑ v : V, ρ v = 1 := by
    rw [hρ]; simp only; rw [← Finset.sum_div]; exact div_self hApos.ne'
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]; simp only; rw [← Finset.sum_div]; exact div_self hBpos.ne'
  have hKL := finite_kl_nonneg ρ γ hρpos hρ1 hγpos hγ1
  have hexp : ∑ v : V, ρ v * Real.log (ρ v / γ v)
      = (1/A) * (∑ v : V, a v * Real.log (a v / b v))
        + Real.log (B/A) := by
    have hsplit : ∀ v : V, ρ v * Real.log (ρ v / γ v)
        = (1/A) * (a v * Real.log (a v / b v))
          + (a v / A) * Real.log (B/A) := by
      intro v
      have hr : ρ v / γ v = (a v / b v) * (B / A) := by
        rw [hρ, hγ]; field_simp
      have hab : 0 < a v / b v := div_pos (ha v) (hb v)
      have hBA : 0 < B / A := div_pos hBpos hApos
      rw [hr, Real.log_mul hab.ne' hBA.ne', hρ]
      simp only
      field_simp
    have hs1 : ∑ v : V, (1/A) * (a v * Real.log (a v / b v))
        = (1/A) * (∑ v : V, a v * Real.log (a v / b v)) :=
      (Finset.mul_sum Finset.univ
        (fun v => a v * Real.log (a v / b v)) (1/A)).symm
    have hs2 : ∑ v : V, (a v / A) * Real.log (B / A)
        = Real.log (B / A) := by
      rw [← Finset.sum_mul, ← Finset.sum_div,
        div_self hApos.ne', one_mul]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib, hs1, hs2]
  rw [hexp] at hKL
  have hlogneg : Real.log (A / B) = -(Real.log (B / A)) := by
    rw [Real.log_div hApos.ne' hBpos.ne',
      Real.log_div hBpos.ne' hApos.ne']
    ring
  rw [hlogneg]
  have hKLA := mul_nonneg hKL hApos.le
  field_simp at hKLA
  linarith

open Finset in
/-- **Log-sum неравенство на
подмножестве (R452)**:
для s ⊆ V и положительных на s:
(Σ_{v∈s} a)·ln(Σa/Σb) ≤ Σ_{v∈s} a·ln(a/b).
Доказательство:
применение R451 к
подтипу {v // v ∈ s}
(Finset.sum_coe_sort).
Кирпич для
неравенства
обработки данных (KL не
растёт при сжатии по
слоям). -/
theorem log_sum_ineq_on {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty)
    (a b : V → ℝ)
    (ha : ∀ v ∈ s, 0 < a v) (hb : ∀ v ∈ s, 0 < b v) :
    (∑ v ∈ s, a v) * Real.log ((∑ v ∈ s, a v) / (∑ v ∈ s, b v))
      ≤ ∑ v ∈ s, a v * Real.log (a v / b v) := by
  -- subtype carrier
  have hne : Nonempty {v // v ∈ s} := hs.to_subtype
  have hsub := @log_sum_ineq {v // v ∈ s} _ _ hne
    (fun v => a v.val) (fun v => b v.val)
    (fun v => ha v.1 v.2) (fun v => hb v.1 v.2)
  -- convert coe-sort sums to Finset sums
  rw [Finset.sum_coe_sort, Finset.sum_coe_sort] at hsub
  have hlast : ∑ v : {v // v ∈ s}, a v.val * Real.log (a v.val / b v.val)
      = ∑ v ∈ s, a v * Real.log (a v / b v) :=
    Finset.sum_coe_sort s (fun x => a x * Real.log (a x / b x))
  rw [hlast] at hsub
  exact hsub

open Finset in
/-- **Неравенство
обработки данных (R453)**:
KL(Tρḟ‖Tγ) ≤ KL(ρḟ‖γ) для
любого отображения T:
информация только
теряется при
обработке.
Механика:
fiber-разложение
(Finset.sum_fiberwise) + log-sum
почленно по слоям
(R452); пустые слои — нулевой
вклад (log 0 = 0). -/
theorem kl_data_processing {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [Nonempty V]
    (T : V → W)
    (ρ γ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1)
    (hγ : ∀ v, 0 < γ v) (hγ1 : ∑ v : V, γ v = 1) :
    (∑ w : W, (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
        * Real.log ((∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
          / (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, γ v)))
    ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) := by
  -- fiber decomposition: RHS = sum over W of fiber sums
  have hdecomp : (∑ v : V, ρ v * Real.log (ρ v / γ v))
      = ∑ w : W, ∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ,
          ρ v * Real.log (ρ v / γ v) :=
    (Finset.sum_fiberwise Finset.univ T
      (fun v => ρ v * Real.log (ρ v / γ v))).symm
  -- per-fiber log-sum (case split on fiber emptiness)
  have hper : ∀ w : W,
      (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
        * Real.log ((∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
          / (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, γ v))
      ≤ ∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ,
          ρ v * Real.log (ρ v / γ v) := by
    intro w
    by_cases hfib : (Finset.filter (fun v => T v = w) Finset.univ).Nonempty
    · exact log_sum_ineq_on _ hfib ρ γ
        (fun v hv => hρ v) (fun v hv => hγ v)
    · -- empty fiber: both sides 0
      have he : Finset.filter (fun v => T v = w) Finset.univ = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hfib
      rw [he]
      simp [Real.log_zero, zero_div]
  rw [hdecomp]
  exact Finset.sum_le_sum (fun w _ => hper w)

open Real in
/-- **Двухточечная
вогнутость ln (R454)**:
λ·ln x + (1−λ)·ln y ≤
ln(λx+(1−λ)y).
Без calculus:
взвешенное AM-GM
(Реал.geom_mean_le_arith_mean2_weighted)
+ монотонность ln.
Кирпич выпуклости KL-
дивергенции. -/
theorem log_concave_two {lam x y : ℝ} (hlam : 0 < lam) (hlam2 : lam < 1)
    (hx : 0 < x) (hy : 0 < y) :
    lam * Real.log x + (1 - lam) * Real.log y
      ≤ Real.log (lam * x + (1 - lam) * y) := by
  have h1 : x ^ lam * y ^ (1 - lam) ≤ lam * x + (1 - lam) * y :=
    Real.geom_mean_le_arith_mean2_weighted hlam.le
      (by linarith : (0:ℝ) ≤ 1 - lam) hx.le hy.le
      (by ring)
  have h2 : Real.log (x ^ lam * y ^ (1 - lam))
      = lam * Real.log x + (1 - lam) * Real.log y := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hx lam).ne'
      (Real.rpow_pos_of_pos hy (1 - lam)).ne',
      Real.log_rpow hx, Real.log_rpow hy]
  rw [← h2]
  exact Real.log_le_log (mul_pos
    (Real.rpow_pos_of_pos hx lam)
    (Real.rpow_pos_of_pos hy (1 - lam))) h1

open Finset Real in
/-- **Выпуклость x·ln x (R455)**:
(λa+(1−λ)b)·ln(λa+(1−λ)b) ≤
λa·ln a + (1−λ)b·ln b.
Доказательство: log-sum (R451)
на Bool-носителе с
α = (λa, (1−λ)b),
β = (λ, 1−λ) (Σβ = 1).
Энтропийная
функция выпукла —
кирпич выпуклости KL-
дивергенции. -/
theorem xlogx_convex {a b lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlam : 0 < lam) (hlam2 : lam < 1) :
    (lam * a + (1 - lam) * b) * Real.log (lam * a + (1 - lam) * b)
      ≤ lam * a * Real.log a + (1 - lam) * b * Real.log b := by
  set α : Bool → ℝ := fun t => if t then lam * a else (1 - lam) * b with hα
  set β : Bool → ℝ := fun t => if t then lam else 1 - lam with hβ
  have hαpos : ∀ t : Bool, 0 < α t := by
    intro t; cases t <;> rw [hα] <;> simp <;> positivity
  have hβpos : ∀ t : Bool, 0 < β t := by
    intro t; cases t <;> rw [hβ] <;> simp <;> linarith
  have hsum := log_sum_ineq α β hαpos hβpos
  have hβ1 : ∑ t : Bool, β t = 1 := by
    rw [hβ]; simp [Fin.sum_univ_two]
  have hα1 : ∑ t : Bool, α t = lam * a + (1 - lam) * b := by
    rw [hα]; simp [Fin.sum_univ_two]
  rw [hβ1, div_one, hα1] at hsum
  have hexp : ∑ t : Bool, α t * Real.log (α t / β t)
      = lam * a * Real.log a + (1 - lam) * b * Real.log b := by
    have hdiv1 : lam * a / lam = a := by
      field_simp
    have hdiv2 : (1 - lam) * b / (1 - lam) = b := by
      field_simp
      ring_nf
      linarith [mul_inv_cancel₀ (ne_of_gt (show 0 < 1 - lam by linarith))]
    rw [hα, hβ]
    simp [hdiv1, hdiv2]
  rw [hexp] at hsum
  exact hsum

open Real in
/-- **Скалярная выпуклость
x·ln(x/y) по x (R456)**:
(λa+(1−λ)b)·ln((λa+(1−λ)b)/y) ≤
λa·ln(a/y) + (1−λ)b·ln(b/y).
Вывод: R455 (z·ln z выпукла)
+ линейность
z·ln y. Кирпич
выпуклости KL по
первому аргументу. -/
theorem xlog_div_convex {a b y lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 < y) (hlam : 0 < lam) (hlam2 : lam < 1) :
    (lam * a + (1 - lam) * b)
      * Real.log ((lam * a + (1 - lam) * b) / y)
      ≤ lam * a * Real.log (a / y) + (1 - lam) * b * Real.log (b / y) := by
  have hz : 0 < lam * a + (1 - lam) * b :=
    add_pos (mul_pos hlam ha) (mul_pos (by linarith : (0:ℝ) < 1 - lam) hb)
  have h1 := xlogx_convex ha hb hlam hlam2
  -- expand logs: ln(x/y) = ln x - ln y
  rw [Real.log_div hz.ne' hy.ne', Real.log_div ha.ne' hy.ne',
    Real.log_div hb.ne' hy.ne']
  -- z * (ln z - ln y) = z*ln z - z*ln y; split linear term
  have hsplit : (lam * a + (1 - lam) * b) * Real.log y
      = lam * a * Real.log y + (1 - lam) * b * Real.log y := by
    ring
  rw [mul_sub, hsplit]
  linarith

open Finset Real in
/-- **Выпуклость KL по
первому аргументу (R457)**:
KL(λρ₁+(1−λ)ρ₂ ḟ‖ γ) ≤
λ·KL(ρ₁ḟ‖γ)+(1−λ)·KL(ρ₂ḟ‖γ).
Вывод: почленное R456 +
разделение сумм.
Дуга выпуклости
завершена:
R454→R455→R456→R457. -/
theorem kl_convex_first {V : Type*} [Fintype V] [Nonempty V]
    (ρ₁ ρ₂ γ : V → ℝ) (lam : ℝ)
    (hρ₁ : ∀ v, 0 < ρ₁ v) (hρ₂ : ∀ v, 0 < ρ₂ v)
    (hγ : ∀ v, 0 < γ v)
    (hlam : 0 < lam) (hlam2 : lam < 1) :
    (∑ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
        * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v))
    ≤ lam * (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ v))
      + (1 - lam) * (∑ v : V, ρ₂ v * Real.log (ρ₂ v / γ v)) := by
  have hper : ∀ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
      * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v)
      ≤ lam * (ρ₁ v * Real.log (ρ₁ v / γ v))
        + (1 - lam) * (ρ₂ v * Real.log (ρ₂ v / γ v)) :=
    fun v => by
      have h := xlog_div_convex (hρ₁ v) (hρ₂ v) (hγ v) hlam hlam2
      linarith
  calc (∑ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
        * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v))
      ≤ ∑ v : V, (lam * (ρ₁ v * Real.log (ρ₁ v / γ v))
          + (1 - lam) * (ρ₂ v * Real.log (ρ₂ v / γ v))) :=
        Finset.sum_le_sum (fun v _ => hper v)
    _ = lam * (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ v))
        + (1 - lam) * (∑ v : V, ρ₂ v * Real.log (ρ₂ v / γ v)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

open Finset Real in
/-- **Аддитивность KL на
произведении (R458)**:
KL(ρ₁×ρ₂ ḟ‖ γ₁×γ₂) =
KL(ρ₁ḟ‖γ₁) + KL(ρ₂ḟ‖γ₂)
(цепное правило для
независимых).
Механика: log-
разложение + Fubini
(Fintype.sum_prod_type +
sum_congr/свёртка
строк через
Σρ = 1). -/
theorem kl_product_additive {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W]
    (ρ₁ γ₁ : V → ℝ) (ρ₂ γ₂ : W → ℝ)
    (hρ₁ : ∀ v, 0 < ρ₁ v) (hρ₂ : ∀ w, 0 < ρ₂ w)
    (hγ₁ : ∀ v, 0 < γ₁ v) (hγ₂ : ∀ w, 0 < γ₂ w)
    (hρ₁s : ∑ v : V, ρ₁ v = 1) (hρ₂s : ∑ w : W, ρ₂ w = 1) :
    (∑ p : V × W, (ρ₁ p.1 * ρ₂ p.2)
        * Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2)))
    = (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ₁ v))
      + (∑ w : W, ρ₂ w * Real.log (ρ₂ w / γ₂ w)) := by
  have hsplit : ∀ p : V × W,
      Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2))
      = (Real.log (ρ₁ p.1) + Real.log (ρ₂ p.2)
          - Real.log (γ₁ p.1) - Real.log (γ₂ p.2)) := by
    intro p
    rw [Real.log_div (mul_pos (hρ₁ p.1) (hρ₂ p.2)).ne'
      (mul_pos (hγ₁ p.1) (hγ₂ p.2)).ne']
    rw [Real.log_mul (hρ₁ p.1).ne' (hρ₂ p.2).ne',
      Real.log_mul (hγ₁ p.1).ne' (hγ₂ p.2).ne']
    ring
  -- expand the summand algebraically
  have hterm : ∀ p : V × W, (ρ₁ p.1 * ρ₂ p.2)
      * Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2))
      = ρ₁ p.1 * ρ₂ p.2 * Real.log (ρ₁ p.1)
        + ρ₁ p.1 * ρ₂ p.2 * Real.log (ρ₂ p.2)
        - ρ₁ p.1 * ρ₂ p.2 * Real.log (γ₁ p.1)
        - ρ₁ p.1 * ρ₂ p.2 * Real.log (γ₂ p.2) := by
    intro p
    rw [hsplit p]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  -- Fubini bricks
  have hfibV : ∀ f : V → ℝ, (∑ p : V × W, ρ₁ p.1 * ρ₂ p.2 * f p.1)
      = (∑ v : V, ρ₁ v * f v) := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ₁ (v, w).1 * ρ₂ (v, w).2 * f (v, w).1 = (ρ₁ v * f v) * ρ₂ w
      simp only; ring)]
    rw [← Finset.mul_sum, hρ₂s, mul_one]
  have hfibW : ∀ g : W → ℝ, (∑ p : V × W, ρ₁ p.1 * ρ₂ p.2 * g p.2)
      = (∑ w : W, ρ₂ w * g w) := by
    intro g
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, ρ₁ (v, w).1 * ρ₂ (v, w).2 * g (v, w).2
          = (∑ w : W, ρ₂ w * g w) * ρ₁ v := by
      intro v
      rw [Finset.sum_congr rfl (fun w _ => by
        show ρ₁ (v, w).1 * ρ₂ (v, w).2 * g (v, w).2
          = (ρ₂ w * g w) * ρ₁ v
        simp only; ring)]
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    rw [← Finset.mul_sum, hρ₁s, mul_one]
  rw [hfibV (fun v => Real.log (ρ₁ v)), hfibV (fun v => Real.log (γ₁ v)),
    hfibW (fun w => Real.log (ρ₂ w)), hfibW (fun w => Real.log (γ₂ w))]
  -- split log-div sums
  have hsplit2 : ∀ (f g : V → ℝ), (∀ v, 0 < f v) → (∀ v, 0 < g v) →
      (∑ v : V, f v * Real.log (f v / g v))
      = (∑ v : V, f v * Real.log (f v))
        - (∑ v : V, f v * Real.log (g v)) := by
    intro f g hf hg
    have hpt : ∀ v : V, f v * Real.log (f v / g v)
        = f v * Real.log (f v) - f v * Real.log (g v) := by
      intro v
      rw [Real.log_div (hf v).ne' (hg v).ne', mul_sub]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_sub_distrib]
  have hsplit2W : ∀ (f g : W → ℝ), (∀ w, 0 < f w) → (∀ w, 0 < g w) →
      (∑ w : W, f w * Real.log (f w / g w))
      = (∑ w : W, f w * Real.log (f w))
        - (∑ w : W, f w * Real.log (g w)) := by
    intro f g hf hg
    have hpt : ∀ w : W, f w * Real.log (f w / g w)
        = f w * Real.log (f w) - f w * Real.log (g w) := by
      intro w
      rw [Real.log_div (hf w).ne' (hg w).ne', mul_sub]
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib]
  rw [hsplit2 ρ₁ γ₁ hρ₁ hγ₁, hsplit2W ρ₂ γ₂ hρ₂ hγ₂]
  linarith

open Finset Real in
/-- **Субаддитивность
энтропии (R459)**:
S(совместное) ≤
S(маргинальное по V)
+ S(маргинальное по W).
Вывод через взаимную
информацию: KL(ρ ḟ‖ μ₁×μ₂)
= S₁+S₂−S ≥ 0 (R447);
механика в стиле R458
(Fubini-свёртки).
Классика теории
информации. -/
theorem entropy_subadditive {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    -(∑ p : V × W, ρ p * Real.log (ρ p))
      ≤ -(∑ v : V, (∑ w : W, ρ (v, w)) * Real.log (∑ w : W, ρ (v, w)))
        - (∑ w : W, (∑ v : V, ρ (v, w)) * Real.log (∑ v : V, ρ (v, w))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  set μ₂ : W → ℝ := fun w => ∑ v : V, ρ (v, w) with hμ₂
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  have hμ₂pos : ∀ w, 0 < μ₂ w := by
    intro w
    have := Finset.sum_pos (fun v _ => hρ (v, w))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [hμ₂]; exact this
  -- product of marginals is a distribution
  set γ : V × W → ℝ := fun p => μ₁ p.1 * μ₂ p.2 with hγ
  have hγpos : ∀ p, 0 < γ p := fun p => by
    rw [hγ]; exact mul_pos (hμ₁pos p.1) (hμ₂pos p.2)
  have hμ₁s : ∑ v : V, μ₁ v = 1 := by
    rw [hμ₁, ← Fintype.sum_prod_type]; exact hρ1
  have hμ₂s : ∑ w : W, μ₂ w = 1 := by
    rw [hμ₂, Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hρ1
  have hγ1 : ∑ p : V × W, γ p = 1 := by
    show ∑ p : V × W, μ₁ p.1 * μ₂ p.2 = 1
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, μ₁ (v, w).1 * μ₂ (v, w).2 = μ₁ v := by
      intro v
      simp only []
      rw [← Finset.mul_sum, hμ₂s, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    exact hμ₁s
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  -- expand KL = A - B - C
  have hexp : ∑ p : V × W, ρ p * Real.log (ρ p / γ p)
      = (∑ p : V × W, ρ p * Real.log (ρ p))
        - (∑ p : V × W, ρ p * Real.log (μ₁ p.1))
        - (∑ p : V × W, ρ p * Real.log (μ₂ p.2)) := by
    have hpt : ∀ p : V × W, ρ p * Real.log (ρ p / γ p)
        = ρ p * Real.log (ρ p) - ρ p * Real.log (μ₁ p.1)
          - ρ p * Real.log (μ₂ p.2) := by
      intro p
      rw [hγ]
      rw [Real.log_div (hρ p).ne' (mul_pos (hμ₁pos p.1) (hμ₂pos p.2)).ne']
      rw [Real.log_mul (hμ₁pos p.1).ne' (hμ₂pos p.2).ne']
      ring
    rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  -- Fubini collapse of cross terms
  have hfibV : ∀ f : V → ℝ, (∑ p : V × W, ρ p * f p.1)
      = (∑ v : V, μ₁ v * f v) := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ (v, w) * f (v, w).1 = ρ (v, w) * f v
      simp only)]
    rw [Finset.sum_mul]
  have hfibW : ∀ g : W → ℝ, (∑ p : V × W, ρ p * g p.2)
      = (∑ w : W, μ₂ w * g w) := by
    intro g
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [Finset.sum_congr rfl (fun v _ => by
      show ρ (v, w) * g (v, w).2 = ρ (v, w) * g w
      simp only)]
    rw [← Finset.sum_mul, hμ₂]
  rw [hexp, hfibV (fun v => Real.log (μ₁ v)), hfibW (fun w => Real.log (μ₂ w))] at hKL
  rw [hμ₁] at hKL
  rw [hμ₂] at hKL
  linarith

open Finset Real in
/-- **Цепное правило
энтропии Шеннона (R460)**:
S(V,W) = S(V) + Σᵥ μ₁(v)·S(условная)
— совместная энтропия =
маргинальная + средняя
условная по условному
ядру ρ(v,w)/μ₁(v).
Механика: per-term log-
разделение + Fubini-
свёртки строк/ядер в
стиле R458/R459.
Вместе с R459 — полная
энтропийная арифметика
совместных распределений. -/
theorem entropy_chain {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (∑ p : V × W, ρ p * Real.log (ρ p))
      = (∑ v : V, (∑ w : W, ρ (v, w))
            * Real.log (∑ w : W, ρ (v, w)))
        + (∑ v : V, (∑ w : W, ρ (v, w))
            * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
                * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w))))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  -- per-term split: rho ln rho = rho ln mu1 + rho ln(rho/mu1)
  have hpt : ∀ p : V × W, ρ p * Real.log (ρ p)
      = ρ p * Real.log (μ₁ p.1)
        + μ₁ p.1 * ((ρ p / μ₁ p.1) * Real.log (ρ p / μ₁ p.1)) := by
    intro p
    rw [Real.log_div (hρ p).ne' (hμ₁pos p.1).ne']
    field_simp [(hμ₁pos p.1).ne']
    ring
  rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib]
  -- first sum: Fubini collapse
  have hA : (∑ p : V × W, ρ p * Real.log (μ₁ p.1))
      = (∑ v : V, μ₁ v * Real.log (μ₁ v)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ (v, w) * Real.log (μ₁ (v, w).1) = ρ (v, w) * Real.log (μ₁ v)
      simp only)]
    rw [Finset.sum_mul]
  -- second sum: row-collapse with cond kernel
  have hB : (∑ p : V × W, μ₁ p.1
      * ((ρ p / μ₁ p.1) * Real.log (ρ p / μ₁ p.1)))
      = (∑ v : V, μ₁ v
          * (∑ w : W, (ρ (v, w) / μ₁ v)
              * Real.log (ρ (v, w) / μ₁ v))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show μ₁ (v, w).1 * ((ρ (v, w) / μ₁ (v, w).1)
          * Real.log (ρ (v, w) / μ₁ (v, w).1))
        = μ₁ v * ((ρ (v, w) / μ₁ v) * Real.log (ρ (v, w) / μ₁ v))
      simp only)]
    rw [← Finset.mul_sum]
  rw [hA, hB]

open Finset Real in
/-- **Лог-сумма
распределения
неположительна (R461a)**:
Σ ρ·ln ρ ≤ 0 при ρ ≤ 1
почленно
(single_le_sum + log-монотонность). -/
theorem dist_log_nonpos {V : Type*} [Fintype V] [Nonempty V]
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    (∑ v : V, ρ v * Real.log (ρ v)) ≤ 0 := by
  have hle : ∀ v : V, ρ v ≤ 1 := by
    intro v
    have h1 := Finset.single_le_sum (f := ρ) (fun w _ => (hρ w).le)
      (Finset.mem_univ v)
    rw [hρ1] at h1
    exact h1
  have hpt : ∀ v : V, ρ v * Real.log (ρ v) ≤ 0 := by
    intro v
    have hl : Real.log (ρ v) ≤ Real.log 1 :=
      Real.log_le_log (hρ v) (hle v)
    rw [Real.log_one] at hl
    nlinarith [hρ v, hl]
  exact Finset.sum_nonpos (fun v _ => hpt v)

/-- **Условие не
увеличивает
энтропию (R461)**:
S(V,W) ≥ S(V) — условная
энтропия неотрицательна.
Вывод: цепное правило R460 +
неположительность
лог-сумм условных
строк. -/
theorem joint_entropy_ge_marginal {V W : Type*} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (∑ p : V × W, ρ p * Real.log (ρ p))
    ≤ (∑ v : V, (∑ w : W, ρ (v, w))
        * Real.log (∑ w : W, ρ (v, w))) := by
  rw [entropy_chain ρ hρ hρ1]
  -- row conditionals are distributions; each row log-sum <= 0
  have hrow : ∀ v : V,
      (∑ w : W, ρ (v, w))
        * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
            * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w)))) ≤ 0 := by
    intro v
    have hμ : (0:ℝ) < ∑ w : W, ρ (v, w) :=
      Finset.sum_pos (fun w _ => hρ (v, w))
        ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    have hsum1 : ∑ w : W, ρ (v, w) / (∑ w : W, ρ (v, w)) = 1 := by
      rw [← Finset.sum_div, div_self hμ.ne']
    have hpos : ∀ w : W,
        0 < ρ (v, w) / (∑ w : W, ρ (v, w)) :=
      fun w => div_pos (hρ (v, w)) hμ
    have hnonpos := dist_log_nonpos
      (fun w => ρ (v, w) / (∑ w : W, ρ (v, w))) hpos hsum1
    nlinarith [hμ]
  have hrows : (∑ v : V,
      (∑ w : W, ρ (v, w))
        * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
            * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w))))) ≤ 0 :=
    Finset.sum_nonpos (fun v _ => hrow v)
  linarith

open Finset Real in
/-- **Тождество свободной
энергии на равновесии (R462)**:
−T·ln Z = ⟨E⟩_γ + T·Σγ ln γ —
F = ⟨E⟩ − T·S в лог-форме
(эквивалент R446 совместно с
PAC-Bayes-выводом).
Механика: per-v
T·γ ln γ = −γE − γ(T ln Z) +
свёртки сумм через
Σγ = 1. -/
theorem gibbs_free_energy_identity {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T) :
    -T * Real.log (∑ v : V, Real.exp (-(E v)/T))
      = (∑ v : V, (Real.exp (-(E v)/T)
            / ∑ v : V, Real.exp (-(E v)/T)) * E v)
        + T * (∑ v : V, (Real.exp (-(E v)/T)
            / ∑ v : V, Real.exp (-(E v)/T))
            * Real.log (Real.exp (-(E v)/T)
              / ∑ v : V, Real.exp (-(E v)/T))) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set γ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hγ
  have hγpos : ∀ v, 0 < γ v := fun v => by
    rw [hγ]; exact div_pos (exp_pos _) hZpos
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]; simp only; rw [← Finset.sum_div]; exact div_self hZpos.ne'
  -- per-term: T * gamma * ln gamma = - gamma * E - gamma * (T ln Z)
  have hpt : ∀ v : V, T * (γ v * Real.log (γ v))
      = -(γ v * E v) - γ v * (T * Real.log Z) := by
    intro v
    rw [hγ, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
    field_simp [(hγpos v).ne', hZpos.ne']
  -- sum the identity
  have hsum : T * (∑ v : V, γ v * Real.log (γ v))
      = -(∑ v : V, γ v * E v)
        - (∑ v : V, γ v) * (T * Real.log Z) := by
    have h1 : T * (∑ v : V, γ v * Real.log (γ v))
        = ∑ v : V, T * (γ v * Real.log (γ v)) := by
      rw [Finset.mul_sum]
    have h2 : (∑ v : V, T * (γ v * Real.log (γ v)))
        = ∑ v : V, (-(γ v * E v) - γ v * (T * Real.log Z)) :=
      Finset.sum_congr rfl (fun v _ => hpt v)
    have h3 : (∑ v : V, (-(γ v * E v) - γ v * (T * Real.log Z)))
        = -(∑ v : V, γ v * E v)
          - (∑ v : V, γ v) * (T * Real.log Z) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_mul]
    rw [h1, h2, h3, hγ1, one_mul]
  -- conclude
  have hgoalE : (∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T)) * E v)
      = (∑ v : V, γ v * E v) :=
    Finset.sum_congr rfl (fun v _ => rfl)
  have hgoalL : (∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)))
      = (∑ v : V, γ v * Real.log (γ v)) :=
    Finset.sum_congr rfl (fun v _ => rfl)
  have hZZ : Real.log Z
      = Real.log (∑ v : V, Real.exp (-(E v)/T)) := rfl
  rw [hgoalE, hgoalL, ← hZZ]
  rw [hγ1, one_mul] at hsum
  linarith

open Finset Real in
/-- **Safety of a lower-bound entropy proxy (R463)**:
if the entropy estimate Ĥ never exceeds the true h,
then the surrogate free energy E − Ĥ majorizes the
true E − h, and the surprise certificate s ≤ E − h is
preserved by construction. -/
theorem proxy_cert_preserved (E h hhat s : ℝ)
    (hlow : hhat ≤ h) (hcert : s ≤ E - h) :
    s ≤ E - hhat := by
  linarith

/-- **Loss of the certificate for an upper-bound
entropy proxy (R463)**: if the proxy strictly exceeds
the true entropy and the true free energy exactly
meets the certificate, the surrogate free energy
falls strictly below it — the AIF bound is not
guaranteed (arXiv 2607.13612, Prop 2(ii)). -/
theorem proxy_cert_lost (E h hhat s : ℝ)
    (hup : h < hhat) (hexact : E - h = s) :
    E - hhat < s := by
  linarith

/-- **Gibbs certificate bridge (R463)**: at the
Gibbs equilibrium the surprise certificate
s ≤ F = −T·ln Z (R462 identity) is preserved by any
lower-bound entropy proxy Ĥ ≤ T·S_γ. -/
theorem gibbs_cert_bridge {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (hhat s : ℝ)
    (hlow : hhat ≤ T * (-(∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)))))
    (hcert : s ≤ -T * Real.log (∑ v : V,
      Real.exp (-(E v)/T))) :
    s ≤ (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)) * E v) - hhat := by
  have hid := gibbs_free_energy_identity E T hT
  linarith

open Real in
/-- **Three-source gap decomposition (R464)**:
the surrogate-true free-energy gap decomposes
exactly into prior-miscalibration, estimator bias
and optimization slack (arXiv 2607.13612, Prop 1). -/
theorem gap_decomposition (F Fhat g1 g2 g3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3) :
    abs (Fhat - F) = abs (g1 + g2 + g3) := by
  rw [hgap]

/-- **Estimator bias is nonpositive for a lower-bound
entropy proxy (R464)**: Gap II = Ĥ − h ≤ 0 whenever
the proxy underestimates the entropy. -/
theorem gapII_nonpos (h hhat : ℝ) (hlow : hhat ≤ h) :
    hhat - h ≤ 0 := by
  linarith

/-- **Graceful degradation, linear slack (R464)**:
if the gap sources obey |g1| ≤ c1, |g2| ≤ c2,
|g3| ≤ c3 then the surrogate-true gap obeys the
triangle bound (arXiv 2607.13612, Cor 2(i)). -/
theorem gap_graceful (F Fhat g1 g2 g3 c1 c2 c3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3)
    (h1 : abs g1 ≤ c1) (h2 : abs g2 ≤ c2)
    (h3 : abs g3 ≤ c3) :
    abs (Fhat - F) ≤ c1 + c2 + c3 := by
  rw [hgap, add_assoc]
  calc abs (g1 + (g2 + g3))
      ≤ abs g1 + abs (g2 + g3) :=
        abs_add_le g1 (g2 + g3)
    _ ≤ abs g1 + (abs g2 + abs g3) := by
        have := abs_add_le g2 g3
        linarith
    _ ≤ c1 + c2 + c3 := by
        linarith [h1, h2, h3]

open Real in
/-- **Autoregressive error compounding (R465)**:
if the predictor is L-Lipschitz so each step maps
e_t ↦ e_{t+1} ≤ L·e_t, the H-step executed error
compounds geometrically (arXiv 2607.13612, Thm 2(ii),
L^{2H}-structure in the squared metric). -/
theorem compounding_bound (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, e (t+1) ≤ L * e t)
    (n : ℕ) : e n ≤ L^n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := he n
      calc e (n+1) ≤ L * e n := h1
        _ ≤ L * (L^n * e 0) := by
            exact mul_le_mul_of_nonneg_left ih hL
        _ = L^(n+1) * e 0 := by
            rw [pow_succ]; ring

/-- **Squared-metric compounding is L^(2H) (R465)**:
in the squared metric the same step recursion gives
e_H^2 ≤ (L^2)^H·e_0^2 — the O(L^(2H)) term of
arXiv 2607.13612, Thm 2(ii). -/
theorem compounding_sq (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, 0 ≤ e t)
    (hsq : ∀ t, e (t+1)^2 ≤ (L^2) * e t^2)
    (n : ℕ) : e n^2 ≤ (L^2)^n * e 0^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := hsq n
      have hL2 : (0:ℝ) ≤ L^2 := by nlinarith [hL]
      calc e (n+1)^2 ≤ L^2 * e n^2 := h1
        _ ≤ L^2 * ((L^2)^n * e 0^2) := by
            exact mul_le_mul_of_nonneg_left ih hL2
        _ = (L^2)^(n+1) * e 0^2 := by
            rw [pow_succ]; ring

open Finset Real in
/-- **Mutual information is nonnegative (R466)**:
I(X;Y) = KL(ρ ‖ μ₁×μ₂) ≥ 0 — the information a
joint distribution carries about the dependence
of its marginals never decreases below zero
(direct R447 application; equivalent to R459). -/
theorem mutual_info_nonneg {V W : Type*} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W]
    [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (0:ℝ) ≤ ∑ p : V × W, ρ p * Real.log
      (ρ p / ((∑ w : W, ρ (p.1, w))
        * (∑ v : V, ρ (v, p.2)))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  set μ₂ : W → ℝ := fun w => ∑ v : V, ρ (v, w) with hμ₂
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  have hμ₂pos : ∀ w, 0 < μ₂ w := by
    intro w
    have := Finset.sum_pos (fun v _ => hρ (v, w))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [hμ₂]; exact this
  set γ : V × W → ℝ := fun p => μ₁ p.1 * μ₂ p.2 with hγ
  have hγpos : ∀ p, 0 < γ p := fun p => by
    rw [hγ]; exact mul_pos (hμ₁pos p.1) (hμ₂pos p.2)
  have hμ₁s : ∑ v : V, μ₁ v = 1 := by
    rw [hμ₁, ← Fintype.sum_prod_type]; exact hρ1
  have hμ₂s : ∑ w : W, μ₂ w = 1 := by
    rw [hμ₂, Finset.sum_comm, ← Fintype.sum_prod_type]; exact hρ1
  have hγ1 : ∑ p : V × W, γ p = 1 := by
    show ∑ p : V × W, μ₁ p.1 * μ₂ p.2 = 1
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, μ₁ (v, w).1 * μ₂ (v, w).2 = μ₁ v := by
      intro v
      simp only []
      rw [← Finset.mul_sum, hμ₂s, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    exact hμ₁s
  -- the KL expression is definitionally the one in R447
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  exact hKL

/-- **EFE ceiling (R466)**: expected free energy
decomposes as G = P − I with pragmatic value P and
epistemic (information) part I ≥ 0; hence the EFE
never exceeds the pragmatic value — the
state-epistemic gap is exactly the mutual
information (arXiv 2607.13612, Prop 6 structure). -/
theorem efe_ceiling (G P I : ℝ)
    (hdecomp : G = P - I) (hI : 0 ≤ I) :
    G ≤ P := by
  linarith

open Real in
/-- **Amortised EFE policy guarantee (R467)**: if the
learned surrogate Ĝ uniformly approximates the true
expected free energy within slack c, the policy
minimising Ĝ executes within 2c of the optimum
(arXiv 2607.13612, Prop 7 structure). -/
theorem amortized_policy_bound {Pol : Type*}
    (Ghat G : Pol → ℝ) (pih pis : Pol) (c : ℝ)
    (happrox : ∀ pi, abs (Ghat pi - G pi) ≤ c)
    (hmin : ∀ pi, Ghat pih ≤ Ghat pi) :
    G pih ≤ G pis + 2 * c := by
  have hA : ∀ pi : Pol, Ghat pi - G pi ≤ c :=
    fun pi => (abs_le.mp (happrox pi)).2
  have hB : ∀ pi : Pol, G pi - Ghat pi ≤ c :=
    fun pi => by
      have h := abs_le.mp (happrox pi)
      linarith
  have h3 := hmin pis
  linarith [hA pih, hA pis, hB pih]

open Finset Real in
/-- **TV ≤ положительная
часть KL (R469)**:
(1/2)·Σ|p−q| ≤
Σ_{v: q<p} p·ln(p/q).
Механика: расщепление
Σ|p−q| = 2·Σ_A(p−q)
(дополнение меняет
знак) + per-v ln u ≥ 1−1/u
с u = q/p на A.
ВАЖНО: линейное
KL ≥ TV НЕВЕРНО
(контрпример p=(0.9,0.1),
q=(0.5,0.5): KL=0.368 <
TV=0.4; Пинскер требует √).
Кирпич
к Пинскеру. -/
theorem tv_le_pos_part_kl {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * (∑ v : V, |p v - q v|)
      ≤ ∑ v ∈ Finset.filter (fun v => q v < p v) Finset.univ,
        p v * Real.log (p v / q v) := by
  set A : Finset V := Finset.filter (fun v => q v < p v) Finset.univ with hA
  -- per-v on A: p - q <= p ln(p/q)
  have hpt : ∀ v ∈ A, p v - q v ≤ p v * Real.log (p v / q v) := by
    intro v hv
    have hlt : q v < p v := (Finset.mem_filter.mp hv).2
    have h1 : Real.log (q v / p v) ≤ q v / p v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq v) (hp v))
    have h2 : Real.log (p v / q v) = -(Real.log (q v / p v)) := by
      rw [Real.log_div (hp v).ne' (hq v).ne',
        Real.log_div (hq v).ne' (hp v).ne']
      ring
    rw [h2]
    have h3 : p v * (q v / p v) = q v := by
      field_simp [(hp v).ne']
    nlinarith [h1, h3, hp v]
  -- split: sum |p - q| = 2 * sum_A (p - q)
  have hsplit : ∑ v : V, |p v - q v| = 2 * (∑ v ∈ A, (p v - q v)) := by
    have h0 : ∑ v : V, (p v - q v) = 0 := by
      rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
    have hcompl : ∑ v ∈ Aᶜ, (p v - q v) = -(∑ v ∈ A, (p v - q v)) := by
      have hc := Finset.sum_add_sum_compl A (fun v => p v - q v)
      rw [show ∑ i ∈ A, (fun v => p v - q v) i
        = ∑ v ∈ A, (p v - q v) from rfl] at hc
      rw [h0] at hc
      linarith
    have habsA : ∀ v ∈ A, |p v - q v| = p v - q v := by
      intro v hv
      exact abs_of_pos (sub_pos.mpr (Finset.mem_filter.mp hv).2)
    have habsC : ∀ v ∈ Aᶜ, |p v - q v| = -(p v - q v) := by
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact abs_of_nonpos (by linarith)
    have hsplit2 : ∑ v : V, |p v - q v|
        = (∑ v ∈ A, |p v - q v|) + (∑ v ∈ Aᶜ, |p v - q v|) := by
      have h := Finset.sum_add_sum_compl A (fun v => |p v - q v|)
      simpa using h.symm
    rw [hsplit2]
    rw [Finset.sum_congr rfl (fun v hv => habsA v hv)]
    rw [Finset.sum_congr rfl (fun v hv => habsC v hv)]
    rw [Finset.sum_neg_distrib, hcompl]
    ring
  rw [hsplit]
  -- sum_A (p-q) <= sum_A (p ln) <= full sum
  have hnonneg : ∀ v ∈ A, (0:ℝ) ≤ p v * Real.log (p v / q v) := by
    intro v hv
    have hlt : q v < p v := (Finset.mem_filter.mp hv).2
    have hlog : (0:ℝ) ≤ Real.log (p v / q v) := by
      have : (1:ℝ) < p v / q v :=
        (one_lt_div (hq v)).mpr hlt
      exact le_of_lt (log_pos this)
    exact mul_nonneg (hp v).le hlog
  calc (1:ℝ)/2 * (2 * (∑ v ∈ A, (p v - q v)))
      = ∑ v ∈ A, (p v - q v) := by ring
    _ ≤ ∑ v ∈ A, p v * Real.log (p v / q v) :=
      Finset.sum_le_sum hpt

open Finset Real in
/-- **Бхаттачаря
≤ 1 (R470)**:
Σ√(p·q) ≤ 1 — Коши
(sum_mul_sq_le_sq_mul_sq
в форме квадратов с
sq_sqrt-свёрткой).
Кирпич Пинскер-цепи
(BC→KL). -/
theorem bhattacharyya_cauchy {V : Type*} [Fintype V]
    (p q : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v)
    (hp1 : ∑ v : V, p v = 1) (hq1 : ∑ v : V, q v = 1) :
    (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)) ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    Finset.univ (fun v => Real.sqrt (p v)) (fun v => Real.sqrt (q v))
  have hsq : (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)) ^ 2
      ≤ (∑ v : V, p v) * (∑ v : V, q v) := by
    have h1 : (∑ v : V, Real.sqrt (p v) ^ 2) = ∑ v : V, p v := by
      exact Finset.sum_congr rfl (fun v _ => by
        rw [sq_sqrt (hp v)])
    have h2 : (∑ v : V, Real.sqrt (q v) ^ 2) = ∑ v : V, q v := by
      exact Finset.sum_congr rfl (fun v _ => by
        rw [sq_sqrt (hq v)])
    rw [h1, h2] at h
    simpa [pow_two] using h
  have hge : (0:ℝ) ≤ ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hp1' : (0:ℝ) ≤ (∑ v : V, p v) * (∑ v : V, q v) := by
    rw [hp1, hq1]; norm_num
  rw [hp1, hq1] at hsq
  norm_num at hsq
  norm_num at hsq
  by_contra hc
  have hgt : (1:ℝ) < ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
    push_neg at hc
    exact hc
  have h2 : (1:ℝ) < (∑ v : V, Real.sqrt (p v)
      * Real.sqrt (q v)) ^ 2 := by
    nlinarith [hgt]
  linarith [abs_le.mp hsq |>.2]

open Finset Real in
/-- **1 − BC ≤ KL/2 (R471)**:
1 − Σ√(p·q) ≤
(1/2)·Σp·ln(p/q).
Per-v ядро: с t := √(p/q):
p − √(pq) = √(pq)(t−1),
(1/2)p·ln(p/q) = √(pq)·t·ln t,
и t−1 ≤ t·ln t (из
ln u ≤ u−1 с u := 1/t).
С R470 (BC ≤ 1) замыкает
Пинскер-цепь: 1−BC ≤ KL/2. -/
theorem one_minus_bc_le_half_kl {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  have tlem : ∀ t : ℝ, 0 < t → t - 1 ≤ t * Real.log t := by
    intro t ht
    have h1 : Real.log t⁻¹ ≤ t⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    have h2 : t * Real.log t⁻¹ ≤ t * (t⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
    have h3 : t * (t⁻¹ - 1) = 1 - t := by
      field_simp
    have h6 : t * Real.log t = -(t * Real.log t⁻¹) := by
      rw [Real.log_inv t]; ring
    linarith
  have hsplit : 1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      = ∑ v : V, (p v - Real.sqrt (p v) * Real.sqrt (q v)) := by
    have h1 : ∑ v : V, (p v - Real.sqrt (p v) * Real.sqrt (q v))
        = (∑ v : V, p v)
          - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) :=
      by rw [Finset.sum_sub_distrib]
    rw [h1, hp1]
  have hsqpv : ∀ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      * Real.sqrt (p v / q v) = p v := by
    intro v
    have h1 : Real.sqrt (p v) * Real.sqrt (q v)
        = Real.sqrt (p v * q v) :=
      (Real.sqrt_mul (hp v).le (q v)).symm
    have h2 : Real.sqrt (p v * q v) * Real.sqrt (p v / q v)
        = Real.sqrt (p v * q v * (p v / q v)) :=
      (Real.sqrt_mul (mul_nonneg (hp v).le (hq v).le)
        (p v / q v)).symm
    rw [h1, h2]
    have hfe : p v * q v * (p v / q v) = p v * p v := by
      field_simp [(hp v).ne', (hq v).ne']
    rw [hfe, ← sq (p v), Real.sqrt_sq_eq_abs, abs_of_pos (hp v)]
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  set t : ℝ := Real.sqrt (p v / q v) with ht_def
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos (hp v) (hq v))
  have hsq := hsqpv v
  have hte : p v / q v = t ^ 2 :=
    (Real.sq_sqrt (div_nonneg (hp v).le (hq v).le)).symm
  have hlogt : Real.log (p v / q v) = 2 * Real.log t := by
    rw [hte, show t ^ 2 = t * t from sq t,
      Real.log_mul (ne_of_gt htpos) (ne_of_gt htpos)]
    ring
  have hspos : (0:ℝ) < Real.sqrt (p v) * Real.sqrt (q v) :=
    mul_pos (Real.sqrt_pos.mpr (hp v)) (Real.sqrt_pos.mpr (hq v))
  have step1 : p v - Real.sqrt (p v) * Real.sqrt (q v)
      = Real.sqrt (p v) * Real.sqrt (q v) * (t - 1) := by
    have h2' : Real.sqrt (p v) * Real.sqrt (q v) * (t - 1)
        = Real.sqrt (p v) * Real.sqrt (q v) * t
          - Real.sqrt (p v) * Real.sqrt (q v) := by ring
    rw [h2', hsq]
  have hpv : p v * Real.log t
      = (Real.sqrt (p v) * Real.sqrt (q v) * t) * Real.log t := by
    rw [hsq]
  have step2 : (1/2) * (p v * Real.log (p v / q v))
      = Real.sqrt (p v) * Real.sqrt (q v) * (t * Real.log t) := by
    rw [hlogt]
    rw [show (1/2:ℝ) * (p v * (2 * Real.log t))
        = p v * Real.log t from by ring, hpv]
    ring
  rw [step1, step2]
  have h8 := tlem t htpos
  nlinarith

open Finset Real in
/-- **Пинскер,
слабая √-форма
(R472)**:
(1/2)·Σ|p−q| ≤
√(KL).
Цепь: тождество
|p−q| = |√p−√q|·(√p+√q)
+ Коши (суммы
квадратов) →
Σ|p−q| ² ≤
(2−2BC)(2+2BC) =
4(1−BC)(1+BC) ≤
8(1−BC) ≤ 4·KL
(R470: BC ≤ 1; R471:
1−BC ≤ KL/2) →
TV ≤ √(KL).
Выборочный код:
K на R469–R471.
Точная форма
(KL/2) требует
двоич-редукций
(DPI + калкулус) —
не в этом юните. -/
theorem pinsker_sqrt_kl {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, |p v - q v|
      ≤ Real.sqrt (∑ v : V, p v * Real.log (p v / q v)) := by
  set KL : ℝ := ∑ v : V, p v * Real.log (p v / q v) with hKL
  set BC : ℝ := ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) with hBC
  set s : V → ℝ := fun v => Real.sqrt (p v) - Real.sqrt (q v) with hs
  set t : V → ℝ := fun v => Real.sqrt (p v) + Real.sqrt (q v) with htt
  -- per-v: |p - q| = |s| * t
  have hv : ∀ v, |p v - q v| = |s v| * t v := by
    intro v
    have h1 : p v - q v = (Real.sqrt (p v) - Real.sqrt (q v))
        * (Real.sqrt (p v) + Real.sqrt (q v)) := by
      rw [show (Real.sqrt (p v) - Real.sqrt (q v))
          * (Real.sqrt (p v) + Real.sqrt (q v))
          = Real.sqrt (p v) ^ 2 - Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    rw [h1, abs_mul, abs_of_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  -- Cauchy
  have hC2 : (∑ v : V, |p v - q v|) ^ 2
      ≤ (∑ v : V, |s v| ^ 2) * (∑ v : V, t v ^ 2) := by
    have hC := Finset.sum_mul_sq_le_sq_mul_sq
      Finset.univ (fun v => |s v|) t
    rw [Finset.sum_congr rfl (fun v _ => (hv v).symm)] at hC
    exact hC
  -- sum of squares of s: 2 - 2 BC
  have hA : ∑ v : V, |s v| ^ 2 = 2 - 2 * BC := by
    have h2 : ∀ v : V, |s v| ^ 2 = p v + q v
        - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [sq_abs, show s v ^ 2 = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  -- sum of squares of t: 2 + 2 BC
  have hB : ∑ v : V, t v ^ 2 = 2 + 2 * BC := by
    have h2 : ∀ v : V, t v ^ 2 = p v + q v
        + 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [show t v ^ 2 = Real.sqrt (p v) ^ 2
          + 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  rw [hA, hB] at hC2
  -- BC <= 1 and chain
  have hBC1 : BC ≤ 1 :=
    bhattacharyya_cauchy p q (fun v => (hp v).le)
      (fun v => (hq v).le) hp1 hq1
  have hR : 1 - BC ≤ KL / 2 := by
    have := one_minus_bc_le_half_kl p q hp hp1 hq hq1
    rw [← hBC] at this
    linarith
  have h4 : (1 - BC) * (1 + BC) ≤ 2 * (1 - BC) := by
    by_contra hc
    push_neg at hc
    nlinarith [hBC1, sub_nonneg.mpr hBC1]
  have hM : 2 * (KL / 2) = KL := by field_simp
  have i1 : 2 * (1 - BC) ≤ KL := by linarith [hR, hM]
  have hstep : (∑ v : V, |p v - q v|) ^ 2 ≤ 4 * KL := by
    have hc := hC2
    have e1 : (2 - 2 * BC) * (2 + 2 * BC)
        = 4 * ((1 - BC) * (1 + BC)) := by ring
    rw [e1] at hc
    have h5 : 4 * ((1 - BC) * (1 + BC)) ≤ 4 * (2 * (1 - BC)) := by
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    linarith [hc, h5, i1]
  -- final sqrt step
  have hS : (0:ℝ) ≤ ∑ v : V, |p v - q v| := by
    apply Finset.sum_nonneg
    intro v _
    exact abs_nonneg _
  have hs2 : (0:ℝ) ≤ (1/2) * ∑ v : V, |p v - q v| := by
    linarith [hS]
  have hS2 : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2 ≤ KL := by
    have e2 : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
        = (∑ v : V, |p v - q v|) ^ 2 / 4 := by ring
    linarith [hstep, e2]
  exact Real.le_sqrt_of_sq_le hS2

open Finset Real in
/-- **Дуальная
характеризация
TV (R473)**:
для любой 0 ≤ f ≤ 1
|E_p f − E_q f| ≤ TV.
Верх: расщепление
Σ(p−q)f →
Σ_A(p−q)f + 0 ≤
Σ_A(p−q) = TV;
низ — заменой
f → 1−f.
PAC-Bayes-кирпич (дуальность
TV). -/
theorem tv_dual_abs {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V → ℝ) (f : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hf0 : ∀ v, 0 ≤ f v) (hf1 : ∀ v, f v ≤ 1) :
    |∑ v : V, p v * f v - ∑ v : V, q v * f v|
      ≤ (1/2) * ∑ v : V, |p v - q v| := by
  set A : Finset V := Finset.filter (fun v => q v < p v) Finset.univ with hA
  -- TV split: (1/2) sum |p-q| = sum_A (p - q)
  have hT : (1/2) * ∑ v : V, |p v - q v|
      = ∑ v ∈ A, (p v - q v) := by
    have h0 : ∑ v : V, (p v - q v) = 0 := by
      rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
    have hcompl : ∑ v ∈ Aᶜ, (p v - q v) = -(∑ v ∈ A, (p v - q v)) := by
      have hc := Finset.sum_add_sum_compl A (fun v => p v - q v)
      rw [show ∑ i ∈ A, (fun v => p v - q v) i
        = ∑ v ∈ A, (p v - q v) from rfl] at hc
      rw [h0] at hc
      linarith
    have habsA : ∀ v ∈ A, |p v - q v| = p v - q v := by
      intro v hv
      exact abs_of_pos (sub_pos.mpr (Finset.mem_filter.mp hv).2)
    have habsC : ∀ v ∈ Aᶜ, |p v - q v| = -(p v - q v) := by
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact abs_of_nonpos (by linarith)
    have hsplit2 : ∑ v : V, |p v - q v|
        = (∑ v ∈ A, |p v - q v|) + (∑ v ∈ Aᶜ, |p v - q v|) := by
      have h := Finset.sum_add_sum_compl A (fun v => |p v - q v|)
      simpa using h.symm
    rw [hsplit2]
    rw [Finset.sum_congr rfl (fun v hv => habsA v hv),
      Finset.sum_congr rfl (fun v hv => habsC v hv)]
    rw [Finset.sum_neg_distrib, hcompl]
    ring
  -- upper bound for any 0<=f<=1
  have hupper : ∀ g : V → ℝ, (∀ v, 0 ≤ g v) → (∀ v, g v ≤ 1) →
      ∑ v : V, p v * g v - ∑ v : V, q v * g v
        ≤ (1/2) * ∑ v : V, |p v - q v| := by
    intro g hg0 hg1
    have hd : ∑ v : V, p v * g v - ∑ v : V, q v * g v
        = ∑ v : V, (p v - q v) * g v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hup1 : ∑ v ∈ A, (p v - q v) * g v
        ≤ ∑ v ∈ A, (p v - q v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (mul_le_mul_of_nonneg_left (hg1 v)
        (le_of_lt (sub_pos.mpr (Finset.mem_filter.mp hv).2))).trans
        (by rw [mul_one])
    have hup2 : ∑ v ∈ Aᶜ, (p v - q v) * g v ≤ 0 := by
      apply Finset.sum_nonpos
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact le_trans (mul_le_mul_of_nonneg_right
        (sub_nonpos.mpr hle) (hg0 v)) (by rw [zero_mul])
    calc ∑ v : V, p v * g v - ∑ v : V, q v * g v
        = ∑ v : V, (p v - q v) * g v := hd
      _ = (∑ v ∈ A, (p v - q v) * g v)
          + (∑ v ∈ Aᶜ, (p v - q v) * g v) := by
          have h := Finset.sum_add_sum_compl A
            (fun v => (p v - q v) * g v)
          linarith
      _ ≤ ∑ v ∈ A, (p v - q v) + 0 := by linarith
      _ = (1/2) * ∑ v : V, |p v - q v| := by
          rw [add_zero]; exact hT.symm
  have hup := hupper f hf0 hf1
  -- lower bound via 1 - f
  have hf0' : ∀ v, 0 ≤ 1 - f v := by intro v; linarith [hf1 v]
  have hf1' : ∀ v, 1 - f v ≤ 1 := by intro v; linarith [hf0 v]
  have hneg := hupper (fun v => 1 - f v) hf0' hf1'
  have hd2 : ∑ v : V, p v * (1 - f v) - ∑ v : V, q v * (1 - f v)
      = -(∑ v : V, p v * f v - ∑ v : V, q v * f v) := by
    have e3 : ∀ v : V, p v * (1 - f v) = p v - p v * f v :=
      fun v => by ring
    have e4 : ∀ v : V, q v * (1 - f v) = q v - q v * f v :=
      fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => e3 v),
      Finset.sum_congr rfl (fun v _ => e4 v),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hp1, hq1]
    linarith
  rw [abs_le]
  exact ⟨by linarith [hd2, hneg], hup⟩

open Finset Real in
/-- **−ln BC ≤ KL/2
(R474)**:
−ln Σ√(p·q) ≤
(1/2)·Σp·ln(p/q).
Log-sum R451 с
парой a := p,
b := √(p·q)
(LHS = ln(1/BC)); per-v:
p/√(pq) = √(p/q),
т.е. ln(p/√(pq)) =
(1/2)ln(p/q) (log_sqrt).
Эквив: BC ≥
e^{−KL/2} — кирпич
Бретаньоль–Юбера. -/
theorem neg_log_bc_le_half_kl {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hp1 : ∑ v : V, p v = 1) :
    -Real.log (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v))
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  have hper : ∀ v : V, p v / (Real.sqrt (p v) * Real.sqrt (q v))
      = Real.sqrt (p v / q v) := by
    intro v
    have hsq : Real.sqrt (p v) * Real.sqrt (p v) = p v := by
      rw [← sq (Real.sqrt (p v))]
      exact sq_sqrt (hp v).le
    have e3 : p v / (√(p v) * √(q v))
        = (Real.sqrt (p v) * Real.sqrt (p v))
          / (Real.sqrt (p v) * Real.sqrt (q v)) := by
      nth_rewrite 1 [← hsq]
      rfl
    have e4 : (Real.sqrt (p v) * Real.sqrt (p v))
        / (Real.sqrt (p v) * Real.sqrt (q v))
        = Real.sqrt (p v) / Real.sqrt (q v) := by
      exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr (hp v)).ne'
    exact e3.trans ((e4.trans
      (Real.sqrt_div (hp v).le (q v)).symm))
  have hlogper : ∀ v : V,
      Real.log (p v / (Real.sqrt (p v) * Real.sqrt (q v)))
      = (1/2) * Real.log (p v / q v) := by
    intro v
    rw [hper v, Real.log_sqrt ((div_nonneg (hp v).le (hq v).le))]
    ring
  have hBCpos : (0:ℝ) < ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) :=
    Finset.sum_pos (fun v _ => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have h := log_sum_ineq p
    (fun v => Real.sqrt (p v) * Real.sqrt (q v))
    hp (fun v => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
  simp only [hlogper] at h
  have hrhs : (∑ v : V, p v) * Real.log ((∑ v : V, p v)
      / (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)))
      = Real.log (1 / (∑ v : V, Real.sqrt (p v)
        * Real.sqrt (q v))) := by
    rw [hp1, one_mul]
  rw [hrhs] at h
  rw [← Real.log_inv, inv_eq_one_div]
  have hconv : ∑ x : V, p x * (1/2 * Real.log (p x / q x))
      = (1/2) * ∑ x : V, p x * Real.log (p x / q x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [← hconv]
  exact h

open Finset Real in
/-- **Бретаньоль–
Юбер (R475)**:
TV ≤
√(1−e^{−KL})
.
Цепь: Коши
(R472-механика) →
Σ|p−q|² ≤
4(1−BC²);
R474: BC ≥
e^{−KL/2} →
1−BC² ≤
1−e^{−KL}.
Тиснее R472 при
большом KL
(√(1−e^{−KL}) ≤ 1). -/
theorem tv_le_sqrt_one_minus_exp {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, |p v - q v|
      ≤ Real.sqrt (1 - Real.exp
        (-(∑ v : V, p v * Real.log (p v / q v)))) := by
  set KL : ℝ := ∑ v : V, p v * Real.log (p v / q v) with hKL
  set BC : ℝ := ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) with hBC
  set s : V → ℝ := fun v => Real.sqrt (p v) - Real.sqrt (q v) with hs
  set t : V → ℝ := fun v => Real.sqrt (p v) + Real.sqrt (q v) with htt
  have hv : ∀ v, |p v - q v| = |s v| * t v := by
    intro v
    have h1 : p v - q v = (Real.sqrt (p v) - Real.sqrt (q v))
        * (Real.sqrt (p v) + Real.sqrt (q v)) := by
      rw [show (Real.sqrt (p v) - Real.sqrt (q v))
          * (Real.sqrt (p v) + Real.sqrt (q v))
          = Real.sqrt (p v) ^ 2 - Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    rw [h1, abs_mul, abs_of_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hC2 : (∑ v : V, |p v - q v|) ^ 2
      ≤ (∑ v : V, |s v| ^ 2) * (∑ v : V, t v ^ 2) := by
    have hC := Finset.sum_mul_sq_le_sq_mul_sq
      Finset.univ (fun v => |s v|) t
    rw [Finset.sum_congr rfl (fun v _ => (hv v).symm)] at hC
    exact hC
  have hA : ∑ v : V, |s v| ^ 2 = 2 - 2 * BC := by
    have h2 : ∀ v : V, |s v| ^ 2 = p v + q v
        - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [sq_abs, show s v ^ 2 = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  have hB : ∑ v : V, t v ^ 2 = 2 + 2 * BC := by
    have h2 : ∀ v : V, t v ^ 2 = p v + q v
        + 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [show t v ^ 2 = Real.sqrt (p v) ^ 2
          + 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  rw [hA, hB] at hC2
  have e1 : (2 - 2 * BC) * (2 + 2 * BC) = 4 * (1 - BC ^ 2) := by ring
  rw [e1] at hC2
  -- BC >= exp(-KL/2)
  have hBCpos : (0:ℝ) < BC := by
    rw [hBC]
    exact Finset.sum_pos (fun v _ => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hR74 := neg_log_bc_le_half_kl p q hp hq hp1
  rw [← hBC] at hR74
  rw [← hKL] at hR74
  have h2 : Real.exp (-(KL / 2)) ≤ BC := by
    have h1 : -(KL / 2) ≤ Real.log BC := by linarith [hR74]
    have h2p := Real.exp_le_exp.mpr h1
    rw [Real.exp_log hBCpos] at h2p
    exact h2p
  have e1b : (Real.exp (-(KL / 2))) ^ 2 = Real.exp (-(KL)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    linarith
  have hb2 : (Real.exp (-(KL / 2))) ^ 2 ≤ BC ^ 2 := by
    have hBCe : (0:ℝ) ≤ BC + Real.exp (-(KL / 2)) := by
      linarith [hBCpos, Real.exp_pos (-(KL / 2))]
    have hmul : (BC - Real.exp (-(KL / 2)))
        * (BC + Real.exp (-(KL / 2))) ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr h2) hBCe
    have e3r : (BC - Real.exp (-(KL / 2)))
        * (BC + Real.exp (-(KL / 2)))
        = BC ^ 2 - (Real.exp (-(KL / 2))) ^ 2 := by ring
    rw [e3r] at hmul
    linarith
  have e2r : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
      = (∑ v : V, |p v - q v|) ^ 2 / 4 := by ring
  have hTV : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
      ≤ 1 - Real.exp (-(KL)) := by
    linarith [hC2, e2r, hb2, e1b]
  exact Real.le_sqrt_of_sq_le hTV

open Finset Real in
/-- **Совместная
выпуклость KL
(R476)**: для c ∈ (0,1):
KL(c·p₁+(1−c)·p₂
‖ c·q₁+(1−c)·q₂)
≤
c·KL(p₁‖q₁) +
(1−c)·KL(p₂‖q₂).
Per-v — двухточечный
log-sum: R451 на
Fin 2 с парами
(c·p₁v, (1−c)·p₂v) и
(c·q₁v, (1−c)·q₂v);
разбавение диляций
mul_div_mul_left. -/
theorem kl_joint_convex {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p₁ p₂ q₁ q₂ : V → ℝ) (c : ℝ)
    (hp₁ : ∀ v, 0 < p₁ v) (hp₁1 : ∑ v : V, p₁ v = 1)
    (hp₂ : ∀ v, 0 < p₂ v) (hp₂1 : ∑ v : V, p₂ v = 1)
    (hq₁ : ∀ v, 0 < q₁ v) (hq₂ : ∀ v, 0 < q₂ v)
    (hc0 : 0 < c) (hc1 : c < 1) :
    ∑ v : V, (c * p₁ v + (1 - c) * p₂ v)
        * Real.log ((c * p₁ v + (1 - c) * p₂ v)
          / (c * q₁ v + (1 - c) * q₂ v))
      ≤ (1 - c) * (∑ v : V, p₂ v * Real.log (p₂ v / q₂ v))
        + c * (∑ v : V, p₁ v * Real.log (p₁ v / q₁ v)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have ha : ∀ i : Fin 2,
      0 < (fun i => if i = 0 then c * p₁ v else (1 - c) * p₂ v) i := by
    intro i
    by_cases hz : i = 0
    · simp only [hz, if_pos hz]
      exact mul_pos hc0 (hp₁ v)
    · simp only [if_neg hz]
      exact mul_pos (by linarith) (hp₂ v)
  have hb : ∀ i : Fin 2,
      0 < (fun i => if i = 0 then c * q₁ v else (1 - c) * q₂ v) i := by
    intro i
    by_cases hz : i = 0
    · simp only [hz, if_pos hz]
      exact mul_pos hc0 (hq₁ v)
    · simp only [if_neg hz]
      exact mul_pos (by linarith) (hq₂ v)
  have hv := log_sum_ineq
    (fun i => if i = 0 then c * p₁ v else (1 - c) * p₂ v)
    (fun i => if i = 0 then c * q₁ v else (1 - c) * q₂ v)
    ha hb
  simp only [Fin.sum_univ_two] at hv
  simp only [if_pos rfl, if_neg (by omega : ¬((1 : Fin 2) = 0)),
    Fin.isValue, reduceIte] at hv
  rw [mul_div_mul_left _ _ hc0.ne',
    mul_div_mul_left _ _ (by linarith)] at hv
  have hv2 : (1 - c) * (p₂ v * Real.log (p₂ v / q₂ v))
      + c * (p₁ v * Real.log (p₁ v / q₁ v))
      = c * p₁ v * Real.log (p₁ v / q₁ v)
        + (1 - c) * p₂ v * Real.log (p₂ v / q₂ v) := by
    ring
  rw [hv2]
  linarith

open Finset Real in
/-- **Донскер–
Варадхан,
нижняя грань
(R477)**: KL(p‖q) ≥
E_p f −
ln(Σq·e^f).
Механика: софтмакс
r := q·e^f/Z,
KL(p‖r) ≥ 0 (R447),
per-v
ln(p/r) =
ln(p/q) − f + ln Z. -/
theorem kl_variational_lower {V : Type*} [Fintype V] [Nonempty V]
    (p q f : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    ∑ v : V, p v * Real.log (p v / q v)
      ≥ ∑ v : V, p v * f v
        - Real.log (∑ v : V, q v * Real.exp (f v)) := by
  set Z : ℝ := ∑ v : V, q v * Real.exp (f v) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => mul_pos (hq v) (Real.exp_pos (f v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set r : V → ℝ := fun v => q v * Real.exp (f v) / Z with hr
  have hrpos : ∀ v, 0 < r v := fun v =>
    div_pos (mul_pos (hq v) (Real.exp_pos (f v))) hZpos
  have hS2 : (∑ v : V, q v * Real.exp (f v)) = Z := hZ.symm
  have hr1 : ∑ v : V, r v = 1 := by
    have e1 : ∑ v : V, r v
        = ∑ v : V, (q v * Real.exp (f v) / Z) := rfl
    rw [e1, ← Finset.sum_div, hS2]
    exact div_self hZpos.ne'
  have hkl := finite_kl_nonneg p r hp hp1 hrpos hr1
  have hper : ∀ v : V, Real.log (p v / r v)
      = Real.log (p v / q v) - f v + Real.log Z := by
    intro v
    have e1 : p v / r v
        = p v * Z / (q v * Real.exp (f v)) := by
      rw [hr]
      field_simp
    rw [e1, Real.log_div (mul_pos (hp v) hZpos).ne'
      (mul_pos (hq v) (Real.exp_pos (f v))).ne',
      Real.log_mul (hp v).ne' hZpos.ne',
      Real.log_div (hp v).ne' (hq v).ne']
    rw [Real.log_mul (hq v).ne'
      (Real.exp_pos (f v)).ne', Real.log_exp (f v)]
    ring
  have hper2 : ∀ v : V, p v * Real.log (p v / r v)
      = p v * Real.log (p v / q v) - p v * f v
        + p v * Real.log Z := by
    intro v
    rw [hper v]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hper2 v)] at hkl
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hkl
  have hZsum : ∑ v : V, p v * Real.log Z = Real.log Z := by
    rw [Finset.sum_congr rfl
      (fun v _ => mul_comm (p v) (Real.log Z)),
      ← Finset.mul_sum, hp1, mul_one]
  rw [hZsum] at hkl
  linarith

open Finset Real in
/-- **PAC-Чернофф
для событий
(R478)**: при
KL(p‖q) ≤ κ:
Σ_{v∈s} p ≤ κ +
ln(1+(e−1)·q(s))
— одложенная
софтмакс-форма
R477 с f :=
индикатором s;
ключевой
PAC-Bayes-кирпич. -/
theorem pac_chernoff_events {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ) (s : Finset V) (κ : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hκ : ∑ v : V, p v * Real.log (p v / q v) ≤ κ) :
    ∑ v ∈ s, p v
      ≤ κ + Real.log (1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v) := by
  have hR := kl_variational_lower p q (fun v => if v ∈ s then (1:ℝ) else 0)
    hp hp1 hq hq1
  -- per-v equations
  have hpe1 : ∀ v ∈ s, p v * (if v ∈ s then (1:ℝ) else 0) = p v := by
    intro v hv; rw [if_pos hv, mul_one]
  have hpe2 : ∀ v ∈ sᶜ, p v * (if v ∈ s then (1:ℝ) else 0) = 0 := by
    intro v hv; rw [if_neg (Finset.mem_compl.mp hv), mul_zero]
  have hqe1 : ∀ v ∈ s,
      q v * Real.exp (if v ∈ s then (1:ℝ) else 0)
      = Real.exp 1 * q v := by
    intro v hv; rw [if_pos hv]; ring
  have hqe2 : ∀ v ∈ sᶜ,
      q v * Real.exp (if v ∈ s then (1:ℝ) else 0) = q v := by
    intro v hv
    rw [if_neg (Finset.mem_compl.mp hv), Real.exp_zero, mul_one]
  -- E_p[indicator] = p(s)
  have hEta : ∑ v : V, p v * (if v ∈ s then (1:ℝ) else 0)
      = ∑ v ∈ s, p v := by
    have h := Finset.sum_add_sum_compl s
      (fun v => p v * (if v ∈ s then (1:ℝ) else 0))
    rw [Finset.sum_congr rfl (fun v hv => hpe1 v hv)] at h
    have hX : ∑ v ∈ sᶜ, p v * (if v ∈ s then (1:ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun v hv => by rw [hpe2 v hv])
    linarith [h, hX]
  -- Z = 1 + (e-1) q(s)
  have hZeta : ∑ v : V, q v * Real.exp (if v ∈ s then (1:ℝ) else 0)
      = 1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v := by
    have h := Finset.sum_add_sum_compl s
      (fun v => q v * Real.exp (if v ∈ s then (1:ℝ) else 0))
    rw [Finset.sum_congr rfl (fun v hv => hqe1 v hv),
      Finset.sum_congr rfl (fun v hv => hqe2 v hv),
      ← Finset.mul_sum] at h
    have hC : ∑ v ∈ sᶜ, q v = 1 - ∑ v ∈ s, q v := by
      have hc := Finset.sum_add_sum_compl s (fun v => q v)
      rw [show ∑ i ∈ s, (fun v => q v) i = ∑ v ∈ s, q v from rfl,
        show ∑ i ∈ sᶜ, (fun v => q v) i = ∑ v ∈ sᶜ, q v from rfl,
        hq1] at hc
      linarith
    have hRr : Real.exp 1 * ∑ v ∈ s, q v
        + (1 - ∑ v ∈ s, q v)
        = 1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v := by
      ring
    linarith [h, hC, hRr]
  rw [hEta, hZeta] at hR
  linarith [hR, hκ]

open Finset Real in
/-- **ТочностьДВ
(R479)**: sup Донскера
достигается: существует f
(f := ln(p/q)), для
которой KL(p‖q) ≤
E_p f − ln(Σq·e^f)
(с R477 — эквивалентность:
KL = sup_f
(E_p f − ln E_q e^f));
Z = Σq·(p/q) =
Σp = 1 через
exp_log и field_simp. -/
theorem kl_dv_attained {V : Type*} [Fintype V] [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    ∃ f : V → ℝ,
      ∑ v : V, p v * Real.log (p v / q v)
        ≤ ∑ v : V, p v * f v
          - Real.log (∑ v : V, q v * Real.exp (f v)) := by
  refine ⟨fun v => Real.log (p v / q v), ?_⟩
  have hZ : ∑ v : V, q v * Real.exp (Real.log (p v / q v)) = (1:ℝ) := by
    have e1 : ∀ v : V,
        q v * Real.exp (Real.log (p v / q v)) = p v := by
      intro v
      rw [Real.exp_log (div_pos (hp v) (hq v))]
      field_simp [(hq v).ne']
    rw [Finset.sum_congr rfl (fun v _ => e1 v), hp1]
  rw [hZ, Real.log_one]
  have hbe : ∑ v : V, p v * (fun v => Real.log (p v / q v)) v
      = ∑ v : V, p v * Real.log (p v / q v) := rfl
  rw [hbe, sub_zero]

open Finset Real in
/-- **Hellinger-кирпичи
(R480)**: H²(p,q) :=
(1/2)·Σ(√p−√q)²
= 1 − BC — точное
тождество (квадрат
разности корней
разворачивается
в p+q−2√(pq)); с R471
— мост H² ≤ KL/2. -/
theorem hellinger_sq_eq_one_minus_bc {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      = 1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
  have hper : ∀ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      = p v + q v - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
    intro v
    rw [show (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
        = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
          + Real.sqrt (q v) ^ 2 from by ring,
      sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hper v),
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp1, hq1]
  ring

theorem hellinger_le_half_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  rw [hellinger_sq_eq_one_minus_bc p q hp hp1 hq hq1]
  exact one_minus_bc_le_half_kl p q hp hp1 hq hq1

open Finset Real in
/-- **Чернофф-наклон
(R481)**: для любого c:
c·E_p g − ln E_q e^{c·g}
≤ KL(p‖q)
(инстанс R477 с
f := c·g — Cramér-
параметризация
функции моментов). -/
theorem kl_chernoff_tilt {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    c * ∑ v : V, p v * g v
      - Real.log (∑ v : V, q v * Real.exp (c * g v))
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hR := kl_variational_lower p q (fun v => c * g v) hp hp1 hq hq1
  have hconv : ∑ v : V, p v * (c * g v)
      = c * ∑ v : V, p v * g v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hconv] at hR
  exact hR

open Finset Real in
/-- **Конечный
Марков (R482)**:
для g ≥ 0 и t > 0:
t·p({g ≥ t}) ≤ E_p g
(фильтр {t ≤ g},
per-v p·t ≤ p·g,
подсумма → полная
сумма через
nonneg-расширение). -/
theorem markov_finite {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p g : V → ℝ) (t : ℝ)
    (hp : ∀ v, 0 < p v) (hg : ∀ v, 0 ≤ g v) (ht : 0 < t) :
    t * ∑ v ∈ Finset.filter (fun v => t ≤ g v) Finset.univ, p v
      ≤ ∑ v : V, p v * g v := by
  set s' : Finset V := Finset.filter (fun v => t ≤ g v) Finset.univ with hs'
  rw [Finset.mul_sum]
  have h1 : ∑ v ∈ s', t * p v ≤ ∑ v ∈ s', p v * g v := by
    apply Finset.sum_le_sum
    intro v hv
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Finset.mem_filter.mp hv).2 (le_of_lt (hp v))
  have h2 : ∑ v ∈ s', p v * g v ≤ ∑ v : V, p v * g v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun v _ _ => mul_nonneg (hp v).le (hg v))
  linarith

open Finset Real in
/-- **Чернофф
на событии
(R483)**: для λ > 0:
p({g ≥ t}) ≤
e^{−λt}·E_p e^{λg}
(марковский
R482 на
H := e^{λg}; эквивим
фильтров через
exp-монотонность). -/
theorem chernoff_event {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p g : V → ℝ) (hl t : ℝ)
    (hp : ∀ v, 0 < p v) (hltp : 0 < hl) :
    ∑ v ∈ Finset.filter (fun v => t ≤ g v) Finset.univ, p v
      ≤ (∑ v : V, p v * Real.exp (hl * g v)) / Real.exp (hl * t) := by
  set s₁ : Finset V := Finset.filter (fun v => t ≤ g v) Finset.univ with hs₁
  have hm := markov_finite p (fun v => Real.exp (hl * g v))
    (Real.exp (hl * t)) hp
    (fun v => Real.exp_nonneg _) (Real.exp_pos _)
  have hiff : ∀ v : V,
      (Real.exp (hl * g v) ≥ Real.exp (hl * t)) ↔ (t ≤ g v) := by
    intro v
    constructor
    · intro hge
      have hh := Real.exp_le_exp.mp hge
      nlinarith [hh, hltp]
    · intro hle
      exact Real.exp_le_exp.mpr (by nlinarith [hltp])
  have heq : Finset.filter (fun v =>
      Real.exp (hl * g v) ≥ Real.exp (hl * t)) Finset.univ = s₁ := by
    apply Finset.ext
    intro v
    rw [Finset.mem_filter, Finset.mem_filter, hiff v]
  rw [heq] at hm
  exact le_div_iff₀' (Real.exp_pos (hl * t)) |>.mpr hm

open Finset Real in
/-- **Экспоненциальная
интерполяция
(R484)**: для a ≤ g ≤ b:
Σp·e^{c·g} ≤
e^{ca}·Σp·w₁
+ e^{cb}·Σp·w₂,
w₁ = (b−g)/(b−a),
w₂ = (g−a)/(b−a)
— выпуклость e^
через двухточечный
АМ-ГМ (R454):
три случая (краи
аналітика +середина),
p·множение
самсого-сумы-суммой
через
mul_le_mul_of_nonneg_left. -/
theorem exp_tilt_interpol {V : Type*} [Fintype V] [Nonempty V]
    (p g : V → ℝ) (c a b : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hgb : ∀ v, g v ≤ b) (hga : ∀ v, a ≤ g v) (hxx : a < b) :
    ∑ v : V, p v * Real.exp (c * g v)
      ≤ Real.exp (c * a)
        * ∑ v : V, p v * ((b - g v) / (b - a))
        + Real.exp (c * b)
          * ∑ v : V, p v * ((g v - a) / (b - a)) := by
  have hw1 : ∀ v : V, (0:ℝ) ≤ (b - g v) / (b - a) := by
    intro v; exact div_nonneg (by linarith [hgb v]) (by linarith)
  have hw2 : ∀ v : V, (0:ℝ) ≤ (g v - a) / (b - a) := by
    intro v; exact div_nonneg (by linarith [hga v]) (by linarith)
  have hws : ∀ v : V, (b - g v) / (b - a) + (g v - a) / (b - a) = 1 := by
    intro v
    rw [← add_div, show (b - g v) + (g v - a) = (b - a) from by ring,
      div_self (by linarith)]
  have hmid : ∀ v : V, (b - g v) / (b - a) * (c * a)
      + (g v - a) / (b - a) * (c * b) = c * g v := by
    intro v
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      show (b - g v) * (c * a) + (g v - a) * (c * b)
        = c * g v * (b - a) from by ring]
    rw [mul_div_assoc (c * g v) (b - a)]
    rw [div_self (show (b - a : ℝ) ≠ 0 by linarith), mul_one]
  have hpos : ∀ v : V, (0:ℝ) < (b - g v) / (b - a) * Real.exp (c * a)
      + (g v - a) / (b - a) * Real.exp (c * b) := by
    intro v
    by_cases hlt : g v < b
    · have h1 : (0:ℝ) < (b - g v) / (b - a) :=
        div_pos (by linarith) (by linarith)
      exact lt_add_of_pos_of_le
        (mul_pos h1 (Real.exp_pos (c * a)))
        (mul_nonneg (hw2 v) (Real.exp_nonneg (c * b)))
    · have hge : g v = b := le_antisymm (hgb v) (by linarith)
      have h2 : (0:ℝ) < (g v - a) / (b - a) := by
        rw [hge]
        exact div_pos (by linarith) (by linarith)
      exact lt_add_of_le_of_pos
        (mul_nonneg (hw1 v) (Real.exp_nonneg (c * a)))
        (mul_pos h2 (Real.exp_pos (c * b)))
  have hper : ∀ v : V, Real.exp (c * g v)
      ≤ (b - g v) / (b - a) * Real.exp (c * a)
        + (g v - a) / (b - a) * Real.exp (c * b) := by
    intro v
    rcases eq_or_lt_of_le (hga v) with hga' | hgt
    · have hw1e : (b - g v) / (b - a) = (1:ℝ) := by
        rw [show (b - g v) = (b - a) from by rw [hga']]
        exact div_self (by linarith)
      have hw2e : (g v - a) / (b - a) = (0:ℝ) := by
        rw [show (g v - a) = (0:ℝ) from by rw [hga']; ring, zero_div]
      rw [hw1e, hw2e, one_mul, zero_mul, add_zero]
      exact Real.exp_le_exp.mpr (by rw [hga'])
    · rcases eq_or_lt_of_le (hgb v) with hgb' | hlt
      · have hb : (b - g v) = (0:ℝ) := by rw [hgb']; ring
        have ha2 : (g v - a) = (b - a) := by rw [hgb']
        have hw1f : (b - g v) / (b - a) = (0:ℝ) := by
          rw [hb, zero_div]
        have hw2f : (g v - a) / (b - a) = (1:ℝ) := by
          rw [ha2]
          exact div_self (ne_of_gt
            (show (0:ℝ) < b - a by linarith))
        rw [hw1f, hw2f, zero_mul, one_mul, zero_add]
        exact Real.exp_le_exp.mpr (by rw [hgb'])
      · have hw1s : (0:ℝ) < (b - g v) / (b - a) :=
          div_pos (by linarith) (by linarith)
        have hw2s : (0:ℝ) < (g v - a) / (b - a) :=
          div_pos (by linarith) (by linarith)
        have hlam2 : (b - g v) / (b - a) < 1 := by linarith [hws v]
        have hR := log_concave_two hw1s hlam2
          (Real.exp_pos (c * a)) (Real.exp_pos (c * b))
        rw [Real.log_exp (c * a), Real.log_exp (c * b)] at hR
        have hw2eq : (g v - a) / (b - a)
            = 1 - (b - g v) / (b - a) := by linarith [hws v]
        have hmid2 : (b - g v) / (b - a) * (c * a)
            + (1 - (b - g v) / (b - a)) * (c * b) = c * g v := by
          have h2 := hmid v
          rw [hw2eq] at h2
          exact h2
        rw [hmid2] at hR
        have hX := Real.exp_le_exp.mpr hR
        have hpos2 : (0:ℝ) < (b - g v) / (b - a) * Real.exp (c * a)
            + (1 - (b - g v) / (b - a)) * Real.exp (c * b) := by
          rw [← hw2eq]
          exact hpos v
        rw [Real.exp_log hpos2, ← hw2eq] at hX
        exact hX
  refine le_trans (Finset.sum_le_sum (fun v _ =>
    mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hp v)))) ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  exact le_of_eq (by ring)

open Finset Real in
/-- **Cramér-наклон
(R485)**: если E_p g ≥ t,
то для любого
c > 0: c·t −
ln Σq·e^{c·g} ≤
KL(p‖q).
Опора arXiv 2401.01148
(PAC-Bayes-Chernoff,
NeurIPS 2024) — первый
кирпич вертикали. -/
theorem cramer_tilt_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hc : 0 < c) (hge : t ≤ ∑ v : V, p v * g v) :
    c * t - Real.log (∑ v : V, q v * Real.exp (c * g v))
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hR := kl_chernoff_tilt p q g c hp hp1 hq hq1
  have hmono : c * t ≤ c * ∑ v : V, p v * g v :=
    mul_le_mul_of_nonneg_left hge hc.le
  linarith [hR, hmono]

open Finset Real in
/-- **Cramér-sup (R486)**: при E_p g ≥ t:
sSup по c > 0
функционала c·t −
ln Σq·e^{c·g}
≤ KL(p‖q)
(вертикаль arXiv
2401.01148, кирпич 2;
САВ (sup + bound) = Cramér-оболочка). -/
theorem cramer_sup_le_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hge : t ≤ ∑ v : V, p v * g v) :
    sSup {x : ℝ | ∃ c > 0, x = c * t
      - Real.log (∑ v : V, q v * Real.exp (c * g v))}
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  apply csSup_le
  · exact ⟨1 * t - Real.log (∑ v : V, q v * Real.exp (1 * g v)),
      ⟨(1:ℝ), by norm_num, rfl⟩⟩
  · intro x hx
    rcases hx with ⟨c, hc, hxe⟩
    refine hxe ▸ cramer_tilt_kl p q g t c hp hp1 hq hq1 hc ?_
    exact hge

open Finset Real in
/-- **CGF-форма
Cramér (R487)**: если
ln Σq·e^{c(g−μ)} ≤ ψ(c)
и E_p g ≥ t, то
c·(t−μ) − ψ(c) ≤
KL(p‖q) для любого
c > 0 — кирпич CGF-вертикали
(2401.01148 /
JMLR 23-1360: параметр-свободная
CGF-оболочка). -/
theorem cramer_cgf {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t μ : ℝ) (ψ : ℝ → ℝ) (c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hc : 0 < c) (hge : t ≤ ∑ v : V, p v * g v)
    (hcgf : Real.log (∑ v : V, q v * Real.exp (c * (g v - μ))) ≤ ψ c) :
    c * (t - μ) - ψ c ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hper : ∀ v : V, q v * Real.exp (c * g v)
      = Real.exp (c * μ) * (q v * Real.exp (c * (g v - μ))) := by
    intro v
    have h1 : c * g v = c * (g v - μ) + c * μ := by ring
    rw [h1, Real.exp_add]
    ring
  have hsplit : ∑ v : V, q v * Real.exp (c * g v)
      = Real.exp (c * μ) * ∑ v : V,
          q v * Real.exp (c * (g v - μ)) := by
    rw [Finset.sum_congr rfl (fun v _ => hper v), ← Finset.mul_sum]
  have hpos : (0:ℝ) < ∑ v : V, q v * Real.exp (c * (g v - μ)) :=
    Finset.sum_pos (fun v _ => mul_pos (hq v)
      (Real.exp_pos _)) ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hR := cramer_tilt_kl p q g t c hp hp1 hq hq1 hc hge
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne'
    hpos.ne'] at hR
  rw [Real.log_exp (c * μ)] at hR
  linarith [hR, hcgf]

open Finset Real in
/-- **Sub-Gaussian
измерение
(R488)**: при CGF-границе
ln Σq·e^{c(g−μ)} ≤
c²σ²/2 и μ ≤ E_p g:
(E_p g − μ)²/(2σ²) ≤
KL(p‖q) — λ*подстановка
λ = (E_p g − μ)/σ² в R487
без дифференциального
исчисления (оптимум
Cramér-функционала). -/
theorem subgauss_dev_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (μ σ2 : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hs2 : 0 < σ2) (hm : μ ≤ ∑ v : V, p v * g v)
    (hcgf : ∀ c : ℝ, 0 < c →
      Real.log (∑ v : V, q v * Real.exp (c * (g v - μ)))
        ≤ c ^ 2 * σ2 / 2) :
    ((∑ v : V, p v * g v) - μ) ^ 2 / (2 * σ2)
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  set T := ∑ v : V, p v * g v with hT
  rcases eq_or_lt_of_le hm with hhe | hlt
  · rw [← hhe]
    have hkl := finite_kl_nonneg p q hp hp1 hq hq1
    simpa using hkl
  · have hc : (0:ℝ) < (T - μ) / σ2 := div_pos (by linarith) hs2
    have hR := cramer_cgf p q g T μ (fun x => x ^ 2 * σ2 / 2)
      ((T - μ) / σ2) hp hp1 hq hq1 hc (by linarith)
      (hcgf _ hc)
    have hval : (T - μ) / σ2 * (T - μ)
        - ((T - μ) / σ2) ^ 2 * σ2 / 2
        = (T - μ) ^ 2 / (2 * σ2) := by
      field_simp
      ring
    rw [hval] at hR
    exact hR

open Finset Real in
/-- **Сдвиг-среднего
~ TV (R489)**: при
a ≤ g ≤ b:
|E_p g − E_q g| ≤
(b−a)·TV(p,q).
Механика: нормировка
f = (g−a)/(b−a) —
дуальность R473 +
центрировка μ-сдвига
(=с линейным
мостом Δ = d·F
через
partition sum_div). -/
theorem mean_shift_tv {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q g : V → ℝ) (a b : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (hab : a < b) :
    |∑ v : V, p v * g v - ∑ v : V, q v * g v|
      ≤ (b - a) * ((1/2) * ∑ v : V, |p v - q v|) := by
  have hD : (0:ℝ) < b - a := by linarith
  have hf0 : ∀ v, 0 ≤ (g v - a) / (b - a) :=
    fun v => div_nonneg (by linarith [hlo v]) hD.le
  have hf1 : ∀ v, (g v - a) / (b - a) ≤ 1 := by
    intro v
    rw [div_le_one hD]
    linarith [hhi v]
  set Δ := ∑ v : V, p v * g v - ∑ v : V, q v * g v with hΔ
  set F := ∑ v : V, p v * ((g v - a) / (b - a))
    - ∑ v : V, q v * ((g v - a) / (b - a)) with hF
  have hΔF : Δ = (b - a) * F := by
    have hEp : ∑ v : V, p v * ((g v - a) / (b - a))
        = (∑ v : V, p v * (g v - a)) / (b - a) := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_div_assoc' (p v) _ _), Finset.sum_div]
    have hEq : ∑ v : V, q v * ((g v - a) / (b - a))
        = (∑ v : V, q v * (g v - a)) / (b - a) := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_div_assoc' (q v) _ _), Finset.sum_div]
    have hbn : ∑ v : V, p v * (g v - a)
        = ∑ v : V, p v * g v - a := by
      have h2 : ∑ v : V, p v * (g v - a)
          = ∑ v : V, p v * g v - ∑ v : V, p v * a := by
        rw [Finset.sum_congr rfl (fun v _ => by rw [mul_sub]),
          Finset.sum_sub_distrib]
      rw [h2]
      have h3 : ∑ v : V, p v * a = a := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (p v) a),
          ← Finset.mul_sum, hp1, mul_one]
      rw [h3]
    have hqn : ∑ v : V, q v * (g v - a)
        = ∑ v : V, q v * g v - a := by
      have h2 : ∑ v : V, q v * (g v - a)
          = ∑ v : V, q v * g v - ∑ v : V, q v * a := by
        rw [Finset.sum_congr rfl (fun v _ => by rw [mul_sub]),
          Finset.sum_sub_distrib]
      rw [h2]
      have h3 : ∑ v : V, q v * a = a := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a),
          ← Finset.mul_sum, hq1, mul_one]
      rw [h3]
    rw [hΔ, hF, hEp, hEq, hbn, hqn, div_sub_div_same]
    rw [show (∑ v : V, p v * g v - a) - (∑ v : V, q v * g v - a)
        = ∑ v : V, p v * g v - ∑ v : V, q v * g v from by ring]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hD)]
  have hf0 : ∀ v, 0 ≤ (g v - a) / (b - a) :=
    fun v => div_nonneg (by linarith [hlo v]) hD.le
  have hf1 : ∀ v, (g v - a) / (b - a) ≤ 1 := by
    intro v
    rw [div_le_one hD]
    linarith [hhi v]
  have hdual := tv_dual_abs p q (fun v => (g v - a) / (b - a))
    hp hp1 hq hq1 hf0 hf1
  rw [hΔF, abs_mul, abs_of_pos hD]
  exact mul_le_mul_of_nonneg_left hdual hD.le

