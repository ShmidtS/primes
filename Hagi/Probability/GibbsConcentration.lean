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

