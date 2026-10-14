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

