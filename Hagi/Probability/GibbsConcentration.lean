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

