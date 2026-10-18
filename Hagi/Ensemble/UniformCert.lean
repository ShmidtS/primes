/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.Hoeffding

set_option linter.style.header false

/-!
# Uniform-certification block (R402-R410): the probabilistic method

Отщеплено от Ensemble.Hoeffding: хорошие точки, двусторонние
массы, нижняя граница класса, калибровка допуска. Зависит от
ядра `hoeffding_union_tail`; один внешний потребитель —
Growth.Thermostat (calibrated_good_point).
-/

open Finset Real
open scoped ENNReal NNReal

namespace Hagi.Ensemble

/-! ### Probabilistic method (R402): если |K|·e^{−2ε²/(b−a)²} < 1,
то существует "хорошая точка" v: ∀ k, d k v < ε.
От противного: если каждая точка проигрывает какому-то k,
плохое множество покрывает всю вероятностную массу (1), но
union bound (R384) даёт ≤ |K|·c < 1. Первое применение
uniform-convergence конвейера к existential-утверждению. -/
variable {K : Type*} [Fintype K]

theorem uniform_good_point {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : (Fintype.card K : ℝ) * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
      < 1) :
    ∃ v : V, ∀ k : K, d k v < ε := by
  by_contra hcon
  push_neg at hcon
  -- the bad filter is everything
  have hsub : (Finset.univ : Finset V)
      ⊆ Finset.univ.filter (fun v => ∃ k, ε ≤ d k v) :=
    fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcon v⟩
  -- mass of bad set = 1 (weights nonneg, univ covered)
  have h1le : (1:ℝ) ≤ ∑ v ∈ Finset.univ.filter
      (fun v => ∃ k, ε ≤ d k v), w v := by
    rw [← hw1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => le_of_lt (hw v))
  -- R384: mass of the bad set
  have hR384 := hoeffding_union_tail w d a b hw hw1 hlt hbd hc hε
  linarith

/-! ### Масса хороших точек (R403): ≥ 1 − |K|·e^{−2ε²/(b−a)²} —
вероятностная форма uniform convergence: почти вся масса
сосредоточена на точках, хороших для ВСЕГО класса сразу.
Расщепление filter/filter_not + union bound R384. -/
theorem uniform_good_mass {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - (Fintype.card K : ℝ) * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
      ≤ ∑ v ∈ Finset.univ.filter (fun v => ∀ k, d k v < ε), w v := by
  have hR384 := hoeffding_union_tail w d a b hw hw1 hlt hbd hc hε
  -- bad set = filter (exists k) equals filter (not good)
  classical
  have hsplit : ∑ v ∈ Finset.univ.filter (fun v => ∀ k, d k v < ε), w v
      + ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ d k v), w v
      = ∑ v, w v := by
    have hbad : (Finset.univ.filter (fun v => ∃ k, ε ≤ d k v) : Finset V)
        = Finset.univ.filter (fun v => ¬(∀ k, d k v < ε)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk⟩ h
        exact absurd (h k) (not_lt.2 hk)
      · intro h
        by_contra hcon
        push_neg at hcon
        exact h hcon
    rw [hbad]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun v => ∀ k, d k v < ε) w
  rw [hw1] at hsplit
  linarith

/-! ### Двусторонняя граница (R404): масса {∃k |d k v| ≥ ε}
≤ 2|K|e^{−2ε²/(b−a)²} — расщепление |d| на
верх/низ через индикаторы, R384 к d и −d (границы
[−b,−a], среднее −0). -/
theorem two_sided_union_tail {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ |d k v|), w v
      ≤ 2 * (Fintype.card K : ℝ)
        * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) := by
  -- indicator sums
  have hE : ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ |d k v|), w v
      = ∑ v : V, (if ∃ k, ε ≤ |d k v| then w v else 0) :=
    (Finset.sum_filter (fun v => ∃ k, ε ≤ |d k v|) w)
  have hA : ∑ v : V, (if ∃ k, ε ≤ |d k v| then w v else 0)
      ≤ ∑ v : V, ((if ∃ k, ε ≤ d k v then w v else 0)
        + (if ∃ k, ε ≤ -(d k v) then w v else 0)) := by
    refine Finset.sum_le_sum ?_
    intro v _
    rcases Classical.em (∃ k, ε ≤ |d k v|) with ⟨k, hk⟩ | hE'
    · by_cases hd : (0:ℝ) ≤ d k v
      · have h1 : ε ≤ d k v := by rwa [abs_of_nonneg hd] at hk
        have h2 : (if ∃ k, ε ≤ d k v then w v else 0) = w v := by
          rw [if_pos ⟨k, h1⟩]
        have h3 : (0:ℝ) ≤ (if ∃ k, ε ≤ -(d k v) then w v else 0) := by
          rcases Classical.em (∃ k', ε ≤ -(d k' v)) with h | h'
          · rw [if_pos h]; exact le_of_lt (hw v)
          · rw [if_neg h']
        have hstart : (if ∃ k, ε ≤ |d k v| then w v else 0) = w v := by
          rw [if_pos ⟨k, hk⟩]
        rw [hstart, h2]
        linarith
      · have h1 : ε ≤ -(d k v) := by
          rwa [abs_of_neg (by linarith : d k v < 0)] at hk
        have h2 : (if ∃ k, ε ≤ -(d k v) then w v else 0) = w v := by
          rw [if_pos ⟨k, h1⟩]
        have h3 : (0:ℝ) ≤ (if ∃ k, ε ≤ d k v then w v else 0) := by
          rcases Classical.em (∃ k', ε ≤ d k' v) with h | h'
          · rw [if_pos h]; exact le_of_lt (hw v)
          · rw [if_neg h']
        have hstart : (if ∃ k, ε ≤ |d k v| then w v else 0) = w v := by
          rw [if_pos ⟨k, hk⟩]
        rw [hstart, h2]
        linarith
    · have hstart : (if ∃ k, ε ≤ |d k v| then w v else 0) = 0 := by
        rw [if_neg hE']
      have hnn : ∀ v : V, (0:ℝ) ≤ (if ∃ k, ε ≤ d k v then w v else 0)
          + (if ∃ k, ε ≤ -(d k v) then w v else 0) := by
        intro v
        rcases Classical.em (∃ k, ε ≤ d k v) with h | h'
        · rw [if_pos h]
          rcases Classical.em (∃ k, ε ≤ -(d k v)) with h2 | h2'
          · rw [if_pos h2]; linarith [hw v]
          · rw [if_neg h2']; linarith [hw v]
        · rw [if_neg h']
          rcases Classical.em (∃ k, ε ≤ -(d k v)) with h2 | h2'
          · rw [if_pos h2]; linarith [hw v]
          · rw [if_neg h2']
            linarith
      rw [hstart]
      exact hnn v
  -- now sum of indicators splits into A + B sums
  have hsplit : ∑ v : V, ((if ∃ k, ε ≤ d k v then w v else 0)
        + (if ∃ k, ε ≤ -(d k v) then w v else 0))
      = ∑ v : V, (if ∃ k, ε ≤ d k v then w v else 0)
        + ∑ v : V, (if ∃ k, ε ≤ -(d k v) then w v else 0) :=
    Finset.sum_add_distrib
  -- rewrite each as filter sums and apply R384
  have hup : ∑ v : V, (if ∃ k, ε ≤ d k v then w v else 0)
      = ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ d k v), w v :=
    (Finset.sum_filter (fun v => ∃ k, ε ≤ d k v) w).symm
  have hdown : ∑ v : V, (if ∃ k, ε ≤ -(d k v) then w v else 0)
      = ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ -(d k v)), w v :=
    (Finset.sum_filter (fun v => ∃ k, ε ≤ -(d k v)) w).symm
  -- R384 up (direct) and down (apply to -d)
  have hRup := hoeffding_union_tail w d a b hw hw1 hlt hbd hc hε
  -- for -d: bounds negated, mean negated
  have hneg_bd : ∀ k v, -(d k v) ∈ Set.Icc (-b) (-a) := by
    intro k v
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp (hbd k v)
    constructor
    · linarith
    · linarith
  have hneg_c : ∀ k, ∑ v, w v * -(d k v) = 0 := by
    intro k
    have heq : ∑ v, w v * -(d k v) = -∑ v, w v * d k v := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => mul_neg (w v) (d k v))
    rw [heq, hc k]
    ring
  have hneg_lt : (-b:ℝ) < -a := by linarith
  have hRdown := hoeffding_union_tail w (fun k v => -(d k v)) (-b) (-a)
    hw hw1 hneg_lt hneg_bd hneg_c hε
  -- exponent match: (b-a)^2 = (-a-(-b))^2
  have hexp : (-a - (-b))^2 = (b - a)^2 := by ring
  rw [hexp] at hRdown
  -- combine
  rw [hE]
  calc ∑ v : V, (if ∃ k, ε ≤ |d k v| then w v else 0)
      ≤ ∑ v : V, ((if ∃ k, ε ≤ d k v then w v else 0)
        + (if ∃ k, ε ≤ -(d k v) then w v else 0)) := hA
    _ = ∑ v : V, (if ∃ k, ε ≤ d k v then w v else 0)
        + ∑ v : V, (if ∃ k, ε ≤ -(d k v) then w v else 0) := hsplit
    _ = ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ d k v), w v
        + ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ -(d k v)), w v :=
          by rw [hup, hdown]
    _ ≤ (Fintype.card K : ℝ) * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
        + (Fintype.card K : ℝ) * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) :=
          add_le_add hRup hRdown
    _ = 2 * (Fintype.card K : ℝ)
        * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) := by ring

/-! ### Двусторонняя масса хороших точек (R405): ≥
1 − 2|K|e^{−2ε²/(b−a)²} — вероятностная форма
двусторонней uniform convergence (R404 + filter-расщепление
R403-паттерн). -/
theorem two_sided_good_mass {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - 2 * (Fintype.card K : ℝ)
        * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
      ≤ ∑ v ∈ Finset.univ.filter (fun v => ∀ k, |d k v| < ε), w v := by
  have hR404 := two_sided_union_tail w d a b hw hw1 hlt hbd hc hε
  classical
  have hsplit : ∑ v ∈ Finset.univ.filter (fun v => ∀ k, |d k v| < ε), w v
      + ∑ v ∈ Finset.univ.filter (fun v => ∃ k, ε ≤ |d k v|), w v
      = ∑ v, w v := by
    have hbad : (Finset.univ.filter (fun v => ∃ k, ε ≤ |d k v|) : Finset V)
        = Finset.univ.filter (fun v => ¬(∀ k, |d k v| < ε)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk⟩ h
        exact absurd (h k) (not_lt.2 hk)
      · intro h
        by_contra hcon
        push_neg at hcon
        exact h hcon
    rw [hbad]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun v => ∀ k, |d k v| < ε) w
  rw [hw1] at hsplit
  linarith

/-! ### Нижняя граница класса (R406): если каждая точка
проигрывает какому-то k (нет ε-хорошей точки), то
|K| ≥ e^{2ε²/(b−a)²} — экспоненциальная нижняя оценка
размера покрывающего класса (контрапозиция R402 в
размерной форме: covering-number bound). -/
theorem class_size_lower {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hcover : ∀ v : V, ∃ k : K, ε ≤ d k v) :
    Real.exp (2 * ε ^ 2 / (b - a) ^ 2)
      ≤ (Fintype.card K : ℝ) := by
  -- R384 gives |K| * c >= 1
  have hR384 := hoeffding_union_tail w d a b hw hw1 hlt hbd hc hε
  -- the bad filter covers everything: mass = 1
  have hsub : (Finset.univ : Finset V)
      ⊆ Finset.univ.filter (fun v => ∃ k, ε ≤ d k v) :=
    fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcover v⟩
  have h1le : (1:ℝ) ≤ ∑ v ∈ Finset.univ.filter
      (fun v => ∃ k, ε ≤ d k v), w v := by
    rw [← hw1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => le_of_lt (hw v))
  have hkey : (1:ℝ) ≤ (Fintype.card K : ℝ)
      * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) := h1le.trans hR384
  -- divide: exp(2..) <= |K|
  have hcpos : (0:ℝ) < Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) :=
    exp_pos _
  have : (1:ℝ) / Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
      ≤ (Fintype.card K : ℝ) := by
    rw [div_le_iff₀ hcpos]
    exact hkey
  -- 1/e^{-t} = e^{t}
  have hinv : (1:ℝ) / Real.exp (-2 * ε ^ 2 / (b - a) ^ 2)
      = Real.exp (2 * ε ^ 2 / (b - a) ^ 2) := by
    rw [one_div]
    field_simp
    rw [← Real.exp_add]
    have hz : -(2 * ε ^ 2 / (b - a) ^ 2) + 2 * ε ^ 2 / (b - a) ^ 2 = 0 := by ring
    rw [hz, Real.exp_zero]
  rwa [hinv] at this

/-! ### Калибровка допуска (R409): ε := (b−a)·√(ln(1/θ)/2)
даёт РОВНО e^{−2ε²/(b−a)²} = θ — термостатный θ
переводится в ε-допуск Хёфдинга: мост R407 (θ-гейт) ×
R384 (ε-хвост): хвост класса при калиброванном ε есть
|K|·θ. -/
theorem tolerance_calibration (b θ : ℝ) (hb : 0 < b) (hθ1 : 0 < θ)
    (hθ2 : θ < 1) :
    Real.exp (-2 * ((b * Real.sqrt (Real.log (1/θ)/2)) ^ 2) / b ^ 2)
      = θ := by
  have hRpos : (0:ℝ) < b ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hlogpos : (0:ℝ) < Real.log (1/θ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hθ1]
    linarith
  -- expand the square: (b * sqrt(L/2))^2 = b^2 * L/2
  have hsq : (b * Real.sqrt (Real.log (1/θ)/2)) ^ 2
      = b ^ 2 * (Real.log (1/θ)/2) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  rw [hsq]
  -- exponent: -2 * (b^2 * L/2) / b^2 = -L
  have hexp : -2 * (b ^ 2 * (Real.log (1/θ)/2)) / b ^ 2
      = -Real.log (1/θ) := by
    field_simp
  rw [hexp, Real.exp_neg (Real.log (1/θ)), Real.exp_log (by
    rw [lt_div_iff₀ hθ1]; linarith), one_div, inv_inv]

/-! ### Калиброванная двусторонняя масса (R410): при
ε = (b−a)√(ln(1/θ)/2) (R409-калибровка) масса точек,
хороших для всего класса, ≥ 1 − 2|K|θ — финальное звено
моста: охлаждение (θ) → ε-допуск → сертифицированная
равномерная точность. -/
theorem calibrated_two_sided_mass {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1) :
    1 - 2 * (Fintype.card K : ℝ) * θ
      ≤ ∑ v ∈ Finset.univ.filter
          (fun v => ∀ k, |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2)),
          w v := by
  -- R405 at calibrated eps
  set ε : ℝ := (b - a) * Real.sqrt (Real.log (1/θ)/2) with hε
  have hεpos : (0:ℝ) ≤ ε := by
    have hR : (0:ℝ) ≤ b - a := by linarith
    have hone : (1:ℝ) < 1/θ := by
      rw [lt_div_iff₀ hθ1]
      linarith
    have hlog : (0:ℝ) ≤ Real.log (1/θ) :=
      le_of_lt (Real.log_pos hone)
    apply mul_nonneg
    · exact hR
    · exact Real.sqrt_nonneg _
  have hR405 := two_sided_good_mass w d a b hw hw1 hlt hbd hc hεpos
  -- rewrite the exp factor via R409
  have hcal := tolerance_calibration (b - a) θ (by linarith) hθ1 hθ2
  rw [hcal] at hR405
  exact hR405

/-! ### Двусторонняя хорошая точка (R411a): при
2|K|e^{−2ε²/(b−a)²} < 1 существует v: ∀k |d k v| < ε
(вероятностный метод на R404). -/
theorem two_sided_good_point {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : 2 * (Fintype.card K : ℝ)
      * Real.exp (-2 * ε ^ 2 / (b - a) ^ 2) < 1) :
    ∃ v : V, ∀ k : K, |d k v| < ε := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset V)
      ⊆ Finset.univ.filter (fun v => ∃ k, ε ≤ |d k v|) :=
    fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcon v⟩
  have h1le : (1:ℝ) ≤ ∑ v ∈ Finset.univ.filter
      (fun v => ∃ k, ε ≤ |d k v|), w v := by
    rw [← hw1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v _ _ => le_of_lt (hw v))
  have hR404 := two_sided_union_tail w d a b hw hw1 hlt hbd hc hε
  linarith


/-! ### Калиброванная хорошая точка (R411b): при 2|K|θ < 1
существует v, равномерно ε_θ-хорошая для всего класса,
ε_θ = (b−a)√(ln(1/θ)/2) (R411a × R409) — сэмпл-
сложность моста в θ-параметризации: термостатная θ
гарантирует существование репрезентативной точки. -/
theorem calibrated_good_point {V K : Type*} [Fintype V]
    [Nonempty V] [Fintype K] (w : V → ℝ) (d : K → V → ℝ)
    (a b : ℝ) (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hlt : a < b) (hbd : ∀ k v, d k v ∈ Set.Icc a b)
    (hc : ∀ k, ∑ v, w v * d k v = 0)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ < 1)
    (hsmall : 2 * (Fintype.card K : ℝ) * θ < 1) :
    ∃ v : V, ∀ k : K,
      |d k v| < (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
  -- R402 with calibrated eps
  have hεpos : (0:ℝ) ≤ (b - a) * Real.sqrt (Real.log (1/θ)/2) := by
    have hR : (0:ℝ) ≤ b - a := by linarith
    have hone : (1:ℝ) < 1/θ := by
      rw [lt_div_iff₀ hθ1]
      linarith
    apply mul_nonneg hR _
    exact Real.sqrt_nonneg _
  have hcal := tolerance_calibration (b - a) θ (by linarith) hθ1 hθ2
  have hcond : 2 * (Fintype.card K : ℝ)
      * Real.exp (-2 * ((b - a) * Real.sqrt (Real.log (1/θ)/2)) ^ 2
        / (b - a) ^ 2) < 1 := by
    rw [hcal]
    linarith
  exact two_sided_good_point w d a b hw hw1 hlt hbd hc hεpos hcond


end Hagi.Ensemble
