/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Probability.GibbsCooling

/-!
# Каноническое распределение Гиббса

Начало M4-консолидации Гиббс-семейства: единое
определение массы `gibbsW` и нормирующей константы
`gibbsZ` вместо inline-расписываний в десятке
модулей. Базовые леммы: позитивность, нормировка,
сдвиг-инвариантность свободной энергии.
-/

namespace Hagi.Probability

open Finset Real

variable {V : Type*} [Fintype V]

/-- Вес состояния `v` при температуре `T`. -/
noncomputable def gibbsW (E : V → ℝ) (T : ℝ) (v : V) : ℝ :=
  Real.exp (-(E v)/T)

/-- Статистическая сумма. -/
noncomputable def gibbsZ (E : V → ℝ) (T : ℝ) : ℝ :=
  ∑ v, gibbsW E T v

/-- Вес строго положителен при положительной
температуре. -/
theorem gibbsW_pos (E : V → ℝ) (T : ℝ) (hT : 0 < T) (v : V) :
    0 < gibbsW E T v := by
  unfold gibbsW
  exact exp_pos _

/-- Статистическая сумма строго положительна на
непустом носителе. -/
theorem gibbsZ_pos (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    [Nonempty V] : 0 < gibbsZ E T := by
  unfold gibbsZ
  exact Finset.sum_pos (fun v _ => gibbsW_pos E T hT v)
    ⟨Classical.arbitrary V, Finset.mem_univ _⟩

/-- НОРМИРОВКА: сумма нормированных весов равна
единице — `gibbsW/gibbsZ` вероятностный вектор. -/
theorem gibbs_normalize (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    [Nonempty V] :
    ∑ v, gibbsW E T v / gibbsZ E T = 1 := by
  have hpos := gibbsZ_pos E T hT
  rw [← Finset.sum_div]
  show gibbsZ E T / gibbsZ E T = 1
  rw [div_self hpos.ne']

/-- СДВИГ-ИНВАРИАНТНОСТЬ: сдвиг всех энергий на
константу умножает статистическую сумму — нормированное
распределение не меняется. -/
theorem gibbsZ_shift (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (c : ℝ) :
    gibbsZ (fun v => E v + c) T
      = Real.exp (-c/T) * gibbsZ E T := by
  unfold gibbsZ gibbsW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← exp_add]
  congr 1
  field_simp
  ring

/-- ДОМИНИРОВАНИЕ ОСНОВНОГО СОСТОЯНИЯ: вес минимума
энергии не меньше веса любого конкурента при ЛЮБОЙ
положительной температуре (экспонента антимонотонна). -/
theorem gibbsW_min_dominates (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (vstar v : V) (hle : E vstar ≤ E v) :
    gibbsW E T v ≤ gibbsW E T vstar := by
  unfold gibbsW
  exact Real.exp_le_exp.mpr
    ((div_le_div_iff_of_pos_right hT).mpr (neg_le_neg hle))

/-- ГЛАВНЫЙ ВЫВОД: нормированный вес основного состояния
не меньше равномерного — минимум доминирует в среднем. -/
theorem gibbs_min_weight_ge_uniform (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) [Nonempty V] (vstar : V)
    (hmin : ∀ v, E vstar ≤ E v) :
    1 / (Fintype.card V : ℝ)
      ≤ gibbsW E T vstar / gibbsZ E T := by
  have hZpos : 0 < gibbsZ E T := gibbsZ_pos E T hT
  have hZle : gibbsZ E T
      ≤ (Fintype.card V : ℝ) * gibbsW E T vstar := by
    calc gibbsZ E T = ∑ v, gibbsW E T v := rfl
      _ ≤ ∑ v, gibbsW E T vstar :=
        Finset.sum_le_sum fun v _ =>
          gibbsW_min_dominates E T hT vstar v (hmin v)
      _ = (Fintype.card V : ℝ) * gibbsW E T vstar := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (1/(Fintype.card V : ℝ)) * gibbsZ E T
      ≤ (1/(Fintype.card V : ℝ))
        * ((Fintype.card V : ℝ) * gibbsW E T vstar) :=
    mul_le_mul_of_nonneg_left hZle (by positivity)
  have h2 : (1/(Fintype.card V : ℝ))
      * ((Fintype.card V : ℝ) * gibbsW E T vstar)
      = gibbsW E T vstar := by field_simp
  rw [le_div_iff₀ hZpos]
  linarith [h1, h2]

/-- ЭКСПОНЕНЦИАЛЬНАЯ КОНЦЕНТРАЦИЯ НА КАНОНЕ: при
дельта-зазоре до конкурентов нормированный вес минимума
не хуже единицы, делённой на единицу плюс хвост
конкурентов с фактором остывания. -/
theorem gibbs_concentration_canon (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) [Nonempty V] [DecidableEq V]
    (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v) :
    1 / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T))
      ≤ gibbsW E T vstar / gibbsZ E T := by
  have hZpos : 0 < gibbsZ E T := gibbsZ_pos E T hT
  have hwle : ∀ v, v ≠ vstar → gibbsW E T v
      ≤ gibbsW E T vstar * Real.exp (-δ/T) := by
    intro v hv
    have hE := hgap v hv
    have hnegg : -(E v) ≤ -(E vstar + δ) := neg_le_neg hE
    have hdivg : -(E v)/T ≤ -(E vstar + δ)/T :=
      (div_le_div_iff_of_pos_right hT).mpr hnegg
    have hring : -(E vstar + δ)/T
        = -(E vstar)/T + -(δ/T) := by
      field_simp
      ring
    have hpar : (-δ / T : ℝ) = -((δ / T : ℝ)) := by ring
    have hpar : (-δ / T : ℝ) = -((δ / T : ℝ)) := by ring
    unfold gibbsW
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcn : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
    have h1 : (1:ℕ) ≤ Fintype.card V := by
      obtain ⟨v⟩ := ‹Nonempty V›
      have hsub : ({v} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.card_le_card hsub
      simpa using hle
    exact_mod_cast h1
  set Bv := gibbsW E T vstar * Real.exp (-δ/T) with hBv
  have hbound : gibbsZ E T
      ≤ gibbsW E T vstar
        + ((Fintype.card V : ℝ) - 1) * Bv := by
    calc gibbsZ E T = ∑ v, gibbsW E T v := rfl
      _ ≤ ∑ v, (if v = vstar then gibbsW E T vstar else Bv) :=
            Finset.sum_le_sum fun v _ => by
              by_cases h : v = vstar
              · simp [h]
              · simp only [if_neg h]
                exact hwle v h
      _ = gibbsW E T vstar + ((Fintype.card V : ℝ) - 1) * Bv := by
          have h1 : ∀ v : V, (if v = vstar then gibbsW E T vstar else Bv)
              = (if v = vstar then gibbsW E T vstar - Bv else 0) + Bv := by
            intro v
            by_cases h : v = vstar
            · simp [h]
            · simp [h]
          rw [Finset.sum_congr rfl (fun v _ => h1 v),
            Finset.sum_add_distrib]
          have hA : ∑ v, (if v = vstar then gibbsW E T vstar - Bv else 0)
              = gibbsW E T vstar - Bv :=
            Fintype.sum_ite_eq' vstar (fun _ : V => gibbsW E T vstar - Bv)
          have hB : ∑ v : V, Bv = (Fintype.card V : ℝ) * Bv := by
            simp
          rw [hA, hB]
          ring
  have hZle : gibbsZ E T
      ≤ gibbsW E T vstar
        * (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T)) := by
    have hform : gibbsW E T vstar
        * (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T))
        = gibbsW E T vstar
          + ((Fintype.card V : ℝ) - 1) * Bv := by
      rw [hBv]
      ring
    linarith
  have hXpos : (0:ℝ)
      < 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T) := by
    have hprod : (0:ℝ)
        ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    linarith
  rw [le_div_iff₀ hZpos, div_mul_eq_mul_div,
    div_le_iff₀ hXpos, one_mul]
  exact hZle

/-- ЭНЕРГЕТИЧЕСКИЙ СЭНДВИЧ НА КАНОНЕ: ожидаемая энергия
Гиббса не выше оптимума плюс размах, умноженный на
экспоненциальный хвост конкурентов. -/
theorem gibbs_mean_energy_gap (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    [Nonempty V] [DecidableEq V]
    (δ Δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hmax : ∀ v, E v ≤ E vstar + Δ) :
    (∑ v, E v * gibbsW E T v) / gibbsZ E T
      ≤ E vstar + Δ * ((Fintype.card V : ℝ) - 1)
          * Real.exp (-δ/T) := by
  have hZpos : 0 < gibbsZ E T := gibbsZ_pos E T hT
  have hΔ : (0:ℝ) ≤ Δ := by
    have := hmax vstar
    linarith
  set p : V → ℝ := fun v => gibbsW E T v / gibbsZ E T with hpdef
  set X : ℝ := ((Fintype.card V : ℝ) - 1) * Real.exp (-δ/T)
    with hXdef
  have hX : (0:ℝ) ≤ X := by
    have hcn : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
      have h1 : (1:ℕ) ≤ Fintype.card V := by
        obtain ⟨w⟩ := ‹Nonempty V›
        have hsub : ({w} : Finset V) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hle := Finset.card_le_card hsub
        simpa using hle
      exact_mod_cast h1
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hp1 : ∑ v, p v = 1 := gibbs_normalize E T hT
  have hwnn : ∀ v, (0:ℝ) ≤ gibbsW E T v := fun v =>
    (gibbsW_pos E T hT v).le
  have hwle : gibbsW E T vstar ≤ gibbsZ E T :=
    Finset.single_le_sum (f := gibbsW E T)
      (fun i _ => hwnn i) (Finset.mem_univ vstar)
  have hple1 : p vstar ≤ 1 := by
    show gibbsW E T vstar / gibbsZ E T ≤ 1
    rw [div_le_iff₀ hZpos]
    linarith
  have hconc := gibbs_concentration_canon E T hT δ vstar hgap
  rw [← hXdef] at hconc
  have hpx : 1 ≤ (1 + X) * p vstar := by
    calc (1:ℝ) = (1 + X) * (1 / (1 + X)) := by
          field_simp
      _ ≤ (1 + X) * p vstar :=
          mul_le_mul_of_nonneg_left hconc (by linarith)
  have hpx' : 1 ≤ p vstar + X * p vstar := by
    have hh := hpx
    linarith
  have hXp : X * p vstar ≤ X := by
    have hh := mul_le_mul_of_nonneg_left hple1 hX
    rw [mul_one] at hh
    exact hh
  have htail : ∑ v, p v - p vstar ≤ X := by
    rw [hp1]
    by_contra hcon
    push_neg at hcon
    linarith
  have hstep : ∀ v : V, (E v - E vstar) * p v
      ≤ Δ * (if v = vstar then (0:ℝ) else p v) := by
    intro v
    by_cases h : v = vstar
    · have hz : (E v - E vstar) * p v = 0 := by
        rw [h, sub_self, zero_mul]
      rw [hz, if_pos h]
      exact mul_nonneg hΔ (by positivity)
    · have hEv : E v - E vstar ≤ Δ := by
        have := hmax v
        linarith
      have hpnn : (0:ℝ) ≤ p v :=
        div_nonneg (hwnn v) hZpos.le
      rw [if_neg h]
      exact mul_le_mul_of_nonneg_right hEv hpnn
  have hsplit : ∑ v, (if v = vstar then (0:ℝ) else p v)
      = ∑ v, p v - p vstar := by
    have hdec : ∀ v : V, (if v = vstar then (0:ℝ) else p v)
        = p v - (if v = vstar then p v else 0) := by
      intro v
      by_cases h : v = vstar <;> simp [h]
    rw [Finset.sum_congr rfl (fun v _ => hdec v),
      Finset.sum_sub_distrib,
      Fintype.sum_ite_eq' vstar p]
  have hmain : ∑ v, (E v - E vstar) * p v
      ≤ Δ * (∑ v, p v - p vstar) := by
    calc ∑ v, (E v - E vstar) * p v
        ≤ ∑ v, Δ * (if v = vstar then (0:ℝ) else p v) :=
          Finset.sum_le_sum fun v _ => hstep v
      _ = Δ * (∑ v, (if v = vstar then (0:ℝ) else p v)) := by
          rw [Finset.mul_sum]
      _ = Δ * (∑ v, p v - p vstar) := by rw [hsplit]
  have heq : ∑ v, (E v - E vstar) * p v
      = ∑ v, E v * p v - E vstar * ∑ v, p v := by
    have hdistr : ∀ v : V, (E v - E vstar) * p v
        = E v * p v - E vstar * p v := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hdistr v),
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hp1, mul_one] at heq
  have hEp : (∑ v, E v * gibbsW E T v) / gibbsZ E T
      = ∑ v, E v * p v := by
    rw [show (∑ v, E v * gibbsW E T v) / gibbsZ E T
        = ∑ v, (E v * gibbsW E T v) / gibbsZ E T from
        sum_div Finset.univ _ _, hpdef]
    exact Finset.sum_congr rfl fun v _ => by
      show E v * gibbsW E T v / gibbsZ E T
        = E v * (gibbsW E T v / gibbsZ E T)
      rw [mul_div_assoc]
  rw [hEp]
  have hfin : ∑ v, E v * p v ≤ E vstar + Δ * X := by
    have h2 : Δ * (∑ v, p v - p vstar) ≤ Δ * X :=
      mul_le_mul_of_nonneg_left htail hΔ
    linarith
  have hgoal : E vstar + Δ * ((Fintype.card V : ℝ) - 1)
      * Real.exp (-δ/T) = E vstar + Δ * X := by
    rw [hXdef]
    ring
  rw [hgoal]
  exact hfin

end Hagi.Probability

/-!
# Мост: концентрация Гиббса через канон

Субтрактивная форма концентрации (традиционная) —
следствие канонической аддитивной: канон несёт более
сильное утверждение, классическая форма наследуется.
-/

namespace Hagi.Probability

open Finset Real

/-- Алгебра: аддитивная форма сильнее субтрактивной. -/
theorem one_div_ge_sub {x : ℝ} (hx : 0 ≤ x) :
    1 - x ≤ 1 / (1 + x) := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith [mul_nonneg hx hx]

/-- МОСТ: традиционная субтрактивная концентрация —
следствие канонической аддитивной. Канон строго сильнее. -/
theorem gibbs_concentration_via_canon
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Real.exp (-(E vstar) / T) / ∑ v, Real.exp (-(E v) / T)
      ≥ 1 - ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T) := by
  have hx : (0:ℝ)
      ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T) := by
    have hcn : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
      have h1 : (1:ℕ) ≤ Fintype.card V := by
        obtain ⟨v⟩ := ‹Nonempty V›
        have hsub : ({v} : Finset V) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hle := Finset.card_le_card hsub
        simpa using hle
      exact_mod_cast h1
    exact mul_nonneg (by linarith) (exp_pos _).le
  have hcanon := gibbs_concentration_canon E T hT δ vstar hgap
  have hsub := one_div_ge_sub hx
  have hchain : 1 - ((Fintype.card V : ℝ) - 1) * Real.exp (-δ / T)
      ≤ gibbsW E T vstar / gibbsZ E T := le_trans hsub hcanon
  unfold gibbsW gibbsZ at hchain
  exact hchain

end Hagi.Probability
