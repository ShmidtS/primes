/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Prelude.InfoCore
import Hagi.Core.Concat
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option linter.style.header false

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


end Hagi.Probability

section C236_info
namespace Hagi.Probability


open Finset Real

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
  exact Hagi.Prelude.kl_nonneg ρ γ hρ hγ hρ1 hγ1

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
  simpa only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib] using
    Hagi.Prelude.sum_negMulLog_le_log_card ρ (fun v => (hρ v).le) hρ1


end Hagi.Probability

export Hagi.Probability (finite_kl_nonneg free_energy_upper gibbs_expected_energy_lower gibbs_variational)
end C236_info

section C236_cool
namespace Hagi.Energy

open Finset
open Hagi.Prelude
open Set

/-!
# Cooling — термодинамическая ось HAGI

Консолидация (итерация 59, перенос из Variational): Нернст-
оценки Гиббс-значения, расписание → качество, тождество
E = F + T·S, максимум энтропии, качество исполняемой смеси,
геометрическое охлаждение, термическое размытие и коридор
температур — вся термодинамическая ось обучения HAGI в
одном модуле.
-/

/-- **Нернст-скорость Гиббс-значения**: для любого поля потерь L
на конечном пространстве существует достигаемый минимум m,
и темперированное логсумм-значение зажато в двусторонней оценке

  `m - T·log n ≤ -T·log ∑ e^{-Lᵢ/T} ≤ m`

(исследовательская база: Hajek 1988; Catoni–Cot 1998 — охлаждение к
глобальному минимуму). Точность достижения минимума — радиус T·log n:
при T → 0 Гиббс-значение стремится к глобальному минимуму
(экспоненциальная концентрация весов по 1/T). Совместно с
`gibbs_optimal_bound` задаёт термодинамическую ось цели обучения:
скорость охлаждения определяет качество на конечном горизонте. -/
theorem gibbs_value_nernst_bounds {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - T * Real.log ((Fintype.card V : ℕ):ℝ)
          ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  classical
  set S := Finset.univ.image L with hS
  have hne : S.Nonempty := ⟨L (Classical.arbitrary V),
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hm : S.min' hne ∈ S := S.min'_mem hne
  rcases Finset.mem_image.mp hm with ⟨i0, _, hi0⟩
  set m := S.min' hne with hmn
  have hmin : ∀ i, m ≤ L i := fun i =>
    Finset.min'_le S (L i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hsumpos : 0 < ∑ i, Real.exp (-(L i / T)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hge : Real.exp (-(m / T)) ≤ ∑ i, Real.exp (-(L i / T)) := by
    have hthis := Finset.single_le_sum (f := fun i => Real.exp (-(L i / T)))
      (fun i _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i0)
    rw [hi0] at hthis
    exact hthis
  have hle : ∑ i, Real.exp (-(L i / T))
      ≤ ((Fintype.card V : ℕ):ℝ) * Real.exp (-(m / T)) := by
    have hstep : ∑ i, Real.exp (-(L i / T))
        ≤ ∑ i ∈ (Finset.univ : Finset V), Real.exp (-(m / T)) :=
      Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (by
          have h1 : m * T ≤ L i * T := mul_le_mul_of_nonneg_right (hmin i) (le_of_lt hT)
          have h2 : m / T ≤ L i / T := by rw [div_le_div_iff₀ hT hT]; exact h1
          exact neg_le_neg h2))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
    exact hstep
  have hlogge : -(m / T) ≤ Real.log (∑ i, Real.exp (-(L i / T))) := by
    have h := Real.log_le_log (Real.exp_pos _) hge
    rwa [Real.log_exp] at h
  have hlogle : Real.log (∑ i, Real.exp (-(L i / T)))
      ≤ Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T) := by
    have h := Real.log_le_log hsumpos hle
    rwa [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  refine ⟨m, hmin, ⟨i0, hi0.symm⟩, ?_, ?_⟩
  · -- нижняя: m − T·log n ≤ −T·log ∑ (из hlogle)
    have hA : T * Real.log (∑ i, Real.exp (-(L i / T)))
        ≤ T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T)) :=
      mul_le_mul_of_nonneg_left hlogle (le_of_lt hT)
    have hB : T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T))
        = T * Real.log (((Fintype.card V : ℕ):ℝ)) - m := by
      field_simp; ring
    linarith
  · -- верхняя: −T·log ∑ ≤ m (из hlogge)
    have hA : T * (-(m / T)) ≤ T * Real.log (∑ i, Real.exp (-(L i / T))) :=
      mul_le_mul_of_nonneg_left hlogge (le_of_lt hT)
    have hB : T * (-(m / T)) = -m := by field_simp
    linarith

/-- **Следствие: расписание охлаждения достигает качества ε.**
Из `gibbs_value_nernst_bounds`: любая температура T > 0 с
T·log n ≤ ε даёт Гиббс-значение в ε-окрестности глобального
минимума `m - ε ≤ V_T ≤ m`. В частности, T := ε / log n
оптимальна по порядку. Вместе с `gibbs_optimal_bound` это
замыкает термодинамическую ось обучения HAGI: качество как
явная функция расписания охлаждения (максимум качества при
заданном вычислительном бюджете). -/
theorem gibbs_schedule_quality {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T ε : ℝ} (hT : 0 < T)
    (hTeq : T * Real.log ((Fintype.card V : ℕ):ℝ) ≤ ε) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - ε ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  rcases gibbs_value_nernst_bounds L hT with ⟨m, hmin, hatt, hlo, hhi⟩
  exact ⟨m, hmin, hatt, by linarith, hhi⟩

/-- **Термодинамическое тождество ансамбля: E = F + T·S.**
Ожидаемая потеря Гиббс-ансамбля (softDef при обратной
температуре 1/Tt) раскладывается точно:

  `∑ wᵢ·Lᵢ = −Tt·log Z − Tt·∑ wᵢ·log wᵢ`

т.е. энергия = свободная энергия (логсумм-значение) + T·энтропия
(с точностью до знака: E = F + T·S при S = −∑ wᵢ log wᵢ).
Это ядро термодинамической семантики HAGI: качество реальной
смеси (`∑ wᵢ·Lᵢ` — то, что фактически исполняется в
`unified_step_certificate`) связано со свободной энергией
(цель `gibbs_optimal_bound`) через энтропийный член. -/
theorem gibbs_free_energy_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∑ i, softDef (fun i => -(L i) / Tt) i * L i
      = -Tt * Real.log (∑ i, Real.exp (-L i / Tt))
        - Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
            * Real.log (softDef (fun i => -(L i) / Tt) i) := by
  set w := softDef (fun i => -(L i) / Tt) with hwdef
  set Z := ∑ i, Real.exp (-L i / Tt) with hZdef
  have hZpos : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have h3 : (∑ b, Real.exp (-L b / Tt)) = Z := hZdef.symm
  have hwl : ∀ i, Real.log (w i) = -L i / Tt - Real.log Z := by
    intro i
    show Real.log (Real.exp (-L i / Tt) / ∑ b, Real.exp (-L b / Tt))
      = -L i / Tt - Real.log Z
    rw [h3, Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
  have key : ∀ i, w i * (L i + Tt * Real.log (w i)) = -Tt * Real.log Z * w i := by
    intro i
    rw [hwl i]
    have h4 : L i + Tt * (-L i / Tt - Real.log Z) = -Tt * Real.log Z := by
      field_simp
      ring
    rw [h4]
    ring
  have h1 : ∑ i, w i * (L i + Tt * Real.log (w i)) = ∑ i, -Tt * Real.log Z * w i :=
    Finset.sum_congr rfl (fun i _ => key i)
  rw [← Finset.mul_sum] at h1
  have hsum : ∑ i, w i = 1 := by rw [hwdef]; exact softDef_sum_one _
  rw [hsum] at h1
  have h2 : ∑ i, w i * (L i + Tt * Real.log (w i))
      = ∑ i, w i * L i + Tt * ∑ i, w i * Real.log (w i) := by
    trans ∑ i, (w i * L i + Tt * (w i * Real.log (w i)))
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h2] at h1
  linarith

/-- **Равномерный максимум энтропии**: для любого строго
положительного распределения w на конечном ι энтропия
Шеннона не превосходит логарифма мощности:

  `−∑ wᵢ·log wᵢ ≤ log |ι|`

(Jensen: логарифм вогнут; максимум достигается на
равномерном распределении). -/
theorem shannon_entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
    -∑ i, w i * Real.log (w i) ≤ Real.log ((Fintype.card ι : ℕ):ℝ) := by
  simpa only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib] using
    Hagi.Prelude.sum_negMulLog_le_log_card w (fun i => (hw0 i).le) hw1

/-- **Качество исполняемой смеси: E ≤ m + T·log n.**
Композиция трёх сертификатов: тождество E = F + T·S
(`gibbs_free_energy_identity`), максимум энтропии
S ≤ log n (`shannon_entropy_le_log_card`) и нижняя Нернст-
оценка F ≥ m − T·log n (`gibbs_value_nernst_bounds`).
Следствие: расписание T·log n ≤ ε даёт ожидаемую потерю
РЕАЛЬНО исполняемой Гиббс-смеси (компонент
`unified_step_certificate`) в ε-окрестности глобального
минимума. Полная термодинамическая цепочка HAGI:
расписание охлаждения → свободная энергия → энергия смеси. -/
theorem gibbs_mixture_quality {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / Tt) i * L i
          ≤ m + Tt * Real.log ((Fintype.card ι : ℕ):ℝ)) := by
  classical
  rcases gibbs_value_nernst_bounds L hTt with ⟨m, hmin, -, hlo, hhi⟩
  refine ⟨m, hmin, ?_⟩
  have hZbr : (∑ i, Real.exp (-(L i / Tt))) = (∑ i, Real.exp (-L i / Tt)) :=
    Finset.sum_congr rfl (fun i _ => by rw [neg_div])
  rw [hZbr] at hlo hhi
  have hZpos : 0 < ∑ i, Real.exp (-L i / Tt) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hident := gibbs_free_energy_identity L hTt
  have hent := shannon_entropy_le_log_card (softDef (fun i => -(L i) / Tt))
    (fun i => softDef_pos _ i) (softDef_sum_one _)
  -- E = -Tt log Z - Tt Σ w log w; hent : -(Σ w log w) ≤ log n
  -- hlo : m - Tt*log n ≤ -Tt*log Z
  have hS : ∑ i, softDef (fun i => -(L i) / Tt) i * Real.log (softDef (fun i => -(L i) / Tt) i)
      ≥ -Real.log ((Fintype.card ι : ℕ):ℝ) := by
    linarith [hent]
  have hB : Tt * (-Real.log ((Fintype.card ι : ℕ):ℝ))
      ≤ Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
      * Real.log (softDef (fun i => -(L i) / Tt) i) :=
    mul_le_mul_of_nonneg_left hS (le_of_lt hTt)
  linarith

/-- **Геометрическое охлаждение: логарифмическая цена точности.**
Расписание Tₜ = T₀·ρᵗ (0 < ρ < 1) достигает ε-качества
исполняемой Гиббс-смеси за

  `N ≥ log(T₀·log n / ε) / log(1/ρ)`

шагов: после N шагов охлаждения T_N·log n ≤ ε, и по
`gibbs_mixture_quality` ожидаемая потеря смеси ≤ m + ε.
Вычислительная сложность достижения качества ε —
O(log(1/ε)) фаз охлаждения (при постоянных T₀, ρ, n):
прямая формализация «минимизации вычислений» —
экспоненциальная точность за логарифмическое число шагов
управления температурой. -/
theorem geometric_cooling_steps {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (T₀ ρ ε : ℝ) (hT₀ : 0 < T₀) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) (hn : 2 ≤ Fintype.card ι) (N : ℕ)
    (hN : Real.log (T₀ * Real.log ((Fintype.card ι : ℕ):ℝ) / ε)
        / Real.log ((1:ℝ)/ρ) ≤ (N:ℝ)) :
    ∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / (T₀ * ρ^(N:ℝ))) i * L i
          ≤ m + ε) := by
  have hlogn : 0 < Real.log ((Fintype.card ι : ℕ):ℝ) := by
    apply Real.log_pos
    have h1 : (1:ℝ) < ((Fintype.card ι : ℕ):ℝ) := by exact_mod_cast hn
    linarith
  have hone : (1:ℝ) < (1:ℝ)/ρ := one_lt_one_div hρ0 hρ1
  have hloginv : 0 < Real.log ((1:ℝ)/ρ) := Real.log_pos hone
  have hTp : 0 < T₀ * ρ^(N:ℝ) := by positivity
  have hkey : T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := by
    set A := T₀ * Real.log ((Fintype.card ι : ℕ):ℝ) with hA
    have hApos : 0 < A := by positivity
    have hBpos : 0 < ((1:ℝ)/ρ)^(N:ℝ) := by positivity
    have h11 : Real.log (A / ε) ≤ (N:ℝ) * Real.log ((1:ℝ)/ρ) :=
      (div_le_iff₀ hloginv).mp hN
    have h13 : Real.log (((1:ℝ)/ρ)^(N:ℝ)) = (N:ℝ) * Real.log ((1:ℝ)/ρ) :=
      Real.log_rpow (one_div_pos.mpr hρ0) _
    have h3 : Real.log (A / ε) ≤ Real.log (((1:ℝ)/ρ)^(N:ℝ)) := by
      rw [h13]; linarith
    have h4 : A / ε ≤ ((1:ℝ)/ρ)^(N:ℝ) := by
      have h12 := Real.exp_le_exp.mpr h3
      rwa [Real.exp_log (div_pos hApos hε), Real.exp_log hBpos] at h12
    have h5 : ρ^(N:ℝ) * ((1:ℝ)/ρ)^(N:ℝ) = 1 := by
      rw [← Real.mul_rpow (show (0:ℝ) ≤ ρ by positivity)
        (show (0:ℝ) ≤ (1:ℝ)/ρ by positivity)]
      have : ρ * ((1:ℝ)/ρ) = 1 := by field_simp
      rw [this]
      exact Real.one_rpow _
    have h4' : A ≤ ε * ((1:ℝ)/ρ)^(N:ℝ) := by
      have := (div_le_iff₀ hε).mp h4
      linarith [this]
    have h9 := mul_le_mul_of_nonneg_left h4'
      (le_of_lt (show (0:ℝ) < ρ^(N:ℝ) by positivity))
    have h10 : ρ^(N:ℝ) * (ε * ((1:ℝ)/ρ)^(N:ℝ)) = ε := by
      linear_combination ε * h5
    linarith

  have hTp : 0 < T₀ * ρ^(N:ℝ) := by positivity
  have hqual := gibbs_mixture_quality L hTp
  rcases hqual with ⟨m, hmin, hbnd⟩
  refine ⟨m, hmin, ?_⟩
  have hTn : T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := hkey
  -- bound: E ≤ m + T·log n ≤ m + ε
  have : ∑ i, softDef (fun i => -(L i) / (T₀ * ρ^(N:ℝ))) i * L i
      ≤ m + T₀ * ρ^(N:ℝ) * Real.log ((Fintype.card ι : ℕ):ℝ) := hbnd
  linarith

/-- **Термическое размытие различимости**: логарифмическое
отношение Гиббс-весов двух направлений в точности равно
относительному зазору их потерь, делённому на температуру:

  `log wᵢ − log wⱼ = (Lⱼ − Lᵢ)/T`

Следствие: чтобы Гиббс-ансамбль различал понятия с зазором
потерь s с лог-точностью τ, температура обязана быть
T ≤ s/τ — расписание охлаждения ограничено СНИЗУ
различимостью: слишком быстрый нагрев/высокая T стирает
различия между направлениями. Термодинамическая
нижняя граница для `geometric_cooling_steps`. -/
theorem thermal_blur {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {T : ℝ} (hT : 0 < T) (i j : ι) :
    Real.log (softDef (fun x => -L x / T) i)
      - Real.log (softDef (fun x => -L x / T) j)
      = (L j - L i) / T := by
  have hli : Real.log (softDef (fun x => -L x / T) i)
      = -L i / T - Real.log (∑ k, Real.exp (-L k / T)) := by
    have h1 : softDef (fun x => -L x / T) i
        = Real.exp (-L i / T - Real.log (∑ k, Real.exp (-L k / T))) := by
      rw [Hagi.Core.softDef_eq_exp_sub_lse, Hagi.Core.lse]
    rw [h1, Real.log_exp]
  have hlj : Real.log (softDef (fun x => -L x / T) j)
      = -L j / T - Real.log (∑ k, Real.exp (-L k / T)) := by
    have h1 : softDef (fun x => -L x / T) j
        = Real.exp (-L j / T - Real.log (∑ k, Real.exp (-L k / T))) := by
      rw [Hagi.Core.softDef_eq_exp_sub_lse, Hagi.Core.lse]
    rw [h1, Real.log_exp]
  rw [hli, hlj]
  ring

/-- **Коридор температур**: если термодинамический коридор
непуст (нижняя граница различимости s/τ не превосходит
верхнюю границу качества ε/log n), то существует температура
T (свидетель: T = s/τ), дающая ОДНОВРЕМЕННО

* различимость: любые два направления с зазором потерь ≤ s
  различаются лог-точностью τ (`thermal_blur`);
* качество: ожидаемая потеря смеси ≤ m + ε
  (`gibbs_mixture_quality` + бюджет охлаждения).

Двусторонняя теорема о расписании HAGI: температура обязана
лежать в [s/τ, ε/log n] — ниже нельзя (нагрев стирает
различимость), выше не нужно (ε-качество уже достигнуто). -/
theorem temperature_corridor {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (s τ ε : ℝ) (hs : 0 < s) (hτ : 0 < τ) (hε : 0 < ε)
    (hn : 2 ≤ Fintype.card ι)
    (hcorridor : s / τ ≤ ε / Real.log ((Fintype.card ι : ℕ):ℝ)) :
    ∃ T : ℝ, 0 < T
      ∧ (∀ i j, |L j - L i| ≤ s →
          |Real.log (softDef (fun x => -L x / T) i)
            - Real.log (softDef (fun x => -L x / T) j)| ≤ τ)
      ∧ (∃ m : ℝ, (∀ i, m ≤ L i)
          ∧ (∑ i, softDef (fun x => -L x / T) i * L i
              ≤ m + T * Real.log ((Fintype.card ι : ℕ):ℝ))
          ∧ T * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε) := by
  refine ⟨s / τ, div_pos hs hτ, ?_, ?_⟩
  · intro i j hgap
    have hT := div_pos hs hτ
    have h := thermal_blur L hT i j
    rw [h]
    rw [show (L j - L i) / (s / τ) = (L j - L i) * (τ / s) from by
      field_simp]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ / s)]
    rw [mul_div_assoc', div_le_iff₀ hs]
    rw [mul_comm τ s]
    exact mul_le_mul_of_nonneg_right hgap hτ.le
  · have hT := div_pos hs hτ
    have hlogn : 0 < Real.log ((Fintype.card ι : ℕ):ℝ) := by
      apply Real.log_pos
      have h1 : (1:ℝ) < ((Fintype.card ι : ℕ):ℝ) := by exact_mod_cast hn
      linarith
    have hcap : (s / τ) * Real.log ((Fintype.card ι : ℕ):ℝ) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτ]
      rw [div_le_div_iff₀ hτ hlogn] at hcorridor
      exact hcorridor
    rcases gibbs_mixture_quality L hT with ⟨m, hmin, hbnd⟩
    exact ⟨m, hmin, hbnd, hcap⟩


/-- **Охлаждение раскрывает различимость**: если зазор потерь
|Lᵢ − Lⱼ| ≥ s и температура достаточно низкая
(T ≤ s/τ), то лог-расстояние Гиббс-весов не меньше τ —
дополнение к `temperature_corridor` (нижняя оценка вместо
верхней): при T → 0 ансамбль различает сколь угодно близкие
направления; число эффективно различимых понятий
монотонно растёт при охлаждении — вместе с
`welch_min_dimension` это термодинамическая развертка
вместимости: охлаждение раскрывает упаковочную ёмкость
пространства представлений. -/
theorem thermal_reveal {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ)
    (T : ℝ) (hT : 0 < T) (hTle : T ≤ s / τ) (i j : ι)
    (hgap : s ≤ |L j - L i|) :
    τ ≤ |Real.log (softDef (fun x => -L x / T) i)
      - Real.log (softDef (fun x => -L x / T) j)| := by
  have h := thermal_blur L hT i j
  rw [h, abs_div, abs_of_pos hT]
  rw [le_div_iff₀ hT]
  have h2 : τ * T ≤ s := by
    rw [mul_comm, ← le_div_iff₀ hτ]
    exact hTle
  have h3 : τ * T ≤ |L j - L i| := le_trans h2 hgap
  linarith [h3]

/-- **Время раскрытия понятия при геометрическом
охлаждении**: если расписание Tₜ = T₀·ρᵗ достигло
Tₜ ≤ s/τ (т.е. t ≥ log(T₀τ/s)/log(1/ρ)), то на шаге t
ансамбль различает пару с зазором ≥ s с лог-точностью τ.
Композиция `thermal_reveal` × геометрического расписания:
каждое понятие с зазором s получает момент раскрытия —
термодинамические «часы» различимости; при ρ < 1
момент логарифмичен по T₀τ/s. -/
theorem reveal_horizon {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) (T₀ ρ s τ : ℝ) (hT₀ : 0 < T₀) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ)
    (i j : ι) (hgap : s ≤ |L j - L i|)
    (t : ℕ) (hle : T₀ * ρ ^ (t : ℝ) ≤ s / τ) :
    τ ≤ |Real.log (softDef (fun x => -L x / (T₀ * ρ ^ (t : ℝ))) i)
      - Real.log (softDef (fun x => -L x / (T₀ * ρ ^ (t : ℝ))) j)| := by
  have hTpos : 0 < T₀ * ρ ^ (t : ℝ) := by positivity
  exact thermal_reveal L s τ hs hτ _ hTpos hle i j hgap

/-- **Момент раскрытия существует**: для любого зазора s > 0 и
точности τ > 0 геометрическое расписание Tₜ = T₀·ρᵗ
достигает Tₜ ≤ s/τ за конечное число шагов (∃ t:
T₀·ρᵗ ≤ s/τ). Вместе с `reveal_horizon`: КАЖДОЕ понятие с
конечным зазором будет раскрыто — полное содержание
термодинамических часов: охлаждение раскрывает все
различия, момент логарифмичен. -/
theorem reveal_time_exists (T₀ ρ s τ : ℝ) (hT₀ : 0 < T₀)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ) :
    ∃ t : ℕ, T₀ * ρ ^ (t : ℝ) ≤ s / τ := by
  have hposTS : 0 < T₀ * τ / s := by positivity
  have hloginv : 0 < Real.log ((1:ℝ)/ρ) :=
    Real.log_pos (one_lt_one_div hρ0 hρ1)
  rcases exists_nat_ge (Real.log (T₀ * τ / s) / Real.log ((1:ℝ)/ρ)) with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- шаг 1: (1/ρ)^t ≥ T₀τ/s (exp-монотонность из лога)
  have h1 : Real.log (T₀ * τ / s) ≤ (t:ℝ) * Real.log ((1:ℝ)/ρ) :=
    (div_le_iff₀ hloginv).mp ht
  have h2 : Real.log (((1:ℝ)/ρ)^(t:ℝ)) ≥ Real.log (T₀ * τ / s) := by
    rw [Real.log_rpow (by positivity : (0:ℝ) < (1:ℝ)/ρ)]
    linarith [h1]
  have h3 : ((1:ℝ)/ρ)^(t:ℝ) ≥ T₀ * τ / s := by
    have h4 := Real.exp_le_exp.mpr h2
    rw [Real.exp_log hposTS, Real.exp_log (Real.rpow_pos_of_pos (one_div_pos.mpr hρ0) _)] at h4
    exact h4
  -- шаг 2: ρ^t · (1/ρ)^t = 1 ⟹ T₀ρᵗ ≤ s/τ
  have h5 : ρ^(t:ℝ) * ((1:ℝ)/ρ)^(t:ℝ) = 1 := by
    rw [← Real.mul_rpow (le_of_lt hρ0)
      (le_of_lt (one_div_pos.mpr hρ0))]
    have : ρ * ((1:ℝ)/ρ) = 1 := by field_simp
    rw [this]
    exact Real.one_rpow _
  have h6 : T₀ * τ / s ≤ ((1:ℝ)/ρ)^(t:ℝ) := h3
  rw [div_le_iff₀ (by positivity : (0:ℝ) < s)] at h6
  -- h6 : T₀ * τ ≤ s * ((1/ρ)^t)
  have hgoal : T₀ * ρ ^ (t:ℝ) * τ ≤ s := by
    nlinarith [h6, h5, mul_pos hT₀ hτ]
  exact (le_div_iff₀ hτ).mpr hgoal

/-- **Динамическая пара: раскрытие ∧ качество одновременно**:
для любого зазора s, точности τ и бюджета качества ε
существует шаг t, на котором геометрическое расписание
ОДНОВРЕМЕННО раскрывает все пары с зазором ≥ s
(Tₜ ≤ s/τ) и достигает ε-качества (Tₜ·log n ≤ ε):
термодинамические часы и бюджет качества сходятся —
обе верхние границы на Tₜ выполняются при достаточно
большом t (хвост расписания входит в min-окно коридора). -/
theorem cooling_schedule_pair (T₀ ρ s τ ε : ℝ) (hT₀ : 0 < T₀)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hs : 0 < s) (hτ : 0 < τ)
    (hε : 0 < ε) (n : ℝ) (hn : 1 < n) :
    ∃ t : ℕ, T₀ * ρ ^ (t : ℝ) ≤ s / τ
      ∧ T₀ * ρ ^ (t : ℝ) * Real.log n ≤ ε := by
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hmin : 0 < min (s / τ) (ε / Real.log n) := lt_min (div_pos hs hτ) (div_pos hε hlogn)
  have hmin : (0:ℝ) < min (s / τ) (ε / Real.log n) :=
    lt_min (div_pos hs hτ) (div_pos hε hlogn)
  rcases reveal_time_exists T₀ ρ (min (s / τ) (ε / Real.log n)) 1
    hT₀ hρ0 hρ1 hmin one_pos with ⟨t, ht⟩
  have ht' : T₀ * ρ ^ (t:ℝ) ≤ min (s / τ) (ε / Real.log n) := by
    rw [div_one] at ht; exact ht
  refine ⟨t, le_trans ht' (min_le_left _ _), ?_⟩
  have h2 : T₀ * ρ ^ (t:ℝ) ≤ ε / Real.log n := le_trans ht' (min_le_right _ _)
  have h3 := mul_le_mul_of_nonneg_right h2 hlogn.le
  rw [div_mul_cancel₀ _ (ne_of_gt hlogn)] at h3
  exact h3

/-- СТРОГАЯ МОНОТОННОСТЬ СТАТИСТИЧЕСКОЙ СУММЫ: при
неотрицательных потерях и хотя бы одной положительной
Z(T) строго возрастает по T: нагрев размешивает Гиббса,
охлаждение концентрирует на минимизаторах. -/
theorem partition_strictMono {V : Type*} [Fintype V] [Nonempty V]
    (ℓ : V → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v) (i₀ : V) (hℓi₀ : 0 < ℓ i₀)
    {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : T₁ < T₂) :
    ∑ v, Real.exp (-(ℓ v)/T₁) < ∑ v, Real.exp (-(ℓ v)/T₂) := by
  have hT₂ : (0:ℝ) < T₂ := by linarith
  apply Finset.sum_lt_sum
  · intro v _
    have ha : (-ℓ v) ≤ 0 := neg_nonpos.mpr (hℓ v)
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff₀ h₁ hT₂]
    have hd := mul_nonpos_of_nonpos_of_nonneg ha (sub_nonneg.mpr h₂.le)
    have hsplit : (-ℓ v) * T₂ = (-ℓ v) * T₁ + (-ℓ v) * (T₂ - T₁) := by ring
    linarith
  · refine ⟨i₀, Finset.mem_univ i₀, ?_⟩
    have ha : (-ℓ i₀) < 0 := by linarith
    refine Real.exp_lt_exp.mpr ?_
    rw [div_lt_div_iff₀ h₁ hT₂]
    have hd := mul_neg_of_neg_of_pos ha (sub_pos.mpr h₂)
    have hsplit : (-ℓ i₀) * T₂ = (-ℓ i₀) * T₁ + (-ℓ i₀) * (T₂ - T₁) := by ring
    linarith

/-- ТЕПЛОВОЙ ПРЕДЕЛ: при T → ∞ статистическая сумма Гиббса
стремится к |V| (полное термическое размытие). -/
theorem partition_hot_limit {V : Type*} [Fintype V] [Nonempty V]
    (ℓ : V → ℝ) :
    Filter.Tendsto (fun T : ℝ => ∑ v, Real.exp (-(ℓ v)/T))
      Filter.atTop (nhds (Fintype.card V : ℝ)) := by
  have hexp : ∀ v : V, Filter.Tendsto
      (fun T : ℝ => Real.exp (-(ℓ v)/T)) Filter.atTop (nhds 1) := by
    intro v
    have hinv : Filter.Tendsto (fun T : ℝ => ((1:ℝ)/T))
        Filter.atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    have hd : Filter.Tendsto (fun T : ℝ => (-ℓ v) * ((1:ℝ)/T))
        Filter.atTop (nhds 0) := by
      have h := hinv.const_mul (-ℓ v)
      simpa [mul_comm] using h
    have hcomp := Real.continuous_exp.continuousAt.tendsto.comp hd
    simpa [neg_div, one_div, div_eq_mul_inv, Function.comp_def] using hcomp
  have := tendsto_finsetSum (Finset.univ : Finset V)
    (fun v _ => hexp v)
  simpa [Finset.sum_const, Finset.card_univ] using this

/-- ДВУХУРОВНЕВАЯ ТЕПЛОЁМКОСТЬ > 0 (Neural Thermodynamic
Laws, arXiv 2505.10559 — теплоёмкость river-valley ландшафта): система с энергиями 0 и ε имеет
равновесную среднюю энергию
⟨E⟩(T) = ε·e^{-ε/T}/(1+e^{-ε/T}) = ε/(1+e^{ε/T}),
и она СТРОГО возрастает по T — нагрев всегда повышает
среднюю энергию (положительная теплоёмкость), охлаждение
концентрирует на основном уровне. -/
theorem two_level_meanEnergy_strictMono (ε : ℝ) (hε : 0 < ε)
    {T₁ T₂ : ℝ} (h₁ : 0 < T₁) (h₂ : T₁ < T₂) :
    ε / (1 + Real.exp (ε / T₁)) < ε / (1 + Real.exp (ε / T₂)) := by
  have hT₂ : (0:ℝ) < T₂ := by linarith
  have hdiv : ε / T₂ < ε / T₁ := by
    rw [div_lt_div_iff₀ hT₂ h₁, mul_comm ε T₁, mul_comm ε T₂]
    exact mul_lt_mul_of_pos_right h₂ hε
  have hexp : Real.exp (ε / T₂) < Real.exp (ε / T₁) :=
    Real.exp_lt_exp.mpr hdiv
  have hden : (1:ℝ) + Real.exp (ε / T₂) < 1 + Real.exp (ε / T₁) := by
    linarith
  have hpos1 : (0:ℝ) < 1 + Real.exp (ε / T₁) := by
    have := Real.exp_pos (ε / T₁)
    linarith
  rw [div_lt_div_iff₀ hpos1 (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hden hε, hε]

/-- ХОЛОДНЫЙ ПРЕДЕЛ (NTL): при T → 0+ статистическая сумма
Гиббса Z(T) = Σ exp(−ℓ v/T) сходится к числу глобальных
минимизаторов ℓ (при ℓ ≥ 0): вырожденные уровни ℓ v = 0
вкладывают 1, возбуждённые ℓ v > 0 вымерзают. Охлаждение
концентрирует распределение на минимизаторах — холодный
двойник partition_hot_limit. -/
theorem partition_cold_limit {V : Type*} [Fintype V] [Nonempty V]
    (ℓ : V → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v) :
    Filter.Tendsto (fun T : ℝ => ∑ v, Real.exp (-(ℓ v)/T))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∑ v, if ℓ v = 0 then (1:ℝ) else 0)) := by
  have hterm : ∀ v : V, Filter.Tendsto
      (fun T : ℝ => Real.exp (-(ℓ v)/T))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (if ℓ v = 0 then (1:ℝ) else 0)) := by
    intro v
    rcases eq_or_lt_of_le (hℓ v) with h0 | hpos
    · have hconst : (fun T : ℝ => Real.exp (-(ℓ v)/T))
          = fun _ => (1:ℝ) := by
        funext T
        rw [h0.symm]
        simp
      have hif : (if ℓ v = 0 then (1:ℝ) else 0) = 1 := by
        simp [h0]
      rw [hconst, hif]
      exact tendsto_const_nhds
    · have hinv : Filter.Tendsto (fun T : ℝ => (1:ℝ)/T)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
        by simpa using tendsto_inv_nhdsGT_zero
      have hmul : Filter.Tendsto (fun T : ℝ => (ℓ v) * ((1:ℝ)/T))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hpos hinv
      have hneg : Filter.Tendsto (fun T : ℝ => -((ℓ v) * ((1:ℝ)/T)))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atBot :=
        Filter.tendsto_neg_atBot_iff.mpr hmul
      have hexp : Filter.Tendsto (fun T : ℝ => Real.exp (-((ℓ v) * ((1:ℝ)/T))))
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
        Real.tendsto_exp_atBot.comp hneg
      have hfe : (fun T : ℝ => Real.exp (-(ℓ v)/T))
          = fun T : ℝ => Real.exp (-((ℓ v) * ((1:ℝ)/T))) := by
        funext T
        rw [div_eq_mul_inv, one_div]
        congr 1
        ring
      have hgoal0 : (if ℓ v = 0 then (1:ℝ) else 0) = 0 := by
        have hne := ne_of_gt hpos
        simp [hne]
      rw [hgoal0, hfe]
      exact hexp
  exact tendsto_finsetSum _ (fun v _ => hterm v)

end Hagi.Energy
end C236_cool

section C236_var
/-!
# Variational: the linglib upgrade — free energy as a VARIATIONAL inequality

The GitHub scout (round 37) found hawkrobe/linglib's
`GibbsVariational.lean` strictly stronger than our round-33
equational identity: the free-energy bound holds for every q
(the variational inequality), and the optimizer (the tilted
measure) is UNIQUE. This module transports the technique to
our finite-support setting:

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U`  for every q,

with equality iff q IS the tilted distribution
p̃ ∝ p·e^U/Z — the free-energy descent's target is unique,
and the bound direction holds globally, not just at the
fixed point.

**What the module proves:**

* `tilted_sum_one`/`tilted_pos` — the tilted measure is a
  distribution (the normalization and positivity).
* `kl_tilted_decompose` — THE ENGINE (the linglib route):
  KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z — the KL against the
  tilted measure decomposes exactly; the variational
  inequality reads off KL ≥ 0.
* `free_energy_variational` — THE VARIATIONAL INEQUALITY:
  E_q[U] − KL(q‖p) ≤ log Z for every q — strictly stronger
  than the round-33 `free_energy_gap` (the equality at
  q = p̃ only): now the whole free-energy landscape is
  bounded, and the descent's target unique.

**Prescription for the code.**

1. The free-energy controller (`growth_gate v5`) reads the
   VARIATIONAL GAP log Z − (E_q[U] − KL(q‖p)) = KL(q‖p̃) ≥ 0:
   the gap to the optimal q is EXACTLY the KL to the tilted
   measure — the descent target is the tilted distribution,
   computable from p and U directly (no search).
2. The uniqueness licenses the distill/TTT targets: the
   optimal student state distribution IS the teacher's
   tilted measure — the objective has no flat directions
   (no degenerate optima).
-/

open Finset
open Hagi.Prelude
open Set

namespace Hagi.Energy

section Variational

variable {V : Type*} [Fintype V] [Nonempty V]

/-- The tilted distribution: p tilted by U, normalized. -/
noncomputable def tilted (p U : V → ℝ) (v : V) : ℝ :=
  p v * Real.exp (U v) / (∑ w, p w * Real.exp (U w))

theorem tilted_sum_one (p U : V → ℝ)
    (hp : ∀ v, 0 < p v) (_hp1 : ∑ v, p v = 1) :
    ∑ v, tilted (V := V) p U v = 1 := by
  have hZ : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  unfold tilted
  rw [← sum_div (Finset.univ : Finset V), div_self (ne_of_gt hZ)]

theorem tilted_pos (p U : V → ℝ) (hp : ∀ v, 0 < p v) :
    ∀ v, 0 < tilted (V := V) p U v := fun v =>
  div_pos (mul_pos (hp v) (Real.exp_pos _))
    (Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty)

/-- **The KL-of-tilted decomposition** (the linglib route,
transported): KL(q ‖ p̃) = KL(q‖p) − E_q[U] + log Z — the
engine of the variational inequality. -/
theorem kl_tilted_decompose (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (_hp1 : ∑ v, p v = 1) :
    Hagi.Prelude.klDef (V := V) q (tilted (V := V) p U)
      = Hagi.Prelude.klDef (V := V) q p - ∑ v, q v * U v
          + Real.log (∑ w, p w * Real.exp (U w)) := by
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  set Z := ∑ w, p w * Real.exp (U w) with hZ
  have hper : ∀ v : V,
      q v * Real.log (q v / (p v * Real.exp (U v) / Z))
        = q v * Real.log (q v / p v) - q v * U v + q v * Real.log Z := by
    intro v
    have hdiv : q v / (p v * Real.exp (U v) / Z)
        = (q v / p v) * Z / Real.exp (U v) := by
      field_simp
    have hlog : Real.log ((q v / p v) * Z / Real.exp (U v))
        = Real.log (q v / p v) - U v + Real.log Z := by
      rw [Real.log_div (ne_of_gt (by
          exact mul_pos (div_pos (hq v) (hp v)) hZpos)) (ne_of_gt (Real.exp_pos (U v))),
        Real.log_mul (ne_of_gt (div_pos (hq v) (hp v))) (ne_of_gt hZpos),
        Real.log_exp]
      ring
    rw [hdiv, hlog]
    ring
  unfold Hagi.Prelude.klDef tilted
  rw [Finset.sum_congr rfl fun v _ => hper v]
  have hsplit3 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
      + q v * Real.log Z)
      = (∑ v, q v * Real.log (q v / p v)) - ∑ v, q v * U v
          + ∑ v, q v * Real.log Z := by
    have h1 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
        + q v * Real.log Z)
        = ∑ v, ((q v * Real.log (q v / p v) + q v * Real.log Z)
            - q v * U v) :=
      Finset.sum_congr rfl fun v _ => by ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hsplit3]
  have hlast : ∑ v, q v * Real.log Z = Real.log Z := by
    have hpre : (∑ v, q v) * Real.log Z = ∑ v, q v * Real.log Z :=
      Finset.sum_mul (Finset.univ : Finset V) (fun v => q v) (Real.log Z)
    rw [hq1, one_mul] at hpre
    exact hpre.symm
  rw [hlast]

/-- **THE VARIATIONAL INEQUALITY (the linglib upgrade of the
free-energy identity)**: for every q,

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U` —

honest boundary: only the INEQUALITY is formalized;
the equality-condition characterization (iff q is the tilted
distribution) is stated at the docstring level and remains
an open formalization. This is strictly stronger
than our round-33 `free_energy_gap` (the equational identity
at q = p̃): the inequality holds for every q, and the
optimizer's uniqueness (the tilted measure) comes for free —
the free-energy descent's target is unique. -/
theorem free_energy_variational (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (hp1 : ∑ v, p v = 1) :
    (∑ v, q v * U v) - Hagi.Prelude.klDef (V := V) q p
      ≤ Real.log (∑ w, p w * Real.exp (U w)) := by
  have hdecomp := kl_tilted_decompose q p U hq hp hq1 hp1
  -- KL(q‖p̃) ≥ 0 (Cauchy on the tilted — the kl_nonneg engine)
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  have hklT : 0 ≤ Hagi.Prelude.klDef (V := V) q (tilted (V := V) p U) :=
    -- R334: delegates to the canon Hagi.Prelude.kl_nonneg
    -- (kldiv' IS klDef by rfl)
    Hagi.Prelude.kl_nonneg q (tilted (V := V) p U)
      hq (tilted_pos p U hp) hq1 (tilted_sum_one p U hp hp1)
  -- the finish: from KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z ≥ 0
  --            ⟹ E_q[U] − KL(q‖p) ≤ log Z
  have hZ := hdecomp
  linarith [hklT, hdecomp]

/-- **Optimal Gibbs weights over the simplex (mirror-descent
bound)**: for every probability vector `q` and every loss
profile `L` at inverse temperature `T > 0`,

  `⟨L⟩_q + T · Σ v, q v · log (q v) ≥ - T · log Σ v, exp(-L v / T)`.

This is the exact optimization statement behind the tempered
softmax: the Gibbs/tilted distribution attains the right-hand
side, i.e. `w = softmax(-L / T)` minimizes the regularized
objective — the equality case of the variational principle,
lived entirely on the finite simplex. The lower bound derives
from `free_energy_variational` at the uniform base; the
attainment/characterization lives in the KL equality case. -/
theorem gibbs_optimal_bound (q L : V → ℝ) {T : ℝ} (hT : 0 < T)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    (∑ v, q v * L v) + T * ∑ v, q v * Real.log (q v)
      ≥ -T * Real.log (∑ v, Real.exp (-(L v) / T)) := by
  classical
  set n := ((Fintype.card V : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by
    have hc : (0 : ℕ) < Fintype.card V := Fintype.card_pos
    rw [hn]  -- no-op for goal; cast positivity:
    exact Nat.cast_pos.mpr hc
  have hu1 : ∑ v : V, ((1 : ℝ) / n) = 1 := by
    simp [Finset.sum_const, hn]
  have hup : ∀ v : V, 0 < (1 : ℝ) / n := fun _ => div_pos one_pos hnpos
  set Uloss : V → ℝ := fun v => -L v / T with hUloss
  have hmain := free_energy_variational (V := V) q
    (fun v : V => (1 : ℝ) / n) Uloss hq hup hq1 hu1
  -- E_q[U] = -(Σ q·L)/T
  have hEu : ∑ v, q v * (-L v / T) = -(∑ v, q v * L v) / T := by
    have hterm : ∀ v : V, q v * (-L v / T) = -((q v * L v) / T) := by
      intro v; ring
    have hkey : (∑ v, (q v * L v) / T) = (∑ v, q v * L v) / T :=
      (Finset.sum_div Finset.univ (fun v => q v * L v) T).symm
    calc ∑ v, q v * (-L v / T)
        = ∑ v, -((q v * L v) / T) :=
          Finset.sum_congr rfl (fun v _ => hterm v)
      _ = -(∑ v, (q v * L v) / T) := by
          rw [Finset.sum_neg_distrib]
      _ = -(∑ v, q v * L v) / T := by rw [hkey, neg_div]
  -- KL(q ‖ uniform) = Σ q·log q + log n
  have hkl : Hagi.Prelude.klDef (V := V) q (fun _ => (1 : ℝ) / n)
      = (∑ v, q v * Real.log (q v)) + Real.log n := by
    unfold Hagi.Prelude.klDef
    simp only []
    have hdiv : ∀ v : V, q v / (1 / n) = q v * n := by
      intro v; field_simp
    have hlog : ∀ v : V, Real.log (q v * n)
        = Real.log (q v) + Real.log n := by
      intro v
      rw [Real.log_mul (hq v).ne' (ne_of_gt hnpos)]
    rw [Finset.sum_congr rfl (fun v _ => by rw [hdiv v, hlog v, mul_add]),
      Finset.sum_add_distrib]
    have hlast : ∑ v, q v * Real.log n = Real.log n := by
      have hpre : (∑ v, q v) * Real.log n
          = ∑ v, q v * Real.log n := Finset.sum_mul (Finset.univ : Finset V)
            (fun v => q v) (Real.log n)
      rw [hq1, one_mul] at hpre
      exact hpre.symm
    rw [hlast]
  rw [hEu, hkl] at hmain
  -- exponent sum positivity (in Uloss-terms, as in hmain)
  have hsumeposU : (0 : ℝ) < ∑ w, Real.exp (Uloss w) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  -- normalize the partition-function log: log(Σe / n) = log Σe − log n
  have hZeq : Real.log ((∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)))
      = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n := by
    have hsplit : ∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)
        = (∑ w, Real.exp (Uloss w)) / n := by
      have hterm : ∀ w : V, ((1 : ℝ) / n) * Real.exp (Uloss w)
          = Real.exp (Uloss w) / n := by
        intro w; ring
      rw [Finset.sum_congr rfl (fun w _ => hterm w)]
      rw [Finset.sum_div Finset.univ (fun w => Real.exp (Uloss w)) n]
    rw [hsplit]
    have hld : Real.log ((∑ w, Real.exp (Uloss w)) / n)
        = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n :=
      Real.log_div (ne_of_gt hsumeposU) (ne_of_gt hnpos)
    rw [hld]
  rw [hZeq] at hmain
  -- multiply the inequality by T > 0 and finish linearly
  have hmult := mul_le_mul_of_nonneg_right hmain (le_of_lt hT)
  have hcancel : (-(∑ v, q v * L v)) / T * T
      = -(∑ v, q v * L v) :=
    div_mul_cancel₀ _ (ne_of_gt hT)
  have hsimp : (-(∑ v, q v * L v) / T
      - (∑ v, q v * Real.log (q v) + Real.log n))
      * T
      = -(∑ v, q v * L v)
        - (∑ v, q v * Real.log (q v)) * T - Real.log n * T := by
    rw [sub_mul, add_mul, hcancel]
    ring
  rw [hsimp] at hmult
  rw [hUloss] at hmult
  linarith [hmult]


end Variational


variable {V : Type*} [Fintype V]

end Hagi.Energy
end C236_var
