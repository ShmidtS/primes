/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Learning.SoftRouterTotal

set_option linter.style.header false

/-!
# SleepingRouter — sleeping-experts regret мягкого роутера (цикл 21)

C325 закрывает honest gap C320 (`SoftRouterTotal`): у Hedge-носителя
нет механизма спящих экспертов — веса обновляются по ВСЕМ экспертам
каждый раунд, поэтому его regret не покрывает конкуренцию с лучшим
ДОСТУПНЫМ экспертом, когда guard-гатенные эксперты спят на части
раундов. Здесь — классический imputed-loss редукционный трюк
(Freund–Schapire share updates / specialists; вывод —
`.tmp/C325/research.md`):

* спящие эксперты обновляются ПОТЕРЕЙ СМЕСИ m_t (не своими ℓ):
  `w(t+1,i) = w(t,i)·(if awake then e^{-ηℓ} else e^{-η m_t})`;
* KEY IDENTITY `swWeight_eq_ewWeight`: этот процесс ОПРЕДЕЛЕНИЯМИ
  совпадает с `ewWeight (swLoss l a eta) eta` на импутированных
  потерях `swLoss t i = if awake then ℓ else m_t` — весь носитель
  (`hsurv_derived` + `router_regret_bound`) применяется ДОСЛОВНО,
  без изменений доказательства;
* SELF-CONSISTENCY `algLoss_eq_mixLoss`: потери алгоритма (полная
  нормировка ewNorm) на импутированных потерях РАВНЫ m_t —
  awake-часть даёт (P/W)·m_t, asleep-часть (1−P/W)·m_t;
* ТЕЛЕСКОП-КАНЦЕЛЯЦИЯ: `Σ_{t: i awake}(m_t − ℓ_t^i) = A − L*` —
  асимные члены `Σ_{asleep(i)} m_t` сокращаются ТОЧНО (равенство,
  даже неотрицательность m_t не нужна).

Итог — `sleeping_hedge_regret` (носитель) и
`sleeping_router_total_bound` (композиция C320, апгрейд): мягкий
роутер конкурирует с ЛЮБЫМ экспертом i НА ЕГО СОБСТВЕННЫХ
ДОСТУПНЫХ РАУНДАХ — total mixture CE ≤ Σ_{t: i awake} CE_i +
log N/η + η·T/2 при по-раундовой калибровке `soft_router_ce_bound`
(C319) на awake-supported симплекс-весах `swPredW`.

Challenge-pins (честные границы):

* AWAKE-NONEMPTY: посылка «в каждом раунде хоть один эксперт
  доступен» — СТОЯЩАЯ предпосылка (раунд без доступных экспертов не
  имеет предсказания; исключён моделированием, не замят молча).
* ДИАПАЗОН ПОТЕРЬ: `m_t ∈ [0,1]` ВЫВЕДЕНО (`mixLossOf_mem`: выпуклая
  комбинация awake-потерь из [0,1]) — посылка hedge_step не
  протащена, а доказана.
* SCOPE: последовательности oblivious (адаптивный адверсарий НЕ
  заявлен — скоуп носителя наследован дословно); regret против
  ФИКСИРОВАННОГО эксперта на его awake-раундах; best-switching
  последовательность экспертов НЕ заявлена (fixed-share — future).
* ПРЕДСКАЗАНИЕ: смесь логитов по awake-supported весам `swPredW`
  (спящие эксперты исключены из предсказания гвардом; их веса
  эволюционируют импутацией и возвращаются при пробуждении).
-/

namespace Hagi.Learning.SleepingRouter

open Hagi.Autonomy Hagi.Learning.SoftRouterMix

section Carrier

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- `awPot` — масса весов по awake-множеству (фильтр `A i = true`). -/
noncomputable def awPot (w : ι → ℝ) (A : ι → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i

/-- `mixLossOf` — awake-нормированная потеря смеси:
`Σ_{i∈A} (w i / Σ_{j∈A} w j) · ℓ i` — нормировка по AWAKE-множеству
(решение носителя: предсказание поддержано только на доступных
экспертах). -/
noncomputable def mixLossOf (w : ι → ℝ) (lt : ι → ℝ) (A : ι → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => A i = true),
    w i / awPot w A * lt i

/-- `swWeight` — спящие веса: awake-эксперты обновляются своей
потерей, asleep — потерей смеси (imputed share update). -/
noncomputable def swWeight (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ) :
    ℕ → ι → ℝ
  | 0, _ => 1
  | t + 1, i =>
      swWeight l a eta t i *
        (if a t i = true then Real.exp (-eta * l t i)
         else Real.exp (-eta * mixLossOf (swWeight l a eta t) (l t) (a t)))

/-- `swMixLoss` — потеря awake-смеси в раунде t. -/
noncomputable def swMixLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) : ℝ :=
  mixLossOf (swWeight l a eta t) (l t) (a t)

/-- `swLoss` — импутированная последовательность потерь:
awake → своя потеря, asleep → потеря смеси. -/
noncomputable def swLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (i : ι) : ℝ :=
  if a t i = true then l t i else swMixLoss l a eta t

theorem swWeight_pos (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (i : ι) : 0 < swWeight l a eta t i := by
  induction t generalizing i with
  | zero => simp [swWeight]
  | succ t ih =>
      simp only [swWeight]
      split <;> exact mul_pos (ih i) (Real.exp_pos _)

theorem awPot_pos (w : ι → ℝ) (A : ι → Bool) (h : ∃ j, A j = true)
    (hw : ∀ i, 0 < w i) : 0 < awPot w A := by
  obtain ⟨j, hj⟩ := h
  unfold awPot
  have hmem : j ∈ Finset.univ.filter (fun i => A i = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  exact Finset.sum_pos' (fun i _ => (hw i).le) ⟨j, hmem, hw j⟩

theorem awNorm_sum (w : ι → ℝ) (A : ι → Bool) (h : ∃ j, A j = true)
    (hw : ∀ i, 0 < w i) :
    ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A = 1 := by
  have hP := awPot_pos w A h hw
  calc ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A
      = (∑ i ∈ Finset.univ.filter (fun i => A i = true), w i) / awPot w A :=
        (Finset.sum_div _ _ _).symm
    _ = 1 := div_self (ne_of_gt hP)

theorem mixLossOf_mem (w : ι → ℝ) (lt : ι → ℝ) (A : ι → Bool)
    (h : ∃ j, A j = true) (hw : ∀ i, 0 < w i)
    (hl : ∀ i, 0 ≤ lt i ∧ lt i ≤ 1) :
    0 ≤ mixLossOf w lt A ∧ mixLossOf w lt A ≤ 1 := by
  have hP := awPot_pos w A h hw
  have hsum := awNorm_sum w A h hw
  refine ⟨Finset.sum_nonneg fun i _ =>
    mul_nonneg (div_nonneg (hw i).le hP.le) (hl i).1, ?_⟩
  have hle : mixLossOf w lt A
      ≤ ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A :=
    Finset.sum_le_sum fun i _ => by
      have h4 := mul_le_mul_of_nonneg_left (hl i).2
        (div_nonneg (hw i).le hP.le)
      simpa only [mul_one] using h4
  rw [hsum] at hle
  exact hle

/-- KEY IDENTITY: спящий процесс — это в точности Hedge (`ewWeight`)
на импутированных потерях (индукция по t, обе ветки
определительные). Весь существующий носитель применим дословно. -/
theorem swWeight_eq_ewWeight (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) :
    ∀ i, swWeight l a eta t i = ewWeight (swLoss l a eta) eta t i := by
  induction t with
  | zero => intro i; simp [swWeight, ewWeight]
  | succ t ih =>
      have ihf : swWeight l a eta t = ewWeight (swLoss l a eta) eta t :=
        funext ih
      intro i
      simp only [swWeight, ewWeight, ihf]
      by_cases hA : a t i = true
      · rw [if_pos hA, swLoss, if_pos hA]
      · rw [if_neg hA, swLoss, if_neg hA, swMixLoss, ihf]

theorem ewPot_sw (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ) (t : ℕ) :
    ewPot (swLoss l a eta) eta t = ∑ j, swWeight l a eta t j := by
  unfold ewPot
  exact Finset.sum_congr rfl fun j _ =>
    (swWeight_eq_ewWeight l a eta t j).symm

/-- SELF-CONSISTENCY: потери алгоритма (полная нормировка `ewNorm`)
на импутированных потерях РАВНЫ awake-нормированной потере смеси:
awake-часть даёт (P/W)·m_t, asleep-часть (1−P/W)·m_t. -/
theorem algLoss_eq_mixLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (haw : ∃ j, a t j = true) :
    ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = swMixLoss l a eta t := by
  have hwt : ∀ j, 0 < swWeight l a eta t j := swWeight_pos l a eta t
  have hP : 0 < awPot (swWeight l a eta t) (a t) :=
    awPot_pos _ _ haw hwt
  set P : ℝ := awPot (swWeight l a eta t) (a t) with hPdef
  set W : ℝ := ewPot (swLoss l a eta) eta t with hWdef
  have hWpos : 0 < W := ewPot_pos _ _ _
  have hWval : W = ∑ j, swWeight l a eta t j := ewPot_sw l a eta t
  have hnorm : ∀ j, ewNorm (swLoss l a eta) eta t j
      = swWeight l a eta t j / W := by
    intro j
    unfold ewNorm
    rw [swWeight_eq_ewWeight l a eta t j]
  have hPM : P * swMixLoss l a eta t
      = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j * l t j := by
    unfold swMixLoss mixLossOf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hPdef]
    field_simp
  have hS : ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
      swWeight l a eta t j = W - P := by
    have hjoin := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => a t j = true) (fun j => swWeight l a eta t j)
    have hWall : W = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j
        + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
            swWeight l a eta t j := by rw [hWval, hjoin]
    have hPval : P
        = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
            swWeight l a eta t j := rfl
    linarith
  have hsplit : ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j / W * l t j
        + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
            swWeight l a eta t j / W * swMixLoss l a eta t := by
    calc ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
        = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
              ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
          + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
              ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j => a t j = true)
          (fun j => ewNorm (swLoss l a eta) eta t j
            * swLoss l a eta t j)).symm
      _ = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
              swWeight l a eta t j / W * l t j
          + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
              swWeight l a eta t j / W * swMixLoss l a eta t := by
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by
            rcases Finset.mem_filter.mp hj with ⟨_, hjj⟩
            rw [hnorm j]; simp [swLoss, hjj]
        · exact Finset.sum_congr rfl fun j hj => by
            rcases Finset.mem_filter.mp hj with ⟨_, hjj⟩
            rw [hnorm j]; simp [swLoss, hjj]
  rw [hsplit]
  have hA1 : ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
      swWeight l a eta t j / W * l t j = P * swMixLoss l a eta t / W := by
    have heq : ∀ j ∈ Finset.univ.filter (fun j => a t j = true),
        swWeight l a eta t j / W * l t j
          = swWeight l a eta t j * l t j / W :=
      fun j _ => div_mul_eq_mul_div _ _ _
    rw [Finset.sum_congr rfl (fun j hj => heq j hj), ← Finset.sum_div,
      ← hPM]
  have hA2 : ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
      swWeight l a eta t j / W * swMixLoss l a eta t
      = (W - P) * swMixLoss l a eta t / W := by
    have heq : ∀ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
        swWeight l a eta t j / W * swMixLoss l a eta t
          = swWeight l a eta t j * swMixLoss l a eta t / W :=
      fun j _ => div_mul_eq_mul_div _ _ _
    rw [Finset.sum_congr rfl (fun j hj => heq j hj), ← Finset.sum_div,
      ← Finset.sum_mul, ← hS]
  have hWne : W ≠ 0 := ne_of_gt hWpos
  rw [hA1, hA2]
  field_simp
  ring

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ НОСИТЕЛЯ — sleeping-experts regret (маски
рованная версия `hsurv_derived` + `router_regret_bound`): смесь
конкурирует с экспертом i НА ЕГО СОБСТВЕННЫХ AWAKE-РАУНДАХ с
константой носителя log K/η + η·T/2. Асимные члены сокращаются
ТОЧНО (равенство), без отбрасывания. -/
theorem sleeping_hedge_regret (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool)
    (eta : ℝ) (T : ℕ) (i : ι)
    (hl : ∀ t < T, ∀ j, 0 ≤ l t j ∧ l t j ≤ 1)
    (haw : ∀ t < T, ∃ j, a t j = true)
    (heta : 0 < eta ∧ eta ≤ 1) :
    ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
        (swMixLoss l a eta t - l t i)
      ≤ Real.log (Fintype.card ι) / eta + eta * T / 2 := by
  have hmem : ∀ t < T, ∀ j, 0 ≤ swLoss l a eta t j
      ∧ swLoss l a eta t j ≤ 1 := by
    intro t ht j
    by_cases hA : a t j = true
    · rw [swLoss, if_pos hA]; exact hl t ht j
    · rw [swLoss, if_neg hA]
      exact mixLossOf_mem _ _ _ (haw t ht) (swWeight_pos l a eta t)
        (fun j' => hl t ht j')
  have hsurv := hsurv_derived (swLoss l a eta) eta T i hmem
    ⟨heta.1.le, heta.2⟩
  have hAeq : ∑ t ∈ Finset.range T,
      ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = ∑ t ∈ Finset.range T, swMixLoss l a eta t :=
    Finset.sum_congr rfl fun t ht =>
      algLoss_eq_mixLoss l a eta t (haw t (Finset.mem_range.mp ht))
  rw [hAeq] at hsurv
  have hrrb := router_regret_bound (Fintype.card ι) T eta
    (∑ t ∈ Finset.range T, swMixLoss l a eta t)
    (∑ t ∈ Finset.range T, swLoss l a eta t i)
    (Fintype.card_pos) heta.1 hsurv
  have hsplitL : ∑ t ∈ Finset.range T, swLoss l a eta t i
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          l t i
        + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true)) (Finset.range T),
            swMixLoss l a eta t := by
    calc ∑ t ∈ Finset.range T, swLoss l a eta t i
        = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
              swLoss l a eta t i
          + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
                (Finset.range T), swLoss l a eta t i :=
        (Finset.sum_filter_add_sum_filter_not (Finset.range T)
          (fun t => a t i = true) (fun t => swLoss l a eta t i)).symm
      _ = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
              l t i
          + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
                (Finset.range T), swMixLoss l a eta t := by
        congr 1
        · exact Finset.sum_congr rfl fun t ht => by
            rcases Finset.mem_filter.mp ht with ⟨_, htt⟩
            simp [swLoss, htt]
        · exact Finset.sum_congr rfl fun t ht => by
            rcases Finset.mem_filter.mp ht with ⟨_, htt⟩
            simp [swLoss, htt]
  have hsplitM : ∑ t ∈ Finset.range T, swMixLoss l a eta t
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          swMixLoss l a eta t
        + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
              (Finset.range T), swMixLoss l a eta t :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range T)
      (fun t => a t i = true) (fun t => swMixLoss l a eta t)).symm
  rw [hsplitL, hsplitM] at hrrb
  rw [Finset.sum_sub_distrib]
  linarith

end Carrier

section Router

variable {k : Type*} [Fintype k] [Nonempty k]

/-- `swPredW` — предсказательные веса роутера: awake-нормировка,
спящим экспертам ноль (guard исключает их из предсказания;
вероятностный вектор поддержан на awake-множестве). -/
noncomputable def swPredW {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  if a t i = true then
    swWeight l a eta t i / awPot (swWeight l a eta t) (a t) else 0

theorem swPredW_nonneg {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (haw : ∃ j, a t j = true) (i : Fin N) :
    0 ≤ swPredW l a eta t i := by
  haveI : Nonempty (Fin N) := ⟨i⟩
  unfold swPredW
  by_cases hA : a t i = true
  · rw [if_pos hA]
    exact div_nonneg (swWeight_pos l a eta t i).le
      (awPot_pos _ _ haw (swWeight_pos l a eta t)).le
  · rw [if_neg hA]

/-- Скалярное произведение предсказательных весов на любой вектор —
это awake-нормированная смесь по awake-множеству (спящие дают 0). -/
theorem swPredW_mul_sum {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (lt : Fin N → ℝ) (haw : ∃ j, a t j = true) :
    ∑ i, swPredW l a eta t i * lt i
      = mixLossOf (swWeight l a eta t) lt (a t) := by
  unfold swPredW mixLossOf
  calc ∑ i, (if a t i = true then
          swWeight l a eta t i / awPot (swWeight l a eta t) (a t) else 0)
          * lt i
      = ∑ i ∈ Finset.univ.filter (fun i => a t i = true),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i
          + ∑ i ∈ Finset.univ.filter (fun i => ¬(a t i = true)),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i => a t i = true)
          (fun i => (if a t i = true then
            swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i)).symm
    _ = ∑ i ∈ Finset.univ.filter (fun i => a t i = true),
            swWeight l a eta t i
              / awPot (swWeight l a eta t) (a t) * lt i := by
        have hz : ∀ i ∈ Finset.univ.filter (fun i => ¬(a t i = true)),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i = 0 := by
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨_, hii⟩
          simp [hii]
        rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, add_zero]
        exact Finset.sum_congr rfl fun i hi => by
          rcases Finset.mem_filter.mp hi with ⟨_, hii⟩
          simp [hii]

theorem swPredW_sum {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (haw : ∃ j, a t j = true) :
    ∑ i, swPredW l a eta t i = 1 := by
  haveI : Nonempty (Fin N) := let ⟨j, _⟩ := haw; ⟨j⟩
  have h1 : ∑ i, swPredW l a eta t i
      = ∑ i, swPredW l a eta t i * 1 := by
    simp [mul_one]
  rw [h1, swPredW_mul_sum l a eta t (fun _ => 1) haw]
  unfold mixLossOf
  have hns := awNorm_sum (swWeight l a eta t) (a t) haw
    (swWeight_pos l a eta t)
  simpa only [mul_one] using hns

/-- `swPredW_ce` — по-раундовая калибровка (C319): CE смеси логитов
не хуже взвешенного среднего CE экспертов; на awake-supported
весах взвешенная сумма CE РАВНА потере смеси `swMixLoss`
(`swPredW_mul_sum`). -/
theorem swPredW_ce {N : ℕ} (t : k)
    (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool) (eta : ℝ) (t' : ℕ)
    (haw : ∃ j, a t' j = true)
    (z : Fin N → k → ℝ) (hz : ∀ i, ceOneHot t (z i) = l t' i) :
    ceOneHot t (fun v => ∑ i : Fin N, swPredW l a eta t' i * z i v)
      ≤ swMixLoss l a eta t' := by
  haveI : Nonempty (Fin N) := let ⟨j, _⟩ := haw; ⟨j⟩
  refine le_trans (soft_router_ce_bound t (swPredW l a eta t')
    (fun i => swPredW_nonneg l a eta t' haw i)
    (swPredW_sum l a eta t' haw) z) ?_
  have h2 : ∑ i, swPredW l a eta t' i * ceOneHot t (z i)
      = mixLossOf (swWeight l a eta t') (l t') (a t') := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hz i]),
      swPredW_mul_sum l a eta t' (l t') haw]
  rw [h2]
  exact le_rfl

end Router

section Total

variable {k : Type*} [Fintype k] [Nonempty k]

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ КОМПОЗИЦИИ — апгрейд C320
(`soft_router_total_bound` со спящими экспертами). За T раундов с
guard-маской a (каждый раунд хоть один эксперт доступен, CE ≤ 1 —
exact-expert abstention как в C320) суммарный CE мягкой awake-смеси
НА ДОСТУПНЫХ РАУНДАХ ЭКСПЕРТА i не превосходит суммарный CE
эксперта i на тех же раундах плюс константа носителя
log N/η + η·T/2. Композиция: по-раундовая калибровка C319
(`swPredW_ce`) + `sleeping_hedge_regret`; новые факты — только
суммирование-склейка. Honest scope: oblivious-последовательности
(без drift/адаптивности — скоуп носителя); regret против
ФИКСИРОВАННОГО эксперта на его awake-раундах (best-switching не
заявлен); CE смеси на раундах, где i спит, НЕ ограничивается (там
роутер конкурирует с другими доступными экспертами). -/
theorem sleeping_router_total_bound {N : ℕ} [Nonempty (Fin N)]
    (eta : ℝ) (heta : 0 < eta ∧ eta ≤ 1) (T : ℕ)
    (lab : ℕ → k) (z : ℕ → Fin N → k → ℝ) (a : ℕ → Fin N → Bool)
    (hce : ∀ t ∈ Finset.range T, ∀ i, ceOneHot (lab t) (z t i) ≤ 1)
    (haw : ∀ t ∈ Finset.range T, ∃ j, a t j = true)
    (i : Fin N) :
    ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
        ceOneHot (lab t)
          (fun v => ∑ j : Fin N, swPredW
            (fun t j => ceOneHot (lab t) (z t j)) a eta t j * z t j v)
      ≤ ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          ceOneHot (lab t) (z t i)
        + Real.log (Fintype.card (Fin N)) / eta + eta * T / 2 := by
  set l : ℕ → Fin N → ℝ := fun t j => ceOneHot (lab t) (z t j) with hll
  have hl : ∀ t < T, ∀ j, 0 ≤ l t j ∧ l t j ≤ 1 := by
    intro t ht j
    exact ⟨Hagi.Learning.SoftRouterTotal.ceOneHot_nonneg (lab t) (z t j),
      hce t (Finset.mem_range.mpr ht) j⟩
  have hround : ∀ t ∈ Finset.range T,
      ceOneHot (lab t) (fun v => ∑ j : Fin N, swPredW l a eta t j
        * z t j v) ≤ swMixLoss l a eta t := fun t ht =>
    swPredW_ce (lab t) l a eta t (haw t ht) (z t) (fun j => rfl)
  have hA : ∑ t ∈ Finset.filter (fun t => a t i = true)
      (Finset.range T),
      ceOneHot (lab t)
        (fun v => ∑ j : Fin N, swPredW l a eta t j * z t j v)
      ≤ ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          swMixLoss l a eta t :=
    Finset.sum_le_sum fun t ht => hround t (Finset.mem_filter.mp ht).1
  have hreg := sleeping_hedge_regret l a eta T i
    (fun t ht j => hl t ht j)
    (fun t ht => haw t (Finset.mem_range.mpr ht)) heta
  rw [Finset.sum_sub_distrib] at hreg
  have hfil : ∑ t ∈ Finset.filter (fun t => a t i = true)
      (Finset.range T), l t i
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          ceOneHot (lab t) (z t i) := by rw [hll]
  rw [hfil] at hreg
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp [Fintype.card_fin]
  rw [hcard] at hreg
  rw [hcard]
  linarith

end Total

section Anchor

/-- `sleep_anchor_mask` — маска чередования: эксперт i доступен в
раунде t ⟺ (t + i) % 2 = 0 (в каждом раунде доступен ровно один
эксперт; в чётных раундах — эксперт 0, в нечётных — эксперт 1). -/
def sleep_anchor_mask (t : ℕ) (i : Fin 2) : Bool :=
  decide ((t + i.val) % 2 = 0)

theorem sleep_anchor_mask_even (t : ℕ) (ht : t % 2 = 0) :
    sleep_anchor_mask t 0 = true ∧ sleep_anchor_mask t 1 = false := by
  constructor
  · simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
      decide_eq_true_eq]
    omega
  · simp only [sleep_anchor_mask, Fin.isValue, decide_eq_false_iff_not]
    omega

theorem sleep_anchor_mask_odd (t : ℕ) (ht : t % 2 = 1) :
    sleep_anchor_mask t 0 = false ∧ sleep_anchor_mask t 1 = true := by
  constructor
  · simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
      decide_eq_false_iff_not]
    omega
  · simp only [sleep_anchor_mask, Fin.isValue, decide_eq_true_eq]
    omega

theorem sleep_anchor_awake (t : ℕ) : ∃ j : Fin 2, sleep_anchor_mask t j
    = true := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · exact ⟨0, (sleep_anchor_mask_even t h).1⟩
  · exact ⟨1, (sleep_anchor_mask_odd t h).2⟩

/-- `mixLossOf_singleton` — смесь по одноэлементному awake-множеству
вырождается в единственного доступного эксперта (m_t = ℓ_j0; веса
и η не играют роли). -/
theorem mixLossOf_singleton {ι : Type} [Fintype ι] (w lt : ι → ℝ)
    (A : ι → Bool) (j : ι) (hw : w j ≠ 0)
    (hA : ∀ x, A x = true ↔ x = j) : mixLossOf w lt A = lt j := by
  have hfil : Finset.univ.filter (fun x => A x = true) = {j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hA x
  unfold mixLossOf awPot
  rw [hfil, Finset.sum_singleton, Finset.sum_singleton, div_self hw,
    one_mul]

/-- Якорные потери: CE экспертов C320 (`az`): эксперт 0 = wz1
(CE = L = log(1+e⁻²)), эксперт 1 = константа 1 (CE = log 2). -/
noncomputable def sleep_anchor_loss : ℕ → Fin 2 → ℝ :=
  fun t j => ceOneHot 0 (Hagi.Learning.SoftRouterTotal.az t j)

theorem sleep_anchor_loss_eq (t : ℕ) (j : Fin 2) :
    sleep_anchor_loss t j
      = if j = 0 then Real.log (1 + Real.exp (-(2:ℝ)))
        else Real.log 2 := by
  unfold sleep_anchor_loss
  rw [Hagi.Learning.SoftRouterTotal.az_ce]

/-- Смесь якоря: singleton awake ⇒ m_t = CE единственного
доступного эксперта. -/
theorem sleep_anchor_mix_eq (t : ℕ) :
    swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      = if t % 2 = 0 then sleep_anchor_loss t 0
        else sleep_anchor_loss t 1 := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [if_pos h]
    refine mixLossOf_singleton _ _ _ 0
      (ne_of_gt (swWeight_pos sleep_anchor_loss sleep_anchor_mask
        (1 / 2) t 0)) ?_
    intro x
    constructor
    · intro hx
      fin_cases x
      · rfl
      · exact absurd hx
          (Bool.eq_false_iff.mp (sleep_anchor_mask_even t h).2)
    · intro hx
      subst hx
      exact (sleep_anchor_mask_even t h).1
  · rw [if_neg (show ¬t % 2 = 0 by omega)]
    refine mixLossOf_singleton _ _ _ 1
      (ne_of_gt (swWeight_pos sleep_anchor_loss sleep_anchor_mask
        (1 / 2) t 1)) ?_
    intro x
    constructor
    · intro hx
      fin_cases x
      · exact absurd hx
          (Bool.eq_false_iff.mp (sleep_anchor_mask_odd t h).1)
      · rfl
    · intro hx
      subst hx
      exact (sleep_anchor_mask_odd t h).2

/-- ЧИСЛОВАЯ ПРОВЕРКА (2 эксперта, чередующаяся доступность,
4 раунда, η = 1/2): (а) НЕВАКУУНСТВО — смесь строго положительна
(каждый m_t = CE доступного эксперта > 0); (б) ТОЧНОЕ ЗНАЧЕНИЕ —
total = 2·L + 2·log 2 (чётные раунды — эксперт 0, нечётные — 1);
(в) REGRET-ПРОВЕРКА — инстанциация `sleeping_hedge_regret` для
i = 0: LHS = 0 (на чётных раундах смесь вырождена в эксперта 0) ≤
константа 2·log 2 + 1. Все три — через ГЛАВНЫЕ определения/теоремы,
не самостоятельные леммы. -/
theorem sleeping_router_anchor :
    (0:ℝ) < ∑ t ∈ Finset.range 4,
        swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      ∧ ∑ t ∈ Finset.range 4,
          swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
        = 2 * Real.log (1 + Real.exp (-(2:ℝ))) + 2 * Real.log 2
      ∧ ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0 = true)
            (Finset.range 4),
          (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
            - sleep_anchor_loss t 0)
        ≤ 2 * Real.log 2 + 1 := by
  -- значение каждого слагаемого по чётности
  have hterm : ∀ t ∈ Finset.range 4,
      swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
        = if t % 2 = 0 then Real.log (1 + Real.exp (-(2:ℝ)))
          else Real.log 2 := by
    intro t _
    by_cases h : t % 2 = 0
    · rw [sleep_anchor_mix_eq, if_pos h, sleep_anchor_loss_eq, if_pos rfl,
        if_pos h]
    · rw [sleep_anchor_mix_eq, if_neg h, sleep_anchor_loss_eq,
        if_neg (by decide : ¬((1 : Fin 2) = 0)), if_neg h]
  -- развёртка 4 слагаемых
  have hsum : ∑ t ∈ Finset.range 4,
      swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      = 2 * Real.log (1 + Real.exp (-(2:ℝ))) + 2 * Real.log 2 := by
    have e0 : (0 : ℕ) % 2 = 0 := by norm_num
    have e1 : ¬((1 : ℕ) % 2 = 0) := by norm_num
    have e2 : (2 : ℕ) % 2 = 0 := by norm_num
    have e3 : ¬((3 : ℕ) % 2 = 0) := by norm_num
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hterm 0 (by norm_num), hterm 1 (by norm_num),
      hterm 2 (by norm_num), hterm 3 (by norm_num)]
    simp only [Finset.sum_empty, zero_add]
    norm_num
    ring
  refine ⟨?_, hsum, ?_⟩
  · have hL : (0:ℝ) < Real.log (1 + Real.exp (-(2:ℝ))) := by
      have h1 : (1:ℝ) < 1 + Real.exp (-(2:ℝ)) := by
        linarith [Real.exp_pos (-(2:ℝ))]
      exact Real.log_pos (by linarith)
    have h2 : (0:ℝ) < Real.log 2 :=
      Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [hsum]
    linarith
  · have hreg := sleeping_hedge_regret sleep_anchor_loss
      sleep_anchor_mask (1 / 2) 4 0
      (fun t ht j => ⟨
        Hagi.Learning.SoftRouterTotal.ceOneHot_nonneg 0
          (Hagi.Learning.SoftRouterTotal.az t j),
        Hagi.Learning.SoftRouterTotal.az_ce_le_one t j⟩)
      (fun t _ => sleep_anchor_awake t) ⟨by norm_num, by norm_num⟩
    have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
    rw [hcard] at hreg
    -- LHS = 0: на каждом чётном t смесь = l t 0
    have hzero : ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0
        = true) (Finset.range 4),
        (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
          - sleep_anchor_loss t 0) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rcases Finset.mem_filter.mp ht with ⟨_, hmask⟩
      simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
        decide_eq_true_eq] at hmask
      have he : t % 2 = 0 := by omega
      rw [sleep_anchor_mix_eq, if_pos he]
      ring
    -- LHS = 0: на каждом чётном t смесь вырождена в эксперта 0
    have hzero : ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0
        = true) (Finset.range 4),
        (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
          - sleep_anchor_loss t 0) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rcases Finset.mem_filter.mp ht with ⟨_, hmask⟩
      simp only [sleep_anchor_mask, Fin.isValue, decide_eq_true_eq] at hmask
      have he : t % 2 = 0 := by omega
      rw [sleep_anchor_mix_eq, if_pos he]
      ring
    rw [hzero] at hreg
    have hsplit : Real.log 2 / (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((4:ℕ):ℝ) / 2
        = 2 * Real.log 2 + 1 := by push_cast; field_simp; ring
    rw [hsplit] at hreg
    linarith

end Anchor

end Hagi.Learning.SleepingRouter
