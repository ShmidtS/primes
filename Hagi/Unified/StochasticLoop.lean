/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Probability.Freedman
import Hagi.Unified.CertifiedLoop

/-!
# StochasticLoop — стохастический certified loop через ядерный адаптер

Цепь
стохастических шагов (`CertStochasticStep`: drop / failure /
descent_whp) погружается в ядерный капстон
(`certified_loop_kernel` над `CertStepGenBounded`), так что
стохастический тренировочный цикл получает ту же
certified-loop гарантию, что и детерминированные, с whp-бюджетом
отказов, сделанным явным на уровне цикла.

**Что доказано:**

* `stochDBudget` — остаток δ-бюджета `∑ i ∈ Ico k n, deltas i`;
  `stochDBudget_split` — расщепление «текущий + остаток»;
* `stochMetrics` — ядерные носители стохастического цикла:
  objective/budget/task из M (по второй компоненте состояния
  `ℕ × S`), risk = остаток δ-бюджета;
* `pmfMean_indicator_compl` / `pmfMean_bad_le_failure` —
  вероятностный инструментарий (комплемент-индикатор; из
  `descent_whp` шага следует P(bad-события) ≤ failure);
* `certStochasticStep_to_bounded` — АДАПТЕР: CertStochasticStep
  шага плюс good-событие (drop ≤ realized при данном ω) дают
  bounded-шаг ядра; riskSpend = δ_j, а riskRem (в exact-виде
  `CertStepGenBounded.toExact`) = остаток δ-бюджета —
  δ-бюджет канализируется ровно в riskRem-семантику ядра;
* `stochastic_loop_certified` — ГЛАВНАЯ: T-шаговый цикл
  стохастических шагов несёт (1) union bound: вероятность того,
  что ВСЕ шаги реализуют свой drop, ≥ 1 − ∑δ_j (total failure ≤
  Σδ_t); (2) на good-событии пер-шаговые drop'ы телескопируют
  (∑ drops ≤ obj₀ − obj_T) — ДОКАЗАНО ЧЕРЕЗ `certified_loop_kernel`
  (переиспользование, не новая индукция);
* `stochastic_loop_descent_whp` — следствие: суммарный
  сертифицированный спуск выполняется с вероятностью ≥ 1 − ∑δ_j.

**Честные ограничения (что остаётся premise-form):**

* условия шума (bounded / zero-mean / cond-variance) остаются
  биндерами стохастического моста — цикл потребляет ГОТОВЫЕ
  `CertStochasticStep`, на свой уровень их не поднимает;
* бюджетные и floor-законы держатся ω-РАВНОМЕРНО (посылки hbnb /
  hflr): δ-бюджет учитывает только descent-отказы шагов; отказы
  бюджета/качества в budgeted-форме — отдельная задача;
* δ_j ≥ 0 — явная посылка (без неё risk_nonneg не выводим);
* delta-канал ядра не используется (тривиальный нулевой уровень).

Посылки все явные, эмпирических констант (`h_emp_`) нет.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Unified.StochasticLoop

open Hagi.Probability Hagi.Cert Hagi.Unified.CertifiedLoopKernel
open scoped BigOperators Classical

variable {Ω S TaskId : Type*} [Fintype Ω]

/-! ## Остаток δ-бюджета -/

/-- Остаток δ-бюджета после k шагов: сумма δ_j по j ∈ [k, n). -/
def stochDBudget (deltas : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico k n, deltas i

/-- Расщепление остатка: при j < n остаток после j равен
δ_j + остаток после j+1 (трата шага j — ровно δ_j). -/
theorem stochDBudget_split (deltas : ℕ → ℝ) (n j : ℕ) (hj : j < n) :
    deltas j + stochDBudget deltas n (j + 1) = stochDBudget deltas n j := by
  have hmem : j ∉ Finset.Ico (j + 1) n := by simp
  have hunion : Finset.Ico j n = insert j (Finset.Ico (j + 1) n) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [stochDBudget, stochDBudget, hunion, Finset.sum_insert hmem]

/-- Ядерные носители стохастического цикла: состояние `ℕ × S`
(время, состояние цикла); objective/budget/task читаются из M по
состоянию; risk — остаток δ-бюджета по времени (δ-бюджет
канализируется в risk-канал ядра: в exact-виде `toExact` riskRem =
остаток δ-бюджета после шага). -/
def stochMetrics (M : SystemMetrics S TaskId) (deltas : ℕ → ℝ)
    (n : ℕ) : SystemMetrics (ℕ × S) TaskId where
  objective p := M.objective p.2
  risk p := stochDBudget deltas n p.1
  budget p := M.budget p.2
  task p := M.task p.2

/-! ## Вероятностный инструментарий -/

/-- Комплемент-индикатор: среднее индикатора события плюс
среднее индикатора дополнения равно 1. -/
theorem pmfMean_indicator_compl (p : PMF Ω) (Q : Ω → Prop) :
    pmfMean p (fun ω => if Q ω then (1 : ℝ) else 0)
      + pmfMean p (fun ω => if Q ω then 0 else 1) = 1 := by
  have h := pmfMean_add p (fun ω => if Q ω then (1 : ℝ) else 0)
    (fun ω => if Q ω then (0 : ℝ) else 1)
  have hc : pmfMean p (fun a => (if Q a then (1 : ℝ) else 0)
      + (if Q a then (0 : ℝ) else 1))
      = pmfMean p (fun _ => (1 : ℝ)) :=
    pmfMean_congr p (fun a _ => by by_cases hQ : Q a <;> simp [hQ])
  rw [← h, hc, pmfMean_const p 1]

/-- Из whp-закона шага (`descent_whp`): вероятность bad-события
{drop не достигнут} не превосходит failure. -/
theorem pmfMean_bad_le_failure (p : PMF Ω) (realized : Ω → ℝ)
    (cert : CertStochasticStep p realized) :
    pmfMean p (fun ω => if cert.drop ≤ realized ω then (0 : ℝ) else 1)
      ≤ cert.failure := by
  have hw := cert.descent_whp
  have hpair := pmfMean_indicator_compl p
    (fun ω => cert.drop ≤ realized ω)
  have hc : pmfMean p (fun ω => if cert.drop ≤ realized ω then (0 : ℝ) else 1)
      = 1 - pmfMean p (fun ω => if cert.drop ≤ realized ω then (1 : ℝ) else 0) := by
    linarith
  rw [hc]
  linarith

/-! ## Адаптер CertStochasticStep → CertStepGenBounded -/

/-- АДАПТЕР: стохастический сертификат шага плюс good-событие
(certified drop ≤ реализованный декремент objective при данном
ω) дают bounded-шаг ядра на носителях `stochMetrics`.
riskSpend = δ_j; в exact-виде (`CertStepGenBounded.toExact`)
riskRem = остаток δ-бюджета после шага. Бюджетная трата —
дефинициональная разность бюджетов; floors — из равномерной
посылки. -/
def certStochasticStep_to_bounded (law : PMF Ω)
    (M : SystemMetrics S TaskId)
    (obl : StepObligations TaskId) (deltas : ℕ → ℝ) (n : ℕ)
    (hnn : ∀ i, 0 ≤ deltas i)
    (f : ℕ → Ω → S)
    (hbnb : ∀ k ω, 0 ≤ M.budget (f k ω))
    (hflr : ∀ k ω, FloorsKept M obl (f k ω))
    {j : ℕ} (hj : j < n)
    (cert : CertStochasticStep law
      (fun ω => M.objective (f j ω) - M.objective (f (j + 1) ω)))
    (ω : Ω)
    (hgood : cert.drop ≤ M.objective (f j ω) - M.objective (f (j + 1) ω)) :
    CertStepGenBounded (stochMetrics M deltas n) obl (fun _ => (0 : ℝ))
      (j, f j ω) (j + 1, f (j + 1) ω) where
  drop := cert.drop
  drop_pos := cert.drop_pos
  descent := by
    show M.objective (f (j + 1) ω) ≤ M.objective (f j ω) - cert.drop
    linarith
  budgetSpend := M.budget (f j ω) - M.budget (f (j + 1) ω)
  budget_next_le := by
    show M.budget (f (j + 1) ω) ≤ M.budget (f j ω)
      - (M.budget (f j ω) - M.budget (f (j + 1) ω))
    rw [sub_sub_cancel]
  budget_nonneg := hbnb _ ω
  riskSpend := deltas j
  risk_next_le := by
    show stochDBudget deltas n (j + 1)
      ≤ stochDBudget deltas n j - deltas j
    rw [← stochDBudget_split deltas n j hj]
    linarith
  risk_nonneg := by
    show 0 ≤ stochDBudget deltas n (j + 1)
    exact Finset.sum_nonneg fun i _ => hnn i
  delta := 0
  delta_next_le := by simp
  delta_nonneg := le_refl _
  floorsKept := fun t => hflr (j + 1) ω t

/-! ## Стохастический certified loop -/

/-- Drop'ы цепи стохастических сертификатов как функции ℕ → ℝ
(вне горизонта — ноль). -/
def chainDrops (M : SystemMetrics S TaskId) (f : ℕ → Ω → S)
    {n : ℕ} {law : PMF Ω}
    (certs : ∀ j : Fin n, CertStochasticStep law
      (fun ω => M.objective (f j.val ω) - M.objective (f (j.val + 1) ω))) :
    ℕ → ℝ :=
  fun k => if h : k < n then (certs ⟨k, h⟩).drop else 0

/-- Good-событие цикла: при данном ω каждый шаг реализует свой
сертифицированный drop. -/
def stochChainGood (M : SystemMetrics S TaskId) (f : ℕ → Ω → S)
    (n : ℕ) (drops : ℕ → ℝ) : Ω → Prop :=
  fun ω => ∀ k, (h : k < n) →
    drops k ≤ M.objective (f k ω) - M.objective (f (k + 1) ω)

/-- ГЛАВНАЯ ТЕОРЕМА: T-шаговый цикл стохастических шагов.

(1) UNION: вероятность good-события (все шаги реализуют свои
drop'ы) ≥ 1 − ∑ δ_j: суммарная вероятность отказа ≤ Σδ_t
(union bound по bad-событиям шагов, per-step descent_whp);

(2) TELESCOPE: на good-событии пер-шаговые drop'ы телескопируют
(∑ drops ≤ obj₀ − obj_T), floors держатся, бюджет неотрицателен —
заключения выведены ЧЕРЕЗ `certified_loop_kernel` (ядерный
капстон переиспользование).

Посылки: `certs` — CertStochasticStep-сертификаты шагов;
`hnn` — δ_j ≥ 0; `hfail` — failure_j ≤ δ_j; `hbnb`/`hflr` —
ω-равномерные бюджет/floor законы (δ-бюджет покрывает только
descent-отказы). -/
theorem stochastic_loop_certified (law : PMF Ω)
    (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)
    (n : ℕ) (f : ℕ → Ω → S)
    (certs : ∀ j : Fin n, CertStochasticStep law
      (fun ω => M.objective (f j.val ω) - M.objective (f (j.val + 1) ω)))
    (deltas : ℕ → ℝ) (hnn : ∀ i, 0 ≤ deltas i)
    (hfail : ∀ j : Fin n, (certs j).failure ≤ deltas j.val)
    (hbnb : ∀ k ω, 0 ≤ M.budget (f k ω))
    (hflr : ∀ k ω, FloorsKept M obl (f k ω)) :
    pmfMean law (fun ω =>
        if stochChainGood M f n (chainDrops M f certs) ω then (1 : ℝ) else 0)
      ≥ 1 - ∑ j ∈ Finset.range n, deltas j
      ∧ ∀ ω, stochChainGood M f n (chainDrops M f certs) ω →
        (∑ j ∈ Finset.range n, chainDrops M f certs j
          ≤ M.objective (f 0 ω) - M.objective (f n ω)
          ∧ FloorsKept M obl (f n ω)
          ∧ 0 ≤ M.budget (f n ω)) := by
  classical
  set drops : ℕ → ℝ := chainDrops M f certs with hdropsdef
  -- (1) union bound: per-step bad-вероятность ≤ δ_j
  have hbadle : ∀ j ∈ Finset.range n,
      pmfMean law (fun ω =>
        if ¬ (drops j ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
          then (1 : ℝ) else 0)
        ≤ deltas j := by
    intro j hj
    have hlt : j < n := Finset.mem_range.mp hj
    have hb := pmfMean_bad_le_failure law
      (fun ω => M.objective (f j ω) - M.objective (f (j + 1) ω))
      (certs ⟨j, hlt⟩)
    have hbd : drops j = (certs ⟨j, hlt⟩).drop := dite_eq_left hlt
    have hconv : pmfMean law (fun ω =>
        if ¬ (drops j ≤ M.objective (f j ω)
            - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0)
        = pmfMean law (fun ω =>
          if (certs ⟨j, hlt⟩).drop
            ≤ M.objective (f j ω) - M.objective (f (j + 1) ω)
            then (0 : ℝ) else 1) :=
      pmfMean_congr law (fun ω _ => by
        by_cases h : (certs ⟨j, hlt⟩).drop
          ≤ M.objective (f j ω) - M.objective (f (j + 1) ω) <;>
          simp [h, hbd])
    rw [hconv]
    exact le_trans hb (hfail ⟨j, hlt⟩)
  have hsumle : ∑ j ∈ Finset.range n, pmfMean law (fun ω =>
      if ¬ (drops j ≤ M.objective (f j ω)
        - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.range n, deltas j :=
    Finset.sum_le_sum hbadle
  -- good-индикатор + bad∃-индикатор = 1 (поточечный комплемент)
  have hone : pmfMean law (fun ω =>
      (if stochChainGood M f n drops ω then (1 : ℝ) else 0)
        + (if ∃ j ∈ Finset.range n, ¬ (drops j
            ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
            then (1 : ℝ) else 0)) = 1 := by
    refine Eq.trans (pmfMean_congr law ?_) (pmfMean_const law 1)
    intro ω _
    by_cases hg : stochChainGood M f n drops ω
    · have hnb : ¬ ∃ j ∈ Finset.range n, ¬ (drops j
          ≤ M.objective (f j ω) - M.objective (f (j + 1) ω)) := by
        rintro ⟨j, hj, hjn⟩
        exact hjn (hg j (Finset.mem_range.mp hj))
      rw [ite_eq_left hg, ite_eq_right hnb]
      norm_num
    · have hnb : ∃ j ∈ Finset.range n, ¬ (drops j
          ≤ M.objective (f j ω) - M.objective (f (j + 1) ω)) := by
        by_contra hc
        apply hg
        intro k hk
        by_contra hQ
        exact hc ⟨k, Finset.mem_range.mpr hk, hQ⟩
      rw [ite_eq_right hg, ite_eq_left hnb]
      norm_num
  have hpair : pmfMean law (fun ω =>
      if stochChainGood M f n drops ω then (1 : ℝ) else 0)
      + pmfMean law (fun ω =>
          if ∃ j ∈ Finset.range n, ¬ (drops j
            ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
            then (1 : ℝ) else 0) = 1 := by
    rw [← pmfMean_add law
      (fun ω => if stochChainGood M f n drops ω then (1 : ℝ) else 0)
      (fun ω => if ∃ j ∈ Finset.range n, ¬ (drops j
        ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
        then (1 : ℝ) else 0)]
    exact hone
  -- ∃-bad-индикатор ≤ Σ per-step bad-индикаторов (поточечный union)
  have hpt : ∀ ω,
      (if ∃ j ∈ Finset.range n, ¬ (drops j
          ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
          then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.range n,
          (if ¬ (drops j ≤ M.objective (f j ω)
            - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0) := by
    intro ω
    by_cases hE : ∃ j ∈ Finset.range n, ¬ (drops j
        ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
    · simp only [hE, ite_true]
      obtain ⟨j, hj, hjn⟩ := hE
      have hsingle :
          (if ¬ (drops j ≤ M.objective (f j ω)
            - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0)
          ≤ ∑ k ∈ Finset.range n,
              (if ¬ (drops k ≤ M.objective (f k ω)
                - M.objective (f (k + 1) ω)) then (1 : ℝ) else 0) :=
        Finset.single_le_sum
          (f := fun k => (if ¬ (drops k ≤ M.objective (f k ω)
            - M.objective (f (k + 1) ω)) then (1 : ℝ) else 0))
          (fun k _ => by
            by_cases hh : ¬ (drops k ≤ M.objective (f k ω)
              - M.objective (f (k + 1) ω)) <;> simp [hh]) hj
      calc (1 : ℝ)
          = (if ¬ (drops j ≤ M.objective (f j ω)
              - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0) := by
            simp [hjn]
        _ ≤ _ := hsingle
    · simp only [hE, ite_false]
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hh : ¬ (drops j ≤ M.objective (f j ω)
          - M.objective (f (j + 1) ω)) <;> simp [hh]
  have hbadsum : pmfMean law (fun ω =>
      if ∃ j ∈ Finset.range n, ¬ (drops j
        ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
        then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.range n, deltas j := by
    refine le_trans (pmfMean_mono law (fun ω _ => hpt ω)) ?_
    rw [pmfMean_finset_sum law (Finset.range n)
      (fun j ω => if ¬ (drops j ≤ M.objective (f j ω)
        - M.objective (f (j + 1) ω)) then (1 : ℝ) else 0)]
    exact hsumle
  refine ⟨?_, ?_⟩
  · -- union-арифметика
    have hA : pmfMean law (fun ω =>
        if stochChainGood M f n drops ω then (1 : ℝ) else 0)
        = 1 - pmfMean law (fun ω =>
            if ∃ j ∈ Finset.range n, ¬ (drops j
              ≤ M.objective (f j ω) - M.objective (f (j + 1) ω))
              then (1 : ℝ) else 0) := by linarith
    linarith
  · -- (2) телескоп на good-событии ЧЕРЕЗ certified_loop_kernel
    intro ω hg
    have hgoodj : ∀ j : Fin n, (certs j).drop
        ≤ M.objective (f (j : ℕ) ω)
          - M.objective (f ((j : ℕ) + 1) ω) := by
      intro j
      have h := hg j.val j.isLt
      have hd : drops j.val = (certs ⟨j.val, j.isLt⟩).drop :=
        dite_eq_left j.isLt
      rw [hd] at h
      exact h
    have hf0 : FloorsKept (stochMetrics M deltas n) obl (0, f 0 ω) :=
      fun t => hflr 0 ω t
    have hb0 : 0 ≤ (stochMetrics M deltas n).budget (0, f 0 ω) :=
      hbnb 0 ω
    have hr0 : 0 ≤ (stochMetrics M deltas n).risk (0, f 0 ω) := by
      show 0 ≤ stochDBudget deltas n 0
      exact Finset.sum_nonneg fun i _ => hnn i
    have hdelta0 : (0 : ℝ) ≤ (fun _ : ℕ × S => (0 : ℝ)) (0, f 0 ω) :=
      le_refl _
    have hdrops : ∀ j : Fin n,
        drops j.val = (certStochasticStep_to_bounded law M obl deltas
          n hnn f hbnb hflr j.isLt (certs j) ω (hgoodj j)).drop := by
      intro j
      have hd : drops j.val = (certs ⟨j.val, j.isLt⟩).drop :=
        dite_eq_left j.isLt
      rw [hd]
      rfl
    have hspends : ∀ j : Fin n,
        (M.budget (f j.val ω) - M.budget (f (j.val + 1) ω))
          = (certStochasticStep_to_bounded law M obl deltas
              n hnn f hbnb hflr j.isLt (certs j) ω
              (hgoodj j)).budgetSpend :=
      fun j => rfl
    have hrisks : ∀ j : Fin n,
        deltas j.val = (certStochasticStep_to_bounded law M obl deltas
          n hnn f hbnb hflr j.isLt (certs j) ω
          (hgoodj j)).riskSpend :=
      fun j => rfl
    have hdeltas : ∀ j : Fin n,
        (fun _ : ℕ => (0 : ℝ)) j.val
          = (certStochasticStep_to_bounded law M obl deltas
              n hnn f hbnb hflr j.isLt (certs j) ω
              (hgoodj j)).delta :=
      fun j => rfl
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ :=
      certified_loop_kernel (stochMetrics M deltas n) obl n
        (fun k => (k, f k ω)) hf0 hb0 hr0 hdelta0
        (fun j => certStochasticStep_to_bounded law M obl deltas n hnn f
          hbnb hflr j.isLt (certs j) ω (hgoodj j))
        drops
        (fun k => M.budget (f k ω) - M.budget (f (k + 1) ω))
        deltas (fun _ => (0 : ℝ))
        hdrops hspends hrisks hdeltas
    exact ⟨k1, k2, k3⟩

/-- СЛЕДСТВИЕ (whp total descent): суммарный сертифицированный
спуск ∑ drops ≤ obj₀ − obj_T выполняется с вероятностью
≥ 1 − ∑ δ_j (union bound + ядерный телескоп). -/
theorem stochastic_loop_descent_whp (law : PMF Ω)
    (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)
    (n : ℕ) (f : ℕ → Ω → S)
    (certs : ∀ j : Fin n, CertStochasticStep law
      (fun ω => M.objective (f j.val ω) - M.objective (f (j.val + 1) ω)))
    (deltas : ℕ → ℝ) (hnn : ∀ i, 0 ≤ deltas i)
    (hfail : ∀ j : Fin n, (certs j).failure ≤ deltas j.val)
    (hbnb : ∀ k ω, 0 ≤ M.budget (f k ω))
    (hflr : ∀ k ω, FloorsKept M obl (f k ω)) :
    pmfMean law (fun ω =>
        if ∑ j ∈ Finset.range n, chainDrops M f certs j
          ≤ M.objective (f 0 ω) - M.objective (f n ω)
          then (1 : ℝ) else 0)
      ≥ 1 - ∑ j ∈ Finset.range n, deltas j := by
  obtain ⟨h1, h2⟩ := stochastic_loop_certified law M obl n f certs
    deltas hnn hfail hbnb hflr
  refine le_trans h1 (pmfMean_mono law ?_)
  intro ω _
  by_cases hg : stochChainGood M f n (chainDrops M f certs) ω
  · have hdesc := (h2 ω hg).1
    rw [ite_eq_left hg, ite_eq_left hdesc]
  · simp only [hg, ite_false]
    split_ifs <;> norm_num

end Hagi.Unified.StochasticLoop
