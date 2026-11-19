/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.Freedman
set_option linter.style.header false

/-!
# Freedman для адаптированных дисперсий — история-зависимое q

C438 (хвост W5-аудита: «h_emp_var прячет вопрос адаптивности
дисперсии»; «конечные пространства историй с ФИКСИРОВАННЫМ
одношаговым q»). В `Hagi.Probability.Freedman` условное
распределение шага — один и тот же вектор q для каждого шага и
каждого префикса, σ — константа. Настоящий модуль снимает оба
ограничения на конечной prodPq-машине (Markov-kernel-машина
`FreedmanStep.freedman_full` уже adapted — здесь закрывается
дыра конечного формализма, потребляемого success-теоремами):

* условные веса `qd t pref : V → ℝ` — ФУНКЦИЯ префикса:
  зависимое произведение `densD qd` (snoc-рекурсия) вместо
  произведения одинаковых координатных весов `prodDens`;
* дисперсионная граница `sigBd t pref` — предсказуемый процесс,
  а не константа: хвост зависит от потраекторного бюджета
  `varComp sigBd (n := n) ω ≤ V` — суммы фактических префикс-зависимых
  границ.

**Теоремы:**

* `densD_snoc`, `expD_snoc` — башня ожиданий на зависимом
  произведении (через `Fin.snocEquiv`).
* `expD_one`, `probD_mono`, `probD_compl` — вероятностная
  инфраструктура (`IsProbSysD` — посылки на каждый префикс).
* `varComp_snoc`, `varComp_const` — предсказуемый компенсатор.
* `freedmanD_supermart` — E_{qd}[e^{λΣX − κ·varComp}] ≤ 1 при
  κ = λ²e^{λb}/2: условное среднее-ноль и условная дисперсия ≤
  sigBd t pref при КАЖДОМ префиксе (история-зависимое q!).
* `freedmanD_tail_low` — ГЛАВНЫЙ ХВОСТ (adapted Freedman,
  конечная машина):

  P_{qd}[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V + bΔ)))

  при потраекторном бюджете varComp ≤ V. Оптимизация
  λ = Δ/(V + bΔ), e^{λb} ≤ 1/(1−λb), 1−λb = V/den.
* `popoviciu_var_le` — Popoviciu: Σ q (S−m)² ≤ (b−a)²/4
  (дисперсия ограниченной величины; через оценку у середины
  Σ q (S−m)² ≤ Σ q (S−mid)², разница = (m−mid)²).
* `adaptive_success_freedman_adaptive` — РАЗРЯДКА `h_emp_var`:
  успехи S(pref) ∈ [0,1] с условными полами p₀ относительно
  история-зависимого qd, БЕЗ посылки дисперсии:

  1 − exp(−Δ²/(2(n/4 + Δ))) ≤ P_{qd}[ΣS ≥ n·p₀ − Δ]

  — дисперсия ≤ 1/4 ВЫВЕДЕНА (Popoviciu), а не постулирована;
  строго сильнее legacy σ = 1-хвоста exp(−Δ²/(2(n+Δ))).

**Честные границы**: b — константа (диапазон приращений общий
для шагов); anytime-форма и data-зависимый λ — открыто (как и
в `Hagi.Probability.Freedman`); случай V = 0 не выписан
(требуем 0 < V, как 0 < sig у предка).
-/

open Finset Real

namespace Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Зависимое произведение мер -/

/-- **Плотность зависимого произведения**: условный вес шага t
после префикса — `qd t pref`; snoc-рекурсия (ср. `prodDens` —
произведение одинаковых координатных весов). -/
def densD (qd : ∀ t, (Fin t → V) → V → ℝ) : ∀ {n : ℕ}, (Fin n → V) → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun ω => densD qd (fun i => ω i.castSucc)
      * qd n (fun i => ω i.castSucc) (ω (Fin.last n))

/-- **Ожидание на зависимом произведении** (конечная сумма). -/
def expD (qd : ∀ t, (Fin t → V) → V → ℝ) {n : ℕ}
    (f : (Fin n → V) → ℝ) : ℝ :=
  ∑ ω, densD qd ω * f ω

/-- **Вероятность события на зависимом произведении**. -/
def probD (qd : ∀ t, (Fin t → V) → V → ℝ) {n : ℕ}
    (P : (Fin n → V) → Prop) [DecidablePred P] : ℝ :=
  expD qd (fun ω => if P ω then (1 : ℝ) else 0)

/-- **Условные веса — вероятностные векторы при каждом
префиксе** (посылка adapted-машины). -/
def IsProbSysD (qd : ∀ t, (Fin t → V) → V → ℝ) : Prop :=
  ∀ t pref, (∀ v, 0 ≤ qd t pref v) ∧ ∑ v, qd t pref v = 1

omit [Fintype V] [Nonempty V] in
/-- **Snoc-форма плотности**: вес траектории snoc pref v —
произведение веса префикса на условный вес свежей координаты. -/
theorem densD_snoc (qd : ∀ t, (Fin t → V) → V → ℝ) {n : ℕ}
    (pref : Fin n → V) (v : V) :
    densD qd (Fin.snoc (α := fun _ => V) pref v)
      = densD qd pref * qd n pref v := by
  have hpref : (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
      = pref := funext fun i => by
    simp
  have hlast : (Fin.snoc (α := fun _ => V) pref v) (Fin.last n) = v := by
    simp
  show densD qd (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
      * qd n (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
        (Fin.snoc (α := fun _ => V) pref v (Fin.last n)) = _
  rw [hpref, hlast]

omit [Nonempty V] in
/-- **Неотрицательность плотности** (при вероятностных весах). -/
theorem densD_nonneg (qd : ∀ t, (Fin t → V) → V → ℝ)
    (hq : IsProbSysD qd) :
    ∀ {n : ℕ}, ∀ ω : Fin n → V, 0 ≤ densD qd ω := by
  intro n
  induction n with
  | zero => intro ω; exact zero_le_one
  | succ n ih =>
      intro ω
      show 0 ≤ densD qd (fun i : Fin n => ω i.castSucc)
        * qd n (fun i : Fin n => ω i.castSucc) (ω (Fin.last n))
      exact mul_nonneg (ih _) ((hq n _).1 _)

omit [Nonempty V] in
/-- **Башня ожиданий на зависимом произведении**: сумма по
последней координате использует условные веса `qd n pref`. -/
theorem expD_snoc (qd : ∀ t, (Fin t → V) → V → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → V) → ℝ) :
    expD qd f
      = ∑ pref : Fin n → V, densD qd pref
        * ∑ v, qd n pref v * f (Fin.snoc (α := fun _ => V) pref v) := by
  classical
  unfold expD
  rw [← Fintype.sum_equiv (Fin.snocEquiv (n := n) (fun _ => V))
    (fun xp => densD qd (Fin.snoc (α := fun _ => V) xp.2 xp.1)
      * f (Fin.snoc (α := fun _ => V) xp.2 xp.1))
    (fun ω => densD qd ω * f ω)
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro pref _
  have hd : ∀ v : V, densD qd (Fin.snoc (α := fun _ => V) pref v)
      * f (Fin.snoc (α := fun _ => V) pref v)
      = densD qd pref * (qd n pref v
        * f (Fin.snoc (α := fun _ => V) pref v)) := by
    intro v
    rw [densD_snoc qd pref v]
    ring
  calc ∑ v, densD qd (Fin.snoc (α := fun _ => V)
          (Prod.snd (v, pref)) (Prod.fst (v, pref)))
        * f (Fin.snoc (α := fun _ => V)
          (Prod.snd (v, pref)) (Prod.fst (v, pref)))
      = ∑ v, densD qd pref
          * (qd n pref v
            * f (Fin.snoc (α := fun _ => V) pref v)) :=
        Finset.sum_congr rfl fun v _ => by simpa using hd v
    _ = densD qd pref * ∑ v, qd n pref v
        * f (Fin.snoc (α := fun _ => V) pref v) := by
        rw [Finset.mul_sum]

omit [Nonempty V] in
/-- **Полная масса зависимого произведения** = 1. -/
theorem expD_one (qd : ∀ t, (Fin t → V) → V → ℝ) (hq : IsProbSysD qd) :
    ∀ {n : ℕ}, expD qd (fun _ : Fin n → V => (1 : ℝ)) = 1 := by
  intro n
  induction n with
  | zero => simp [expD, densD]
  | succ n ih =>
      rw [expD_snoc qd n (fun _ : Fin (n + 1) → V => (1 : ℝ))]
      have hinner : ∀ pref : Fin n → V,
          ∑ v, qd n pref v * (1 : ℝ) = 1 := fun pref => by
        simpa using (hq n pref).2
      rw [Finset.sum_congr rfl (fun pref _ => by rw [hinner pref, mul_one])]
      simpa [expD, mul_one] using ih

omit [Nonempty V] in
/-- **Монотонность вероятности на зависимом произведении**. -/
theorem probD_mono (qd : ∀ t, (Fin t → V) → V → ℝ) (hq : IsProbSysD qd)
    {n : ℕ}
    (P Q : (Fin n → V) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, P ω → Q ω) :
    probD qd P ≤ probD qd Q := by
  unfold probD expD
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hP : P ω
  · by_cases hQ : Q ω
    · simp [hP, hQ, densD_nonneg qd hq]
    · exact absurd (h ω hP) hQ
  · by_cases hQ : Q ω
    · simp [hP, hQ, densD_nonneg qd hq]
    · simp [hP, hQ]

omit [Nonempty V] in
/-- **Дополнение события на зависимом произведении**. -/
theorem probD_compl (qd : ∀ t, (Fin t → V) → V → ℝ)
    (hq : IsProbSysD qd) {n : ℕ}
    (P : (Fin n → V) → Prop) [DecidablePred P] :
    probD qd (fun ω => ¬ P ω) = 1 - probD qd P := by
  classical
  have hsplit : expD qd (n := n) (fun ω => (1 : ℝ))
      = expD qd (fun ω => (if P ω then (1 : ℝ) else 0)
        + (if ¬ P ω then (1 : ℝ) else 0)) := by
    congr 1
    funext ω
    by_cases hP : P ω <;> simp [hP]
  have hone := expD_one qd hq (n := n)
  rw [hsplit] at hone
  unfold probD at ⊢
  unfold expD at hone ⊢
  have hsum : ∑ ω, densD qd ω * ((if P ω then (1 : ℝ) else 0)
      + (if ¬ P ω then (1 : ℝ) else 0))
      = ∑ ω, densD qd ω * (if P ω then (1 : ℝ) else 0)
        + ∑ ω, densD qd ω * (if ¬ P ω then (1 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hsum] at hone
  linarith

/-! ## Предсказуемый дисперсионный компенсатор -/

/-- **Предсказуемый компенсатор**: snoc-рекурсия, шаг добавляет
дисперсионную границу `sigBd n pref` (функцию префикса). -/
def varComp (sigBd : ∀ t, (Fin t → V) → ℝ) : ∀ {n : ℕ}, (Fin n → V) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => varComp sigBd (fun i => ω i.castSucc)
      + sigBd n (fun i => ω i.castSucc)

omit [Fintype V] [Nonempty V] in
/-- **Snoc-форма компенсатора**. -/
theorem varComp_snoc (sigBd : ∀ t, (Fin t → V) → ℝ) {n : ℕ}
    (pref : Fin n → V) (v : V) :
    varComp sigBd (Fin.snoc (α := fun _ => V) pref v)
      = varComp sigBd pref + sigBd n pref := by
  have hpref : (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
      = pref := funext fun i => by
    simp
  show varComp sigBd (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc)
      + sigBd n (fun i : Fin n => (Fin.snoc (α := fun _ => V) pref v) i.castSucc) = _
  rw [hpref]

omit [Fintype V] [Nonempty V] in
/-- **Константная граница ⇒ детерминированный бюджет n·c.** -/
theorem varComp_const (c : ℝ) :
    ∀ (n : ℕ) (ω : Fin n → V),
    varComp (fun _ _ => c) (n := n) ω = n * c := by
  intro n
  induction n with
  | zero => intro ω; simp [varComp]
  | succ n ih =>
      intro ω
      show varComp (fun _ _ => c) (fun i : Fin n => ω i.castSucc)
          + c = _
      rw [ih]
      push_cast
      ring

/-! ## Супермартингал Freedman на зависимом произведении -/

/-- **Супермартингал Freedman (adapted)**: при условно
центрированных приращениях (|X| ≤ b, Σ qd·X = 0, Σ qd·X² ≤
sigBd t pref при каждом префиксе, с история-зависимым qd)
E_{qd}[e^{λΣX − κ·varComp}] ≤ 1, κ = λ²e^{λb}/2. Индукция по n:
шаг — условная лемма `freedman_lemma_prefix` на qd n pref. -/
theorem freedmanD_supermart (qd : ∀ t, (Fin t → V) → V → ℝ)
    (hq : IsProbSysD qd)
    (X : ∀ t, (Fin t → V) → ℝ) (b : ℝ)
    (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sigBd : ∀ t, (Fin t → V) → ℝ)
    (hsBd : ∀ t pref, 0 ≤ sigBd t pref)
    (hmean : ∀ t pref,
      ∑ v, qd t pref v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, qd t pref v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sigBd t pref)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ n : ℕ, expD qd (fun ω => Real.exp (lam * azumaSum X n ω
      - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) ≤ 1 := by
  intro n
  induction n with
  | zero => simp [expD, densD, azumaSum, varComp]
  | succ n ih =>
      rw [expD_snoc qd n]
      -- факторизация F (snoc pref v) = C pref * e^{λX} * e^{−κσ²}
      have hfac : ∀ pref : Fin n → V, ∀ v : V,
          Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v)
            - (lam ^ 2 * Real.exp (lam * b) / 2)
              * varComp sigBd (n := n + 1) (Fin.snoc (α := fun _ => V) pref v))
          = Real.exp (lam * azumaSum X n pref
              - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
            * (Real.exp (lam * X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v))
              * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2)
                * sigBd n pref)) := by
        intro pref v
        rw [azumaSum_snoc X n pref v, varComp_snoc sigBd pref,
          ← Real.exp_add, ← Real.exp_add]
        ring
      -- внутренняя сумма: условная лемма на qd n pref
      have hinner : ∀ pref : Fin n → V,
          ∑ v, qd n pref v * Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v)
            - (lam ^ 2 * Real.exp (lam * b) / 2)
              * varComp sigBd (n := n + 1) (Fin.snoc (α := fun _ => V) pref v))
          ≤ Real.exp (lam * azumaSum X n pref
            - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref) := by
        intro pref
        have hsplit : ∑ v, qd n pref v * Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v)
            - (lam ^ 2 * Real.exp (lam * b) / 2)
              * varComp sigBd (n := n + 1) (Fin.snoc (α := fun _ => V) pref v))
            = Real.exp (lam * azumaSum X n pref
                - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
              * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref)
              * ∑ v, qd n pref v * Real.exp (lam * X (n + 1)
                  (Fin.snoc (α := fun _ => V) pref v)) := by
          have hterm : ∀ v : V, qd n pref v * Real.exp (lam * azumaSum X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v)
              - (lam ^ 2 * Real.exp (lam * b) / 2)
                * varComp sigBd (n := n + 1) (Fin.snoc (α := fun _ => V) pref v))
              = Real.exp (lam * azumaSum X n pref
                  - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
                * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref)
                * (qd n pref v * Real.exp (lam * X (n + 1)
                    (Fin.snoc (α := fun _ => V) pref v))) := by
            intro v
            rw [hfac pref v]
            ring
          rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.mul_sum]
        rw [hsplit]
        -- mgf шага по условной мере qd n pref
        have hmgf := freedman_lemma_prefix (qd n pref) (hq n pref).1
          (hq n pref).2
          (fun v => X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) b
          (fun v => hbnd (n + 1) (Fin.snoc (α := fun _ => V) pref v))
          (hmean n pref) (sigBd n pref) (hsBd n pref) (hvar n pref) lam hlam
        have hnn : 0 ≤ Real.exp (lam * azumaSum X n pref
              - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
            * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref) :=
          mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
        calc Real.exp (lam * azumaSum X n pref
              - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
              * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref)
              * ∑ v, qd n pref v * Real.exp (lam * X (n + 1)
                  (Fin.snoc (α := fun _ => V) pref v))
            ≤ Real.exp (lam * azumaSum X n pref
                - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
              * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref)
              * Real.exp (lam ^ 2 * sigBd n pref * Real.exp (lam * b) / 2) :=
              mul_le_mul_of_nonneg_left hmgf hnn
          _ = Real.exp (lam * azumaSum X n pref
                - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref) := by
              have hz2 : Real.exp (lam * azumaSum X n pref
                  - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref)
                  * Real.exp (- (lam ^ 2 * Real.exp (lam * b) / 2) * sigBd n pref)
                  * Real.exp (lam ^ 2 * sigBd n pref * Real.exp (lam * b) / 2)
                  = Real.exp (lam * azumaSum X n pref
                    - (lam ^ 2 * Real.exp (lam * b) / 2)
                      * varComp sigBd (n := n) pref) := by
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
                ring
              rw [hz2]
      -- сжатие и индукция
      calc ∑ pref : Fin n → V, densD qd pref
              * ∑ v, qd n pref v * Real.exp (lam * azumaSum X (n + 1)
                  (Fin.snoc (α := fun _ => V) pref v)
                - (lam ^ 2 * Real.exp (lam * b) / 2)
                  * varComp sigBd (n := n + 1) (Fin.snoc (α := fun _ => V) pref v))
            ≤ ∑ pref : Fin n → V, densD qd pref
                * Real.exp (lam * azumaSum X n pref
                  - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) pref) :=
              Finset.sum_le_sum fun pref _ =>
                mul_le_mul_of_nonneg_left (hinner pref) (densD_nonneg qd hq _)
          _ = expD qd (fun ω => Real.exp (lam * azumaSum X n ω
                - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) := rfl
          _ ≤ 1 := ih

/-! ## Adapted-хвост Freedman -/

/-- **Freedman-хвост с адаптированной дисперсией (ГЛАВНЫЙ)**:
для условно центрированных приращений относительно
ИСТОРИЯ-ЗАВИСИМОГО qd (Σ qd t pref·X = 0 при каждом префиксе),
диапазона |X| ≤ b и ПРЕДСКАЗУЕМОЙ дисперсионной границы
Σ qd t pref·X² ≤ sigBd t pref с потраекторным бюджетом
varComp sigBd (n := n) ω ≤ V:

  P_{qd}[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(V + bΔ)))

— бюджет V вместо расточительного n·σ² константной версии
`freedman_tail_low`. Оптимизация λ = Δ/(V+bΔ), e^{λb} ≤
1/(1−λb) с сопряжённой парой `Real.add_one_le_exp`. -/
theorem freedmanD_tail_low (qd : ∀ t, (Fin t → V) → V → ℝ)
    (hq : IsProbSysD qd)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sigBd : ∀ t, (Fin t → V) → ℝ)
    (hsBd : ∀ t pref, 0 ≤ sigBd t pref)
    (hmean : ∀ t pref,
      ∑ v, qd t pref v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, qd t pref v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sigBd t pref)
    (n : ℕ) (Vtot : ℝ) (hV : 0 < Vtot)
    (hVt : ∀ ω : Fin n → V, varComp sigBd (n := n) ω ≤ Vtot)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    probD qd (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * (Vtot + b * Δ))) := by
  classical
  set den : ℝ := Vtot + b * Δ with hden
  set lam : ℝ := Δ / den with hlams
  have hdenpos : 0 < den := by
    have := hV
    have := hΔ
    have := hb
    unfold den
    positivity
  have hlamage : 0 ≤ lam := div_nonneg hΔ.le hdenpos.le
  have hkapnn : 0 ≤ lam ^ 2 * Real.exp (lam * b) / 2 := by positivity
  -- суперmartингал для (−X)
  have hsuper : expD qd (fun ω => Real.exp (lam * (- azumaSum X n ω)
      - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) ≤ 1 := by
    have hrw : (fun ω => Real.exp (lam * (- azumaSum X n ω)
        - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω))
        = (fun ω => Real.exp (lam
          * azumaSum (fun t pref => - X t pref) n ω
          - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) :=
      funext fun ω => by rw [azumaSum_neg X n ω]
    rw [hrw]
    refine freedmanD_supermart qd hq (fun t pref => - X t pref) b
      (fun t pref => by rw [abs_neg]; exact hbnd t pref)
      sigBd hsBd
      (fun t pref => by
        have h0 := hmean t pref
        have hneg : ∑ v, qd t pref v * (- X (t + 1)
            (Fin.snoc (α := fun _ => V) pref v))
            = - ∑ v, qd t pref v * X (t + 1)
              (Fin.snoc (α := fun _ => V) pref v) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [hneg, h0]
        ring)
      (fun t pref => by
        have h0 := hvar t pref
        have hsq : ∀ v, qd t pref v
            * (- X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
            = qd t pref v * (X (t + 1)
              (Fin.snoc (α := fun _ => V) pref v)) ^ 2 := by
          intro v
          rw [neg_sq]
        rw [Finset.sum_congr rfl (fun v _ => hsq v)]
        exact h0)
      lam hlamage n
  -- поточечный Markov-мажорант
  have hmark : ∀ ω : Fin n → V,
      (if azumaSum X n ω ≤ -Δ then (1 : ℝ) else 0)
      ≤ Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
        * Real.exp (lam * (- azumaSum X n ω)
          - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω) := by
    intro ω
    by_cases hω : azumaSum X n ω ≤ -Δ
    · have hkey : Δ ≤ - azumaSum X n ω := by
        have := hω
        linarith
      have h1 : lam * Δ ≤ lam * (- azumaSum X n ω) :=
        mul_le_mul_of_nonneg_left hkey hlamage
      have h2 : - (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot
          ≤ - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω := by
        have hle := hVt ω
        nlinarith [hkapnn]
      have hexp : Real.exp (lam * Δ - (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          ≤ Real.exp (lam * (- azumaSum X n ω)
            - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω) :=
        Real.exp_le_exp.mpr (by linarith)
      have hX : Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          * Real.exp (lam * Δ - (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          = 1 := by
        rw [← Real.exp_add,
          show (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
            + (lam * Δ - (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot) = 0 from by ring,
          Real.exp_zero]
      simp only [hω, ite_true]
      calc (1 : ℝ) = Real.exp (- lam * Δ
              + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
            * Real.exp (lam * Δ - (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot) :=
            hX.symm
        _ ≤ Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
            * Real.exp (lam * (- azumaSum X n ω)
              - (lam ^ 2 * Real.exp (lam * b) / 2)
                * varComp sigBd (n := n) ω) :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    · simp only [hω, ite_false]
      positivity
  -- связка Markov
  have hbind : probD qd (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot) := by
    unfold probD
    have hle : expD qd (fun ω => if azumaSum X n ω ≤ -Δ then (1 : ℝ) else 0)
        ≤ expD qd (fun ω => Real.exp
            (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          * Real.exp (lam * (- azumaSum X n ω)
            - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) := by
      unfold expD
      refine Finset.sum_le_sum fun ω _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (densD_nonneg qd hq _)
      simpa using hmark ω
    have hmul : expD qd (fun ω => Real.exp
          (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          * Real.exp (lam * (- azumaSum X n ω)
            - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω))
        = Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
          * expD qd (fun ω => Real.exp (lam * (- azumaSum X n ω)
            - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) := by
      unfold expD
      have hterm : ∀ ω : Fin n → V,
          densD qd ω * (Real.exp
              (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
            * Real.exp (lam * (- azumaSum X n ω)
              - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω))
          = Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
            * (densD qd ω * Real.exp (lam * (- azumaSum X n ω)
              - (lam ^ 2 * Real.exp (lam * b) / 2) * varComp sigBd (n := n) ω)) :=
        fun ω => by ring
      rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.mul_sum]
    refine le_trans hle ?_
    rw [hmul]
    exact (mul_le_mul_of_nonneg_left hsuper (Real.exp_pos _).le).trans_eq (mul_one _)
  -- λ-оптимизация: λ = Δ/den, e^{λb} ≤ den/V
  have hlam_b : lam * b < 1 := by
    rw [hlams]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
    unfold den
    nlinarith [hV]
  have hone : 1 - lam * b ≤ Real.exp (-(lam * b)) := by
    have h := Real.add_one_le_exp (-(lam * b))
    linarith
  have hexpb : Real.exp (lam * b) ≤ den / Vtot := by
    have hd : den ≠ 0 := ne_of_gt hdenpos
    have hsub : 1 - lam * b = Vtot / den := by
      rw [eq_div_iff hd]
      rw [hlams]
      field_simp
      rw [hden]
      ring
    have h1 : Real.exp (lam * b) * (Vtot / den) ≤ 1 := by
      have hpos : (0 : ℝ) < Real.exp (lam * b) := Real.exp_pos _
      have hmul : Real.exp (lam * b) * Real.exp (-(lam * b)) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hsub] at hone
      have h2 : Real.exp (lam * b) * (Vtot / den)
          ≤ Real.exp (lam * b) * Real.exp (-(lam * b)) :=
        mul_le_mul_of_nonneg_left hone hpos.le
      rwa [hmul] at h2
    have hVpos : (0 : ℝ) < Vtot := hV
    rw [le_div_iff₀ hVpos]
    have hA : Real.exp (lam * b) * Vtot ≤ den := by
      have hconv : Real.exp (lam * b) * (Vtot / den)
          = (Real.exp (lam * b) * Vtot) / den := by ring
      rw [hconv] at h1
      exact (div_le_one hdenpos).mp h1
    exact hA
  have hlamΔ : lam * Δ = Δ ^ 2 / den := by
    rw [hlams]
    field_simp
  have hfinal : Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot)
      ≤ Real.exp (- Δ ^ 2 / (2 * den)) := by
    refine Real.exp_le_exp.mpr ?_
    have hVpos : (0 : ℝ) < Vtot := hV
    have hsplit : lam ^ 2 = Δ ^ 2 / den ^ 2 := by
      rw [hlams]
      rw [div_pow]
    have hbound : (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot
        ≤ Δ ^ 2 / (2 * den) := by
      rw [hsplit]
      have hd0 : den ≠ 0 := ne_of_gt hdenpos
      have hV0 : Vtot ≠ 0 := ne_of_gt hV
      calc ((Δ ^ 2 / den ^ 2) * Real.exp (lam * b) / 2) * Vtot
          ≤ ((Δ ^ 2 / den ^ 2) * (den / Vtot) / 2) * Vtot := by
            gcongr
        _ = Δ ^ 2 / (2 * den) := by
            field_simp
    have hneg : -lam * Δ = -(lam * Δ) := by ring
    rw [hneg, hlamΔ]
    have h2 : Δ ^ 2 / den - Δ ^ 2 / (2 * den) = Δ ^ 2 / (2 * den) := by
      field_simp
      ring
    have hkey : (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot
        ≤ Δ ^ 2 / den - Δ ^ 2 / (2 * den) := by
      rw [h2]
      exact hbound
    have hsplit' : -Δ ^ 2 / (2 * den) = -(Δ ^ 2 / (2 * den)) := by ring
    rw [hsplit']
    linarith
  calc probD qd (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- lam * Δ + (lam ^ 2 * Real.exp (lam * b) / 2) * Vtot) := hbind
    _ ≤ Real.exp (- Δ ^ 2 / (2 * den)) := hfinal
    _ = Real.exp (- Δ ^ 2 / (2 * (Vtot + b * Δ))) := by rw [hden]

/-! ## Popoviciu и разрядка дисперсионной посылки -/

omit [Nonempty V] in
/-- **Popoviciu**: дисперсия величины в [a, b] ≤ (b−a)²/4.
Доказательство: Σ q (S−m)² ≤ Σ q (S−mid)² (разница = (m−mid)²)
и поточечная (S−mid)² ≤ ((b−a)/2)². -/
theorem popoviciu_var_le (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (S : V → ℝ) (a b : ℝ)
    (ha : ∀ v, a ≤ S v) (hb : ∀ v, S v ≤ b) :
    ∑ v, q v * (S v - ∑ u, q u * S u) ^ 2 ≤ (b - a) ^ 2 / 4 := by
  set m : ℝ := ∑ u, q u * S u with hm
  set mid : ℝ := (a + b) / 2 with hmid
  have hpt : ∀ v, (S v - mid) ^ 2 ≤ ((b - a) / 2) ^ 2 := by
    intro v
    have h1 : S v - mid ≤ (b - a) / 2 := by
      unfold mid; field_simp; linarith [ha v, hb v]
    have h2 : -((b - a) / 2) ≤ S v - mid := by
      unfold mid; field_simp; linarith [ha v, hb v]
    have := abs_le.mpr ⟨h2, h1⟩
    nlinarith [this, sq_nonneg (S v - mid)]
  have hexp : ∀ c : ℝ, ∑ v, q v * (S v - c) ^ 2
      = ∑ v, q v * (S v) ^ 2 - 2 * c * m + c ^ 2 := by
    intro c
    have h1 : ∀ v, q v * (S v - c) ^ 2
        = q v * (S v) ^ 2 - 2 * c * (q v * S v) + q v * c ^ 2 := by
      intro v; ring
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    have h2 : ∑ v, 2 * c * (q v * S v) = 2 * c * m := by
      rw [hm, ← Finset.mul_sum]
    have h3 : ∑ v, q v * c ^ 2 = c ^ 2 := by
      rw [Finset.sum_congr rfl (fun v _ =>
          (by ring : q v * c ^ 2 = c ^ 2 * q v)),
        ← Finset.mul_sum, hq1, mul_one]
    rw [h2, h3]
  have hkey : ∑ v, q v * (S v - mid) ^ 2
      = ∑ v, q v * (S v - m) ^ 2 + (m - mid) ^ 2 := by
    rw [hexp m, hexp mid]; ring
  have hmidb : ∑ v, q v * (S v - mid) ^ 2
      ≤ ∑ v, q v * (((b - a) / 2) ^ 2) :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hpt v) (hq0 v)
  rw [Finset.sum_congr rfl (fun v _ =>
      (by ring : q v * ((b - a) / 2) ^ 2 = ((b - a) / 2) ^ 2 * q v)),
    ← Finset.mul_sum, hq1, mul_one] at hmidb
  have hfinal : ((b - a : ℝ) / 2) ^ 2 = (b - a) ^ 2 / 4 := by ring
  rw [hfinal] at hmidb
  linarith [hkey, hmidb, sq_nonneg (m - mid)]

/-- **Успехи с история-зависимым q, Freedman с ВЫВЕДЕННОЙ
дисперсией (разрядка h_emp_var)**: успехи S_{t+1}(префикс) ∈
[0,1] с условными полами p₀ относительно зависимого qd
(посылки при КАЖДОМ префиксе) — дисперсионная посылка НЕ
нужна: центрированная условная дисперсия ≤ 1/4 выведена
`popoviciu_var_le`:

  azumaSum S n ≥ n·p₀ − Δ  w.p. ≥ 1 − exp(−Δ²/(2(n/4 + Δ)))

Хвост строго сильнее legacy-версии с σ = 1
(`adaptive_success_freedman`: exp(−Δ²/(2(n·1 + Δ)))) и
условная мера — история-зависимое произведение, а не
произведение фиксированных весов. -/
theorem adaptive_success_freedman_adaptive (qd : ∀ t, (Fin t → V) → V → ℝ)
    (hq : IsProbSysD qd)
    (S : ∀ t, (Fin t → V) → ℝ)
    (hS : ∀ t pref, 0 ≤ S t pref ∧ S t pref ≤ 1)
    (p0 : ℝ)
    (hfloor : ∀ t pref,
      p0 ≤ ∑ v, qd t pref v * S (t + 1) (Fin.snoc (α := fun _ => V) pref v))
    (n : ℕ) (hn : 0 < n) (Δ : ℝ) (hΔ : 0 < Δ) :
    1 - Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) / 4 + Δ)))
      ≤ probD qd (fun ω => n * p0 - Δ ≤ azumaSum S n ω) := by
  classical
  -- центрированные приращения
  set m : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    ∑ v, qd t pref v * S (t + 1) (Fin.snoc (α := fun _ => V) pref v) with hmdef
  set Z : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    match t with
    | 0 => 0
    | t + 1 => S (t + 1) pref
        - m t (Fin.init (α := fun _ => V) pref) with hZdef
  have hm01 : ∀ t pref, 0 ≤ m t pref ∧ m t pref ≤ 1 := by
    intro t pref
    constructor
    · exact Finset.sum_nonneg fun v _ =>
        mul_nonneg ((hq t pref).1 v) (hS (t + 1) _).1
    · have hle : m t pref ≤ ∑ v, qd t pref v * (1 : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hS (t + 1) _).2 ((hq t pref).1 v)
      have hrw : ∑ v, qd t pref v * (1 : ℝ) = 1 := by
        simp [(hq t pref).2]
      rw [hmdef] at hle
      linarith
  have hZbnd : ∀ t pref, |Z t pref| ≤ 1 := by
    intro t pref
    match t with
    | 0 => simp [hZdef]
    | t + 1 =>
        have h1 := hS (t + 1) pref
        have h2 := hm01 t (Fin.init (α := fun _ => V) pref)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmeanZ : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, qd t pref v * Z (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0 := by
    intro t pref
    have hinit : ∀ v, Fin.init (α := fun _ => V)
        (Fin.snoc (α := fun _ => V) pref v) = pref :=
      fun v => by simpa using Fin.init_snoc pref v
    have hZterm : ∀ v, Z (t + 1) (Fin.snoc pref v)
        = S (t + 1) (Fin.snoc pref v) - m t pref := by
      intro v
      simp only [hZdef]
      rw [hinit v]
    rw [Finset.sum_congr rfl (fun v _ => by
      rw [hZterm v])]
    have hsplit2 : ∑ v, qd t pref v * (S (t + 1) (Fin.snoc pref v)
          - m t pref)
        = ∑ v, qd t pref v * S (t + 1) (Fin.snoc pref v)
          - ∑ v, qd t pref v * (m t pref) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsplit2]
    have hfirst : ∑ v, qd t pref v * S (t + 1) (Fin.snoc pref v)
        = m t pref := by simp only [hmdef]
    have hsecond : ∑ v, qd t pref v * m t pref = m t pref := by
      rw [← Finset.sum_mul, (hq t pref).2]
      simp
    rw [hfirst, hsecond]
    ring
  -- условная дисперсия Z ≤ 1/4: Popoviciu (h_emp_var РАЗРЯЖЕНА)
  have hvarZ : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, qd t pref v * (Z (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ 1 / 4 := by
    intro t pref
    have hZterm : ∀ v, Z (t + 1) (Fin.snoc (α := fun _ => V) pref v)
        = S (t + 1) (Fin.snoc (α := fun _ => V) pref v) - m t pref := by
      intro v
      simp only [hZdef]
      simpa using congrArg (fun π => S (t + 1) π
        - m t (Fin.init (α := fun _ => V) π))
        (Fin.init_snoc pref v)
    rw [Finset.sum_congr rfl (fun v _ => by rw [hZterm v])]
    have hrw : ∑ u, qd t pref u * S (t + 1)
        (Fin.snoc (α := fun _ => V) pref u)
        = m t pref := by simp only [hmdef]
    have hpop := popoviciu_var_le (qd t pref) (hq t pref).1 (hq t pref).2
      (fun v => S (t + 1) (Fin.snoc (α := fun _ => V) pref v)) 0 1
      (fun v => (hS (t + 1) _).1) (fun v => (hS (t + 1) _).2)
    rw [hrw] at hpop
    have hone : ((1 : ℝ) - 0) ^ 2 / 4 = 1 / 4 := by ring
    rw [hone] at hpop
    exact hpop
  -- Freedman-хвост для Z с b = 1, бюджетом n/4
  have hVpos : (0 : ℝ) < (n : ℝ) / 4 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hVt : ∀ ω : Fin n → V,
      varComp (fun _ _ => (1 / 4 : ℝ)) (n := n) ω ≤ (n : ℝ) / 4 := by
    intro ω
    rw [varComp_const]
    have hconv : (n : ℝ) * (1 / 4 : ℝ) = (n : ℝ) / 4 := by ring
    rw [hconv]
  have htail := freedmanD_tail_low qd hq Z 1 (by norm_num) hZbnd
    (fun _ _ => (1 / 4 : ℝ)) (fun _ _ => by positivity) hmeanZ hvarZ
    n ((n : ℝ) / 4) hVpos hVt Δ hΔ
  -- разложение azumaSum Z = azumaSum S − azumaSum m'
  set m' : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    match t with
    | 0 => S 0 pref
    | t + 1 => m t (Fin.init (α := fun _ => V) pref) with hm'def
  have hZeq : ∀ t pref, Z t pref = S t pref - m' t pref := by
    intro t pref
    match t with
    | 0 => simp [hZdef, hm'def]
    | t + 1 => simp [hZdef, hm'def]
  have hsplit : ∀ ω : Fin n → V,
      azumaSum Z n ω
        = azumaSum S n ω - azumaSum m' n ω := by
    intro ω
    rw [azumaSum_ext Z (fun t pref => S t pref - m' t pref)
      hZeq n ω]
    exact azumaSum_sub S m' n ω
  have hmlower : ∀ ω : Fin n → V,
      (n : ℝ) * p0 ≤ azumaSum m' n ω := by
    intro ω
    refine azumaSum_lower m' p0 ?_ n ω
    intro t pref
    rw [hm'def]
    show p0 ≤ m t (Fin.init (α := fun _ => V) pref)
    rw [hmdef]
    exact hfloor t (Fin.init (α := fun _ => V) pref)
  have hmono : probD qd
      (fun ω => azumaSum S n ω < n * p0 - Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) / 4 + Δ))) := by
    have himpl : ∀ ω : Fin n → V,
        azumaSum S n ω < n * p0 - Δ → azumaSum Z n ω ≤ -Δ := by
      intro ω hω
      rw [hsplit]
      have h1 := hmlower ω
      linarith
    rw [one_mul] at htail
    exact le_trans (probD_mono qd hq
      (fun ω => azumaSum S n ω < n * p0 - Δ)
      (fun ω => azumaSum Z n ω ≤ -Δ) himpl) htail
  have hcompl : probD qd
      (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ))
      = 1 - probD qd (fun ω => azumaSum S n ω < n * p0 - Δ) :=
    probD_compl qd hq _
  calc (1 : ℝ) - Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) / 4 + Δ)))
      ≤ 1 - probD qd (fun ω => azumaSum S n ω < n * p0 - Δ) := by
          linarith [hmono]
    _ = probD qd (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ)) := hcompl.symm
    _ ≤ probD qd (fun ω => n * p0 - Δ ≤ azumaSum S n ω) :=
          probD_mono qd hq _ _ (fun ω hω => not_lt.mp hω)

end Hagi.Probability
