/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.Azuma
import Mathlib
set_option linter.style.header false

/-!
# Freedman-канон

Canonical Freedman concentration family in one file: variance-adapted
Freedman inequality, two-sided confidence forms, step/history-additive
analysis, adaptive martingale forms, finite-family simultaneous confidence.
-/

/-!
# Freedman вместо Azuma — дисперсионная адаптация

Азума мажорирует приращения диапазоном [−c, c]: хвост
exp(−Δ²/(2nc²)). Если типичный шаг МАЛ (дисперсия σ² ≪ c²),
Азума расточительна. Freedman (arXiv 2609.37787 скалярная L∞-форма;
2607.18899 совместная форма)
заменяет nc² на nσ² + bΔ — накопленную условную дисперсию с
поправкой на диапазон b:

  P[ΣX ≤ −Δ] ≤ exp(−Δ² / (2(nσ² + bΔ))).

**План доказательства** (конечный порт, без measure-theory):

* `exp_tail_two` — хвост экспоненты рядом Тейлора:
  e^u ≤ 1 + u + (u²/2)e^{|u|} (HasSum-мажорация хвоста k ≥ 2
  через (k+2)! ≥ 2·k!).
* `freedman_lemma_prefix` — условная лемма Бернштейна: при
  условном среднем-ноль, |X| ≤ b и условной дисперсии
  Σ q·X² ≤ σ² mgf шага ≤ exp((λ²σ²/2)e^{λb}).
* `freedman_mgf` — мартингальный mgf: prodE e^{λΣX} ≤
  exp(n·λ²σ²e^{λb}/2) индукцией по n (snoc-декомпозиция).
* `freedman_tail_low` — Freedman-хвост с оптимизацией
  λ = Δ/(nσ²+bΔ) и e^{λb} ≤ 1/(1−λb) (сопряжённая пара
  add_one_le_exp).
* `adaptive_success_freedman` — дисперсионное усиление
  `adaptive_success_azuma`: полы p₀ при каждом префиксе +
  измеренная условная дисперсия σ²_success ⇒ ΣS ≥ n·p₀ − Δ
  с вероятностью ≥ 1 − exp(−Δ²/(2(nσ² + Δ))); при σ² = 1 хвост
  совпадает с Azuma, при σ² < 1 СИЛЬНЕЕ.

**Честные границы**: σ² — измеряемая посылка (условная
дисперсия при каждом префиксе — runtime-измерение, не следствие
iid); b — конструкторский диапазон приращений. Совместная и anytime-формы —
на Markov-машине ниже (`history_additive_freedman_maximal`).
-/

open Finset Real

namespace Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Хвост экспоненты рядом Тейлора -/

/-- **Хвост экспоненты**: e^u ≤ 1 + u + (u²/2)e^{|u|}.
Ряд Тейлора e^u = Σ uⁿ/n!, хвост с n ≥ 2 мажорируется
геометрически: u^{k+2}/(k+2)! ≤ (u²/2)·|u|^k/k!, поскольку
(k+2)! ≥ 2·k!. -/
theorem exp_tail_two (u : ℝ) :
    Real.exp u ≤ 1 + u + (u ^ 2 / 2) * Real.exp |u| := by
  classical
  -- производные компоненты
  have hd1 : ∀ t, HasDerivAt (fun x => Real.exp (x * u))
      (Real.exp (t * u) * u) t := by
    intro t
    have h : DifferentiableAt ℝ (fun x => Real.exp (x * u)) t := by fun_prop
    have hval : deriv (fun x => Real.exp (x * u)) t
        = Real.exp (t * u) * u := by simp
    rw [← hval]
    exact h.hasDerivAt
  have hd2 : ∀ t, HasDerivAt (fun x => 1 + x * u) u t := by
    intro t
    have h : DifferentiableAt ℝ (fun x => 1 + x * u) t := by fun_prop
    have hval : deriv (fun x => 1 + x * u) t = u := by simp
    exact h.hasDerivAt.congr_deriv hval
  have hd3 : ∀ t, HasDerivAt (fun x => x ^ 2 * (u ^ 2 / 2 * Real.exp |u|))
      (2 * t * (u ^ 2 / 2 * Real.exp |u|)) t := by
    intro t
    have h : DifferentiableAt ℝ (fun x => x ^ 2 * (u ^ 2 / 2 * Real.exp |u|)) t :=
      by fun_prop
    have hval : deriv (fun x => x ^ 2 * (u ^ 2 / 2 * Real.exp |u|)) t
        = 2 * t * (u ^ 2 / 2 * Real.exp |u|) := by simp
    rw [← hval]
    exact h.hasDerivAt
  have hd1' : ∀ t, HasDerivAt (fun x => Real.exp (x * u) * u)
      (Real.exp (t * u) * u * u) t := by
    intro t
    have h : DifferentiableAt ℝ (fun x => Real.exp (x * u) * u) t := by fun_prop
    have hval : deriv (fun x => Real.exp (x * u) * u) t
        = Real.exp (t * u) * u * u := by simp
    rw [← hval]
    exact h.hasDerivAt
  have hd2' : ∀ t, HasDerivAt
      (fun x => u + 2 * x * (u ^ 2 / 2 * Real.exp |u|))
      (2 * (u ^ 2 / 2 * Real.exp |u|)) t := by
    intro t
    have h : DifferentiableAt ℝ
        (fun x => u + 2 * x * (u ^ 2 / 2 * Real.exp |u|)) t := by fun_prop
    have hval : deriv (fun x => u + 2 * x * (u ^ 2 / 2 * Real.exp |u|)) t
        = 2 * (u ^ 2 / 2 * Real.exp |u|) := by simp
    rw [← hval]
    exact h.hasDerivAt
  have hds : ∀ t, HasDerivAt
      (fun x => Real.exp (x * u) - (1 + x * u)
        - x ^ 2 * (u ^ 2 / 2 * Real.exp |u|))
      (Real.exp (t * u) * u - u - 2 * t * (u ^ 2 / 2 * Real.exp |u|)) t :=
    fun t => ((hd1 t).sub (hd2 t)).sub (hd3 t)
  have hdsd : ∀ t, HasDerivAt
      (fun x => Real.exp (x * u) * u - u - 2 * x * (u ^ 2 / 2 * Real.exp |u|))
      (Real.exp (t * u) * u * u - 2 * (u ^ 2 / 2 * Real.exp |u|)) t := by
    intro t
    refine ((hd1' t).sub (hd2' t)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun x => by
      show Real.exp (x * u) * u - u - 2 * x * (u ^ 2 / 2 * Real.exp |u|)
        = (fun y => Real.exp (y * u) * u
            - (u + 2 * y * (u ^ 2 / 2 * Real.exp |u|))) x
      ring)
  -- знак второй "производной": e^{tu} ≤ e^{|u|} при t ∈ [0,1]
  have hsdd_le : ∀ t, 0 ≤ t → t ≤ 1 →
      Real.exp (t * u) * u * u - 2 * (u ^ 2 / 2 * Real.exp |u|) ≤ 0 := by
    intro t ht0 ht1
    have htu : t * u ≤ |u| := by
      have h1 : t * u ≤ t * |u| :=
        mul_le_mul_of_nonneg_left (le_abs_self u) ht0
      have h2 : t * |u| ≤ 1 * |u| :=
        mul_le_mul_of_nonneg_right ht1 (abs_nonneg u)
      linarith
    have hexp : Real.exp (t * u) ≤ Real.exp |u| :=
      Real.exp_le_exp.mpr htu
    nlinarith [hexp, sq_nonneg u, Real.exp_pos (t * u)]
  -- внутренний MVT: sd не возрастает на [0, c], c > 0
  have sd_mono : ∀ c, 0 < c → c ≤ 1 →
      Real.exp (c * u) * u - u - 2 * c * (u ^ 2 / 2 * Real.exp |u|)
        ≤ Real.exp (0 * u) * u - u - 2 * 0 * (u ^ 2 / 2 * Real.exp |u|) := by
    intro c hc0 hc1
    have hcont : ContinuousOn
        (fun t => Real.exp (t * u) * u - u - 2 * t * (u ^ 2 / 2 * Real.exp |u|))
        (Set.Icc (0:ℝ) c) := fun x _ =>
      (hdsd x).continuousAt.continuousWithinAt
    have h0c : (0:ℝ) < c := hc0
    obtain ⟨ξ, hξmem, hslope⟩ :=
      exists_hasDerivAt_eq_slope
        (fun t => Real.exp (t * u) * u - u - 2 * t * (u ^ 2 / 2 * Real.exp |u|))
        (fun t => Real.exp (t * u) * u * u - 2 * (u ^ 2 / 2 * Real.exp |u|))
        h0c hcont (fun x _ => hdsd x)
    have hξ := hsdd_le ξ (by linarith [hξmem.1]) (by linarith [hξmem.2, hc1])
    have hkey : Real.exp (c * u) * u - u - 2 * c * (u ^ 2 / 2 * Real.exp |u|)
        - (Real.exp (0 * u) * u - u - 2 * 0 * (u ^ 2 / 2 * Real.exp |u|))
        = (Real.exp (ξ * u) * u * u - 2 * (u ^ 2 / 2 * Real.exp |u|)) * c := by
      have := (eq_div_iff (by linarith : (c:ℝ) - 0 ≠ 0)).mp hslope
      linarith [this]
    have hpos : (0:ℝ) ≤ c := hc0.le
    have hzero : Real.exp (0 * u) * u - u - 2 * 0 * (u ^ 2 / 2 * Real.exp |u|)
        = 0 := by
      simp
    rw [hzero] at hkey ⊢
    nlinarith
  -- sd 0 = 0
  have sd0 : Real.exp (0 * u) * u - u - 2 * 0 * (u ^ 2 / 2 * Real.exp |u|) = 0 := by
    simp
  -- внешний MVT на [0, 1]
  have hconts : ContinuousOn
      (fun t => Real.exp (t * u) - (1 + t * u)
        - t ^ 2 * (u ^ 2 / 2 * Real.exp |u|))
      (Set.Icc (0:ℝ) 1) := fun x _ =>
    (hds x).continuousAt.continuousWithinAt
  have h01 : (0:ℝ) < 1 := by norm_num
  obtain ⟨η, hηmem, hslope2⟩ :=
    exists_hasDerivAt_eq_slope
      (fun t => Real.exp (t * u) - (1 + t * u)
        - t ^ 2 * (u ^ 2 / 2 * Real.exp |u|))
      (fun t => Real.exp (t * u) * u - u - 2 * t * (u ^ 2 / 2 * Real.exp |u|))
      h01 hconts (fun x _ => hds x)
  have hsdη : Real.exp (η * u) * u - u - 2 * η * (u ^ 2 / 2 * Real.exp |u|) ≤ 0 := by
    have hmono := sd_mono η (by linarith [hηmem.1]) (by linarith [hηmem.2])
    linarith [hmono, sd0]
  -- s(0) = 0
  have hs0 : Real.exp (0 * u) - (1 + 0 * u)
      - 0 ^ 2 * (u ^ 2 / 2 * Real.exp |u|) = 0 := by
    simp
  -- финал: s(1) = s(0) + sd η · 1 ≤ 0
  have hkey2 : Real.exp (1 * u) - (1 + 1 * u)
      - 1 ^ 2 * (u ^ 2 / 2 * Real.exp |u|)
        = (Real.exp (η * u) * u - u - 2 * η * (u ^ 2 / 2 * Real.exp |u|))
          * (1 - 0) + (Real.exp (0 * u) - (1 + 0 * u)
      - 0 ^ 2 * (u ^ 2 / 2 * Real.exp |u|)) := by
    have := (eq_div_iff (by norm_num : (1:ℝ) - 0 ≠ 0)).mp hslope2
    linarith [this]
  have hone : (1:ℝ) * u = u := by ring
  have hone2 : (1:ℝ) ^ 2 = 1 := by ring
  have hfin : Real.exp u - (1 + u) - (u ^ 2 / 2 * Real.exp |u|) ≤ 0 := by
    rw [hone, hone2, show (1:ℝ) - 0 = 1 from by ring, hs0] at hkey2
    have hm : (Real.exp (η * u) * u - u - 2 * η * (u ^ 2 / 2 * Real.exp |u|))
        * (1:ℝ) ≤ 0 := by
      simp only [mul_one]
      exact hsdη
    linarith
  linarith

/-! ## Условная лемма Бернштейна -/

/-- **Условная лемма Бернштейна/Freedman**: при условном
среднем-ноль (Σ q·X = 0), диапазоне |X| ≤ b и условной
дисперсии Σ q·X² ≤ σ² mgf шага ограничен
exp((λ²σ²/2)·e^{λb}) — дисперсиона вместо диапазона c²
(ср. `hoeffding_lemma_prefix`: exp(λ²c²/2)). -/
theorem freedman_lemma_prefix (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : V → ℝ) (b : ℝ) (hb : ∀ v, |X v| ≤ b)
    (hmean : ∑ v, q v * X v = 0)
    (sig : ℝ) (hsig : 0 ≤ sig)
    (hvar : ∑ v, q v * (X v) ^ 2 ≤ sig)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ v, q v * Real.exp (lam * X v)
      ≤ Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2) := by
  -- поглощение хвоста: e^{λX} ≤ 1 + λX + (λ²X²/2)e^{λb}
  have habs : ∀ v, |lam * X v| ≤ lam * b := by
    intro v
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left (hb v) hlam
  have h2 : ∀ v, Real.exp (lam * X v)
      ≤ 1 + lam * X v
        + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp (lam * b) := by
    intro v
    have h1 := exp_tail_two (lam * X v)
    have he : Real.exp |lam * X v| ≤ Real.exp (lam * b) :=
      Real.exp_le_exp.mpr (habs v)
    have hpow : (lam * X v) ^ 2 = lam ^ 2 * (X v) ^ 2 := by ring
    rw [hpow] at h1
    calc Real.exp (lam * X v)
        ≤ 1 + lam * X v + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp |lam * X v| :=
          h1
      _ ≤ 1 + lam * X v
          + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp (lam * b) := by
          have hsx : (0:ℝ) ≤ lam ^ 2 * (X v) ^ 2 / 2 := by positivity
          gcongr
  -- взвешенная сумма
  have hsum : ∑ v, q v * Real.exp (lam * X v)
      ≤ ∑ v, q v * (1 + lam * X v
        + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp (lam * b)) :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h2 v) (hq0 v)
  -- раскрытие: веса, среднее-ноль, дисперсия
  have hopen : ∑ v, q v * (1 + lam * X v
        + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp (lam * b))
      = 1 + (lam ^ 2 * Real.exp (lam * b) / 2)
          * ∑ v, q v * (X v) ^ 2 := by
    have hsplit : ∀ v, q v * (1 + lam * X v
          + (lam ^ 2 * (X v) ^ 2 / 2) * Real.exp (lam * b))
        = q v + lam * (q v * X v)
          + (lam ^ 2 * Real.exp (lam * b) / 2) * (q v * (X v) ^ 2) := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq1, hmean]
    ring
  rw [hopen] at hsum
  -- сжатие дисперсии и финал через add_one_le_exp
  have hcoef : (0:ℝ) ≤ lam ^ 2 * Real.exp (lam * b) / 2 := by positivity
  have hvar' : (lam ^ 2 * Real.exp (lam * b) / 2) * ∑ v, q v * (X v) ^ 2
      ≤ (lam ^ 2 * Real.exp (lam * b) / 2) * sig :=
    mul_le_mul_of_nonneg_left hvar hcoef
  have hfin := Real.add_one_le_exp
    ((lam ^ 2 * Real.exp (lam * b) / 2) * sig)
  rw [show lam ^ 2 * sig * Real.exp (lam * b) / 2
      = (lam ^ 2 * Real.exp (lam * b) / 2) * sig from by ring]
  linarith

/-! ## Мартингальный mgf -/

/-- **Мартингальный mgf (Freedman)**: при условно
центрированных приращениях (|X| ≤ b, E[X_{t+1}|π] = 0,
E[X_{t+1}²|π] ≤ σ² при каждом префиксе) mgf суммы ограничен
exp(n·λ²σ²e^{λb}/2). Дисперсиона σ² вместо диапазона c²
в `azuma_mgf`. -/
theorem freedman_mgf (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ) (b : ℝ)
    (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 ≤ sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    prodE (fun _ => q) (fun ω => Real.exp (lam * azumaSum X n ω))
      ≤ Real.exp (n * (lam ^ 2 * sig * Real.exp (lam * b) / 2)) := by
  induction n with
  | zero => simp [azumaSum, prodE, prodDens]
  | succ n ih =>
      rw [prodE_snoc]
      -- внутренняя сумма по свежей координате: условная лемма
      have hinner : ∀ pref : Fin n → V,
          ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
            (Fin.snoc (α := fun _ => V) pref v))
            ≤ Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2) := by
        intro pref
        have hmul : ∀ v, Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            = Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam * X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v)) := by
          intro v
          rw [azumaSum_snoc, ← Real.exp_add]
          ring
        have hsub : ∑ v, q v * Real.exp
            (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v))
            ≤ Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2) :=
          freedman_lemma_prefix q hq0 hq1
            (fun v => X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) b
            (fun v => hbnd (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            (hmean n pref) sig hsig (hvar n pref) lam hlam
        calc ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            = ∑ v, q v * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam * X (n + 1)
                  (Fin.snoc (α := fun _ => V) pref v))) := by
              refine Finset.sum_congr rfl ?_
              intro v _
              rw [hmul v]
          _ = Real.exp (lam * azumaSum X n pref)
              * ∑ v, q v * Real.exp
                  (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v)) := by
              have hswap : ∑ v, q v * (Real.exp (lam * azumaSum X n pref)
                  * Real.exp (lam * X (n + 1)
                    (Fin.snoc (α := fun _ => V) pref v)))
                = ∑ v, Real.exp (lam * azumaSum X n pref)
                  * (q v * Real.exp
                    (lam * X (n + 1) (Fin.snoc (α := fun _ => V) pref v))) :=
                Finset.sum_congr rfl fun v _ => by ring
              rw [hswap, Finset.mul_sum]
          _ ≤ Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2) :=
              mul_le_mul_of_nonneg_left hsub (by positivity)
      -- сжатие
      have houter : ∑ pref : Fin n → V,
          (∏ i, q (pref i))
          * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
            (Fin.snoc (α := fun _ => V) pref v))
          ≤ Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)
            * prodE (fun _ => q)
              (fun ω => Real.exp (lam * azumaSum X n ω)) := by
        have h1 : ∀ pref : Fin n → V,
            (∏ i, q (pref i))
            * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
              (Fin.snoc (α := fun _ => V) pref v))
            ≤ (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)) :=
          fun pref => mul_le_mul_of_nonneg_left (hinner pref)
            (Finset.prod_nonneg fun i _ => hq0 (pref i))
        have h2 : ∑ pref : Fin n → V,
            (∏ i, q (pref i))
            * (Real.exp (lam * azumaSum X n pref)
              * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2))
            = Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)
              * prodE (fun _ => q)
                (fun ω => Real.exp (lam * azumaSum X n ω)) := by
          unfold prodE prodDens
          have hstep : ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2))
            = ∑ pref : Fin n → V,
                Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)
                * ((∏ i, q (pref i))
                  * Real.exp (lam * azumaSum X n pref)) :=
              Finset.sum_congr rfl fun pref _ => by ring
          rw [hstep, Finset.mul_sum]
        calc ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * ∑ v, q v * Real.exp (lam * azumaSum X (n + 1)
                (Fin.snoc (α := fun _ => V) pref v))
            ≤ ∑ pref : Fin n → V,
              (∏ i, q (pref i))
              * (Real.exp (lam * azumaSum X n pref)
                * Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)) :=
              Finset.sum_le_sum fun pref _ => h1 pref
          _ = Real.exp (lam ^ 2 * sig * Real.exp (lam * b) / 2)
              * prodE (fun _ => q)
                (fun ω => Real.exp (lam * azumaSum X n ω)) := h2
      refine le_trans houter ?_
      refine le_trans (mul_le_mul_of_nonneg_left ih
        (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, Real.exp_le_exp]
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast]
      linarith

/-! ## Freedman-хвост -/

/-- **Хвост Freedman (нижний)**: для условно центрированных
приращений с диапазоном b и условной дисперсией σ²

  P[ΣX ≤ −Δ] ≤ exp(−Δ²/(2(nσ² + bΔ)))

— оптимизация λ = Δ/(nσ²+bΔ), e^{λb} ≤ 1/(1−λb). При
σ² = b² = 1 не слабее хвоста Азумы exp(−Δ²/(2(n+Δ)))... -/
theorem freedman_tail_low (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    prodPq (fun _ => q)
      (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ))) := by
  classical
  set den : ℝ := (n : ℝ) * sig + b * Δ with hden
  set lam : ℝ := Δ / den with hlam
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdenpos : 0 < den := by
    have := hn'
    have := hsig
    have := hΔ
    unfold den
    positivity
  -- λ ≥ 0 и λb < 1
  have hlamage : 0 ≤ lam := div_nonneg hΔ.le hdenpos.le
  -- mgf для (−X)
  have hmgf : prodE (fun _ => q)
      (fun ω => Real.exp (lam * (- azumaSum X n ω)))
      ≤ Real.exp (n * (lam ^ 2 * sig * Real.exp (lam * b) / 2)) := by
    have hrw : (fun ω => Real.exp (lam * (- azumaSum X n ω)))
        = (fun ω => Real.exp (lam
          * azumaSum (fun t pref => - X t pref) n ω)) :=
      funext fun ω => by rw [azumaSum_neg X n ω]
    rw [hrw]
    refine freedman_mgf q hq0 hq1 (fun t pref => -X t pref) b
      (fun t pref => by
        rw [abs_neg]
        exact hbnd t pref)
      sig hsig.le
      (fun t pref => by
        have h0 := hmean t pref
        have hneg : ∑ v, q v * (- X (t + 1) (Fin.snoc pref v))
            = - ∑ v, q v * X (t + 1) (Fin.snoc pref v) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
        rw [hneg, h0]
        ring)
      (fun t pref => by
        have h0 := hvar t pref
        have hsq : ∀ v, q v * (- X (t + 1) (Fin.snoc pref v)) ^ 2
            = q v * (X (t + 1) (Fin.snoc pref v)) ^ 2 := by
          intro v
          rw [neg_sq]
        rw [Finset.sum_congr rfl (fun v _ => hsq v)]
        exact h0)
      lam hlamage n
  -- сопряжение: e^{λb} ≤ den / (n σ²)
  have hlam_b : lam * b < 1 := by
    unfold lam
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenpos]
    nlinarith [hn', hsig]
  have hone : 1 - lam * b ≤ Real.exp (-(lam * b)) := by
    have h := Real.add_one_le_exp (-(lam * b))
    linarith
  have hexpb : Real.exp (lam * b) ≤ den / ((n : ℝ) * sig) := by
    have hd : den ≠ 0 := ne_of_gt hdenpos
    have hsub : 1 - lam * b = ((n : ℝ) * sig) / den := by
      rw [eq_div_iff hd]
      unfold lam
      field_simp
      rw [hden]
      ring
    have h1 : Real.exp (lam * b) * (((n : ℝ) * sig) / den) ≤ 1 := by
      have hpos : (0:ℝ) < Real.exp (lam * b) := Real.exp_pos _
      have hmul : Real.exp (lam * b) * Real.exp (-(lam * b)) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hsub] at hone
      have h2 : Real.exp (lam * b) * (((n : ℝ) * sig) / den)
          ≤ Real.exp (lam * b) * Real.exp (-(lam * b)) :=
        mul_le_mul_of_nonneg_left hone hpos.le
      rwa [hmul] at h2
    have hnsig : (0:ℝ) < (n : ℝ) * sig := by positivity
    rw [le_div_iff₀ hnsig]
    have hA : Real.exp (lam * b) * ((n : ℝ) * sig) ≤ den := by
      have hconv : Real.exp (lam * b) * (((n : ℝ) * sig) / den)
          = (Real.exp (lam * b) * ((n : ℝ) * sig)) / den := by ring
      rw [hconv] at h1
      exact (div_le_one hdenpos).mp h1
    exact hA
  -- мажорация mgf-экспоненты: nλ²σ²e^{λb}/2 ≤ Δ²/(2·den)
  have hmgfexp : n * (lam ^ 2 * sig * Real.exp (lam * b) / 2)
      ≤ Δ ^ 2 / (2 * den) := by
    have hnsig : (0:ℝ) < (n : ℝ) * sig := by positivity
    have hsplit : lam ^ 2 = Δ ^ 2 / den ^ 2 := by
      unfold lam
      rw [div_pow]
    rw [hsplit]
    have hpos : (0:ℝ) ≤ (Δ ^ 2 / den ^ 2) * sig / 2 := by positivity
    calc ((n : ℝ)) * ((Δ ^ 2 / den ^ 2) * sig * Real.exp (lam * b) / 2)
        ≤ ((n : ℝ))
            * ((Δ ^ 2 / den ^ 2) * sig * (den / ((n : ℝ) * sig)) / 2) := by
          gcongr
      _ = Δ ^ 2 / (2 * den) := by
          have hd0 : den ≠ 0 := ne_of_gt hdenpos
          have hn0 : ((n : ℝ)) ≠ 0 := by positivity
          have hs0 : sig ≠ 0 := ne_of_gt hsig
          field_simp
  -- Markov на событии {ΣX ≤ −Δ}
  have hisprob : IsProbSys (fun _ : Fin n => q) :=
    fun _ => ⟨hq0, hq1⟩
  have hmarkov : Real.exp (lam * Δ)
      * prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ prodE (fun _ => q)
        (fun ω => Real.exp (lam * (- azumaSum X n ω))) := by
    refine markov_ge (fun _ => q) hisprob
      (fun ω => Real.exp (lam * (- azumaSum X n ω)))
      (fun ω => (Real.exp_pos _).le) _
      (fun ω => azumaSum X n ω ≤ -Δ)
      (fun ω hω => ?_)
    apply Real.exp_le_exp.mpr
    have hkey : Δ ≤ - azumaSum X n ω := by
      have : azumaSum X n ω ≤ -Δ := hω
      linarith
    calc lam * Δ ≤ lam * (- azumaSum X n ω) :=
          mul_le_mul_of_nonneg_left hkey hlamage
      _ = lam * (- azumaSum X n ω) := rfl
  -- сведение
  have hfinal : prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ))) := by
    have h1 : Real.exp (lam * Δ)
        * prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (n * (lam ^ 2 * sig * Real.exp (lam * b) / 2)) :=
        le_trans hmarkov hmgf
    have hexp : (0:ℝ) < Real.exp (lam * Δ) := Real.exp_pos _
    have h2 : prodPq (fun _ => q) (fun ω => azumaSum X n ω ≤ -Δ)
      ≤ Real.exp (n * (lam ^ 2 * sig * Real.exp (lam * b) / 2))
        / Real.exp (lam * Δ) := by
      rw [le_div_iff₀ hexp]
      nlinarith [h1]
    refine le_trans h2 ?_
    rw [← Real.exp_sub]
    have hlamΔ : lam * Δ = Δ ^ 2 / den := by
      unfold lam
      field_simp
    have hdelta : Δ ^ 2 / (2 * den) - Δ ^ 2 / den
        = - Δ ^ 2 / (2 * den) := by
      field_simp
      ring
    -- монотонность exp: mgf-показатель − λΔ ≤ −Δ²/(2·den)
    refine Real.exp_le_exp.mpr ?_
    have hsub : n * (lam ^ 2 * sig * Real.exp (lam * b) / 2) - lam * Δ
        = (n * (lam ^ 2 * sig * Real.exp (lam * b) / 2) - Δ ^ 2 / (2 * den))
          + (Δ ^ 2 / (2 * den) - Δ ^ 2 / den) := by
      rw [hlamΔ]
      ring
    rw [hsub, hdelta]
    linarith
  exact hfinal

/-! ## Дисперсионное усиление успехов -/

/-- **Дисперсионная декомпозиция**: условная дисперсия центрированных
успехов Z = S − m не превосходит второго момента: Σ q (S−m)² =
Σ q S² − m² ≤ Σ q S². -/
theorem cond_var_le_second (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (S : V → ℝ) :
    ∑ v, q v * (S v - ∑ u, q u * S u) ^ 2
      ≤ ∑ v, q v * (S v) ^ 2 := by
  set m : ℝ := ∑ u, q u * S u with hm
  have h1 : ∀ v, q v * (S v - m) ^ 2
      = q v * (S v) ^ 2 - 2 * m * (q v * S v) + q v * m ^ 2 := by
    intro v
    ring
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have h2 : ∑ v, 2 * m * (q v * S v) = 2 * m * m := by
    rw [hm, ← Finset.mul_sum]
  have h3 : ∑ v, q v * m ^ 2 = m ^ 2 := by
    have hrw : ∀ v, q v * m ^ 2 = m ^ 2 * q v := fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => hrw v), ← Finset.mul_sum, hq1,
      mul_one]
  linarith [sq_nonneg m]

/-- **История-зависимые успехи, Freedman-усиление**: успехи
S_{t+1} ∈ [0,1] с условными полами p₀ и измеренной условной
дисперсией σ² (Σ q·S² ≤ σ² при каждом префиксе — runtime-посылка;
σ² = 1 — грубая [0,1]-оценка):

  azumaSum S n ≥ n·p₀ − Δ  w.p.  ≥ 1 − exp(−Δ²/(2(nσ² + Δ)))

При σ² < 1 хвост СИЛЬНЕЕ азумовского exp(−Δ²/(2n));
при σ² = 1 — не слабее. -/
theorem adaptive_success_freedman (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (S : ∀ t, (Fin t → V) → ℝ)
    (hS : ∀ t pref, 0 ≤ S t pref ∧ S t pref ≤ 1)
    (p0 : ℝ)
    (hfloor : ∀ t pref,
      p0 ≤ ∑ v, q v * S (t + 1) (Fin.snoc pref v))
    (sig : ℝ) (hsig : 0 < sig)
    (h_emp_var : ∀ t pref,
      ∑ v, q v * (S (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n) (Δ : ℝ) (hΔ : 0 < Δ) :
    1 - Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + Δ)))
      ≤ prodPq (fun _ => q)
        (fun ω => n * p0 - Δ ≤ azumaSum S n ω) := by
  classical
  -- центрированные приращения (как в adaptive_success_azuma)
  set m : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    ∑ v, q v * S (t + 1) (Fin.snoc (α := fun _ => V) pref v) with hmdef
  set Z : ∀ t, (Fin t → V) → ℝ := fun t pref =>
    match t with
    | 0 => 0
    | t + 1 => S (t + 1) pref
        - m t (Fin.init (α := fun _ => V) pref) with hZdef
  have hm01 : ∀ t pref, 0 ≤ m t pref ∧ m t pref ≤ 1 := by
    intro t pref
    constructor
    · exact Finset.sum_nonneg fun v _ =>
        mul_nonneg (hq0 v) (hS (t + 1) _).1
    · have hle : m t pref ≤ ∑ v, q v * (1 : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hS (t + 1) _).2 (hq0 v)
      rw [hmdef] at hle
      have hrw : ∑ v, q v * (1 : ℝ) = 1 := by
        simp [hq1]
      rw [hrw] at hle
      exact hle
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
      ∑ v, q v * Z (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0 := by
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
    have hsplit2 : ∑ v, q v * (S (t + 1) (Fin.snoc pref v)
          - m t pref)
        = ∑ v, q v * S (t + 1) (Fin.snoc pref v)
          - ∑ v, q v * (m t pref) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hsplit2]
    have hfirst : ∑ v, q v * S (t + 1) (Fin.snoc pref v)
        = m t pref := by simp only [hmdef]
    have hsecond : ∑ v, q v * m t pref = m t pref := by
      rw [← Finset.sum_mul, hq1]
      simp
    rw [hfirst, hsecond]
    ring
  -- условная дисперсия Z: Σ q Z² ≤ Σ q S² ≤ sig
  have hvarZ : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * (Z (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig := by
    intro t pref
    have hZterm : ∀ v, Z (t + 1) (Fin.snoc (α := fun _ => V) pref v)
        = S (t + 1) (Fin.snoc (α := fun _ => V) pref v) - m t pref := by
      intro v
      simp only [hZdef]
      simpa using congrArg (fun π => S (t + 1) π - m t (Fin.init (α := fun _ => V) π))
        (Fin.init_snoc pref v)
    rw [Finset.sum_congr rfl (fun v _ => by rw [hZterm v])]
    have hle := cond_var_le_second q hq0 hq1
      (fun v => S (t + 1) (Fin.snoc (α := fun _ => V) pref v))
    have hrw : ∑ u, q u * S (t + 1) (Fin.snoc (α := fun _ => V) pref u)
        = m t pref := by simp only [hmdef]
    rw [hrw] at hle
    exact le_trans hle (h_emp_var t pref)
  -- Freedman-хвост для Z с b = 1
  have hisprob : IsProbSys (fun _ : Fin n => q) :=
    fun _ => ⟨hq0, hq1⟩
  have htail := freedman_tail_low q hq0 hq1 Z 1 (by norm_num)
    hZbnd sig hsig hmeanZ hvarZ n hn Δ hΔ
  rw [one_mul] at htail
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
  have hmono : prodPq (fun _ => q)
      (fun ω => azumaSum S n ω < n * p0 - Δ)
      ≤ Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + Δ))) := by
    refine le_trans (prodPq_mono (fun _ => q) hisprob _ _
      (fun ω hω => ?_)) htail
    rw [hsplit]
    have h1 := hmlower ω
    linarith
  have hcompl : prodPq (fun _ => q)
      (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ))
      = 1 - prodPq (fun _ => q)
        (fun ω => azumaSum S n ω < n * p0 - Δ) :=
    prodPq_compl (fun _ => q) hisprob _
  calc (1:ℝ) - Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + Δ)))
      ≤ 1 - prodPq (fun _ => q)
        (fun ω => azumaSum S n ω < n * p0 - Δ) := by
          linarith [hmono]
    _ = prodPq (fun _ => q)
        (fun ω => ¬ (azumaSum S n ω < n * p0 - Δ)) := hcompl.symm
    _ ≤ prodPq (fun _ => q)
        (fun ω => n * p0 - Δ ≤ azumaSum S n ω) :=
          prodPq_mono (fun _ => q) hisprob _ _
            (fun ω hω => not_lt.mp hω)

/-- МОСТ ФРИДМАНА ⇒ ПОСЫЛКИ: если выполнение
эмпирической посылки A потраекторно эквивалентно тому, что
сумма ограниченных мартингал-разностей не провалилась ниже
−Δ, то A выполняется с вероятностью ≥ 1 − exp(−Δ²/(2(nσ+bΔ)))
— anytime-валидная уверенность в эмпирических посылках
h_emp-блока. -/
theorem freedman_confidence {V : Type} [Fintype V] [Nonempty V]
    (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n) (Δ : ℝ) (hΔ : 0 < Δ)
    (A : (Fin n → V) → Prop) [DecidablePred A]
    (hA : ∀ ω, A ω ↔ ¬ (azumaSum X n ω ≤ -Δ)) :
    1 - Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ)))
      ≤ prodPq (V := V) (fun _ : Fin n => q) A := by
  have htail := freedman_tail_low q hq0 hq1 X b hb hbnd sig hsig
    hmean hvar n hn Δ hΔ
  have hisprob : IsProbSys (fun _ : Fin n => q) := fun _ => ⟨hq0, hq1⟩
  have hcompl : prodPq (fun _ : Fin n => q)
      (fun ω => ¬ (azumaSum X n ω ≤ -Δ))
      = 1 - prodPq (fun _ : Fin n => q)
          (fun ω => azumaSum X n ω ≤ -Δ) :=
    prodPq_compl (fun _ : Fin n => q) hisprob _
  have hmono : prodPq (fun _ : Fin n => q)
      (fun ω => ¬ (azumaSum X n ω ≤ -Δ))
      ≤ prodPq (V := V) (fun _ : Fin n => q) A :=
    prodPq_mono (fun _ : Fin n => q) hisprob _ _
      (fun ω h => (hA ω).mpr h)
  rw [hcompl] at hmono
  linarith

end Hagi.Probability
/-!
# PmfMean — finite PMF expectations

Ported verbatim (proofs unchanged) from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean into Hagi vocabulary. The
finite-expectation kernel for the Markov-chain Freedman
inequality (MarkovFreedman): pmfMean and its algebra
(add/sub/mono/sq/Markov/bind/map/uniform), 0 sorry in the
source, 0 here.
-/

namespace Hagi.Probability

open Filter
open scoped BigOperators Topology

noncomputable def pmfMean {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_const_mul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  simpa only [mul_comm] using pmfMean_mul_const p f c

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_sq_sub {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => (f a - c) ^ 2) =
      pmfMean p (fun a => f a ^ 2) - 2 * c * pmfMean p f + c ^ 2 := by
  have hpoly : (fun a => (f a - c) ^ 2) =
      (fun a => (f a ^ 2 - (2 * c) * f a) + c ^ 2) := by
    funext a
    ring
  rw [hpoly, pmfMean_add, pmfMean_sub, pmfMean_const_mul, pmfMean_const]

theorem pmfMean_sq_le {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    (pmfMean p f) ^ 2 ≤ pmfMean p (fun a => f a ^ 2) := by
  have h := pmfMean_nonneg p
    (fun a (_ : a ∈ p.support) => sq_nonneg (f a - pmfMean p f))
  rw [pmfMean_sq_sub] at h
  nlinarith

theorem pmfMean_markov_sq {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    pmfMean p (fun a => if ε < |f a| then 1 else 0) ≤
      pmfMean p (fun a => f a ^ 2) / ε ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  rw [← pmfMean_mul_const]
  apply pmfMean_mono
  intro a _
  split_ifs with ha
  · simp only [one_mul]
    exact sq_le_sq.mpr (by rw [abs_of_pos hε]; exact le_of_lt ha)
  · simp only [zero_mul]
    exact sq_nonneg _

@[simp] theorem pmfMean_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfMean (PMF.pure a) f = f a := by
  classical
  simp [pmfMean, PMF.pure_apply, apply_ite]

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

namespace PMF
open scoped ENNReal Classical in
/-- PMF-valued uniform distribution on a nonempty finset.

Restored locally: Mathlib 4.35 turned `PMF.uniformOfFinset` into a
`Measure`-valued definition, but the PMF kernel below (and its apply
lemma) is still referenced by `pmfMean_uniformOfFinset`. -/
noncomputable def uniformOfFinset {α : Type*} [Fintype α] (s : Finset α) (_hs : s.Nonempty) :
    PMF α :=
  ⟨fun a => if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0, by
    classical
    have hcard : (s.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr _hs).ne'
    have hval : (∑ a, (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞))) = 1 := by
      have hzero : (∑ a ∈ sᶜ, (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞))) = 0 :=
        Finset.sum_eq_zero (fun a ha => by simp [Finset.mem_compl.mp ha])
      rw [← Finset.sum_add_sum_compl s, hzero, add_zero]
      refine Eq.trans (Finset.sum_congr rfl (fun a ha => by rw [if_pos ha])) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel hcard (by simp)
    have hsum := hasSum_fintype (fun a : α => (if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else (0:ℝ≥0∞)))
    rwa [hval] at hsum⟩

open scoped ENNReal Classical in
@[simp] theorem uniformOfFinset_apply {α : Type*} [Fintype α] {s : Finset α} {_hs : s.Nonempty} (a : α) :
    uniformOfFinset s _hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  show (uniformOfFinset s _hs).val a = _
  rfl

end PMF

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]


end Hagi.Probability

/-!
# MarkovFreedman — the full discrete time-inhomogeneous
Freedman inequality

Ported verbatim (proofs unchanged) from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.MarkovLaw. On a finite-state
time-inhomogeneous Markov chain (initial: PMF α, kernels
K: ℕ → α → PMF α) with a process X, a predictable variance
counter V and uniform step bound c:

* `pmfMean_exp_le` — the compensated MGF bound (the
  one-step core: negative-mean, variance-bounded steps);
* `markovMean_potential_le` — supermartingale propagation
  along the chain law;
* `markovMean_exp_compensated_le` — the exp potential is a
  supermartingale under the compensated conditions;
* `pmfMean_compensated_tail` — the single-time tail;
* `finite_freedman` — THE ANYTIME FORM:
  P[∃j≤k: X_j ≥ r ∧ V_j ≤ v] ≤ exp(−r²/(4(v + c·r))) —
  measured at the terminal law of the chain; the bound is
  time-uniform in the usual sense (any stopping time ≤ k
  by the same argument at that time).

0 sorry in the source, 0 here; axioms standard.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

theorem pmfMean_exp_le {α : Type*} [Fintype α] (p : PMF α)
    (X : α → ℝ) (c v lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ a ∈ p.support, |X a| ≤ c)
    (hmean : pmfMean p X ≤ 0) (hvar : pmfMean p (fun a => X a ^ 2) ≤ v) :
    pmfMean p (fun a => Real.exp (lam * X a)) ≤ Real.exp (lam ^ 2 * v) := by
  have hpt (a : α) (ha : a ∈ p.support) :
      Real.exp (lam * X a) ≤ 1 + lam * X a + lam ^ 2 * X a ^ 2 := by
    have hb : |lam * X a| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact (mul_le_mul_of_nonneg_left (hbounded a ha) hlam).trans hclam
    have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hb)).2
    nlinarith
  calc
    _ ≤ pmfMean p (fun a => (1 + lam * X a) + lam ^ 2 * X a ^ 2) :=
      pmfMean_mono p hpt
    _ = 1 + lam * pmfMean p X + lam ^ 2 * pmfMean p (fun a => X a ^ 2) := by
      rw [pmfMean_add, pmfMean_add, pmfMean_const, pmfMean_const_mul,
        pmfMean_const_mul]
    _ ≤ 1 + lam ^ 2 * v := by
      have hs := mul_le_mul_of_nonneg_left hmean hlam
      have hv := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (lam ^ 2 * v)

noncomputable def markovLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => initial
  | k + 1 => (markovLaw initial K k).bind (K k)

theorem markovMean_potential_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (Z : ℕ → α → ℝ)
    (hstep : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (Z (k + 1)) ≤ Z k a) (k : ℕ) :
    pmfMean (markovLaw initial K k) (Z k) ≤ pmfMean initial (Z 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [markovLaw, pmfMean_bind]
    exact (pmfMean_mono _ (hstep k)).trans ih

theorem markovMean_exp_compensated_le {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c lam : ℝ)
    (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) :
    pmfMean (markovLaw initial K k)
      (fun a => Real.exp (lam * X k a - lam ^ 2 * V k a)) ≤
      pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) := by
  apply markovMean_potential_le initial K
    (fun k a => Real.exp (lam * X k a - lam ^ 2 * V k a))
  intro j a ha
  have hmgf := pmfMean_exp_le (K j a) (fun b => X (j + 1) b - X j a)
    c (incrementVar j a) lam hlam hclam (hbounded j a ha) (hmean j a ha) (hvar j a ha)
  have heq : pmfMean (K j a) (fun b => Real.exp (lam * X (j + 1) b - lam ^ 2 * V (j + 1) b)) =
      Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        pmfMean (K j a) (fun b => Real.exp (lam * (X (j + 1) b - X j a))) := by
    rw [← pmfMean_const_mul]
    apply pmfMean_congr
    intro b hb
    rw [hcounter j a ha b hb, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (lam * X j a - lam ^ 2 * V j a - lam ^ 2 * incrementVar j a) *
        Real.exp (lam ^ 2 * incrementVar j a) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem pmfMean_compensated_tail {α : Type*} [Fintype α] (p : PMF α)
    (X V : α → ℝ) (lam r v : ℝ) (hlam : 0 ≤ lam)
    (hmgf : pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) ≤ 1) :
    pmfMean p (fun a => if r ≤ X a ∧ V a ≤ v then 1 else 0) ≤
      Real.exp (-lam * r + lam ^ 2 * v) := by
  classical
  have hevent (a : α) :
      (if r ≤ X a ∧ V a ≤ v then (1 : ℝ) else 0) ≤
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v) := by
    split_ifs with ha
    · rw [← Real.exp_add, Real.one_le_exp_iff]
      have hx := mul_le_mul_of_nonneg_left ha.1 hlam
      have hv := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg lam)
      linarith
    · positivity
  calc
    _ ≤ pmfMean p (fun a =>
        Real.exp (lam * X a - lam ^ 2 * V a) * Real.exp (-lam * r + lam ^ 2 * v)) :=
      pmfMean_mono p (fun a _ => hevent a)
    _ = pmfMean p (fun a => Real.exp (lam * X a - lam ^ 2 * V a)) *
        Real.exp (-lam * r + lam ^ 2 * v) := pmfMean_mul_const _ _ _
    _ ≤ 1 * Real.exp (-lam * r + lam ^ 2 * v) :=
      mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = _ := one_mul _

theorem finite_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α)
    (X V incrementVar : ℕ → α → ℝ) (c : ℝ) (hc : 0 < c)
    (hinitial : ∀ a ∈ initial.support, X 0 a ≤ 0 ∧ 0 ≤ V 0 a)
    (hbounded : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, |X (k + 1) b - X k a| ≤ c)
    (hmean : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => X (k + 1) b - X k a) ≤ 0)
    (hvar : ∀ k a, a ∈ (markovLaw initial K k).support →
      pmfMean (K k a) (fun b => (X (k + 1) b - X k a) ^ 2) ≤ incrementVar k a)
    (hcounter : ∀ k a, a ∈ (markovLaw initial K k).support →
      ∀ b ∈ (K k a).support, V (k + 1) b = V k a + incrementVar k a)
    (k : ℕ) (r v : ℝ) (hr : 0 < r) (hv : 0 ≤ v) :
    pmfMean (markovLaw initial K k)
      (fun a => if r ≤ X k a ∧ V k a ≤ v then 1 else 0) ≤
      Real.exp (-r ^ 2 / (4 * (v + c * r))) := by
  classical
  let A : ℝ := v + c * r
  have hA : 0 < A := by dsimp [A]; positivity
  let lam : ℝ := r / (2 * A)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hclam : lam * c ≤ 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_pos hc hr]
  have hmgf := markovMean_exp_compensated_le initial K X V incrementVar c lam hlam hclam
    hbounded hmean hvar hcounter k
  have hi : pmfMean initial (fun a => Real.exp (lam * X 0 a - lam ^ 2 * V 0 a)) ≤ 1 := by
    rw [← pmfMean_const initial 1]
    apply pmfMean_mono
    intro a ha
    apply Real.exp_le_one_iff.mpr
    obtain ⟨hx, hv⟩ := hinitial a ha
    have hx' := mul_le_mul_of_nonneg_left hx hlam
    have hv' := mul_nonneg (sq_nonneg lam) hv
    linarith
  have hhalf : lam * v ≤ r / 2 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).mpr
    dsimp [A]
    nlinarith [mul_nonneg hc.le (sq_nonneg r)]
  have hexponent : -lam * r + lam ^ 2 * v ≤ -r ^ 2 / (4 * (v + c * r)) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf hlam
    calc
      _ ≤ -lam * r / 2 := by nlinarith
      _ = _ := by
        dsimp [lam]
        change -(r / (2 * A)) * r / 2 = -r ^ 2 / (4 * A)
        field_simp
        ring
  exact (pmfMean_compensated_tail _ (X k) (V k) lam r v hlam (hmgf.trans hi)).trans
    (Real.exp_le_exp.mpr hexponent)


end

end Hagi.Probability
/-!
# HistoryPath — the path-space lift of a Markov chain


Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Process.History : History (path type), historyIndex,
historyInitial/historyKernel/historyLaw (the lifted chain on
paths), the marginal/invariant lemmas and the support
transport — the infrastructure for path-level additive
functionals (HistoryAdditive next).
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

abbrev History (α : Type*) (T : ℕ) := Fin (T + 1) → α

def historyIndex (T k : ℕ) : Fin (T + 1) := ⟨min k T,by omega⟩

@[simp] theorem historyIndex_val (T k : ℕ) : (historyIndex T k).val = min k T := rfl

noncomputable def historyInitial {α : Type*} (initial : PMF α) (T : ℕ) : PMF (History α T) :=
  initial.map (fun a => fun _ => a)

noncomputable def historyKernel {α : Type*} (K : ℕ → α → PMF α) (T k : ℕ)
    (ω : History α T) : PMF (History α T) :=
  if k < T then (K k (ω (historyIndex T k))).map
    (fun b => Function.update ω (historyIndex T (k + 1)) b) else PMF.pure ω

noncomputable def historyLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) : PMF (History α T) :=
  markovLaw (historyInitial initial T) (historyKernel K T) k

theorem historyIndex_ne_succ {T j k : ℕ} (hjk : j ≤ k) (hk : k < T) :
    historyIndex T j ≠ historyIndex T (k + 1) := by
  intro h
  have he := congrArg Fin.val h
  simp only [historyIndex_val] at he
  omega

theorem historyLaw_marginal {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) (hk : k ≤ T) :
    (historyLaw initial K T k).map (fun ω => ω (historyIndex T k)) =
      markovLaw initial K k := by
  induction k with
  | zero =>
    simp only [historyLaw,markovLaw,historyInitial,PMF.map_comp]
    change initial.map id = initial
    exact PMF.map_id initial
  | succ k ih =>
    have hkt : k < T := by omega
    have hkm : k ≤ T := by omega
    simp only [historyLaw,markovLaw,PMF.map_bind]
    have ih' := ih hkm
    change (historyLaw initial K T k).bind _ = (markovLaw initial K k).bind (K k)
    rw [← ih',PMF.bind_map]
    congr 1
    funext ω
    simp only [historyKernel,ite_eq_left hkt,PMF.map_comp,Function.comp_def,
      Function.update_self]
    exact PMF.map_id _

theorem historyLaw_invariant {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (P : α → Prop) (hinit : ∀ a ∈ initial.support, P a)
    (hstep : ∀ k a, P a → ∀ b ∈ (K k a).support, P b)
    (T k : ℕ) (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ∀ j, P (ω j) := by
  induction k generalizing ω with
  | zero =>
    obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact fun _ => hinit a ha
  | succ k ih =>
    obtain ⟨pI,hpI,hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    have hp := ih pI hpI
    by_cases hk : k < T
    · rw [historyKernel,ite_eq_left hk] at hω
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
      intro j
      by_cases hj : j = historyIndex T (k + 1)
      · subst j
        rw [Function.update_self]
        exact hstep k _ (hp _) b hb
      · rw [Function.update_of_ne hj]
        exact hp j
    · rw [historyKernel,ite_eq_right hk,PMF.mem_support_pure_iff] at hω
      subst ω
      exact hp

noncomputable def historyIncrement {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (ω : History α T) : ℝ :=
  f (j + 1) (ω (historyIndex T (j + 1))) -
    pmfMean (K j (ω (historyIndex T j))) (f (j + 1))

noncomputable def historyNoise {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), historyIncrement K f T j ω

noncomputable def historyCounter {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), v j (ω (historyIndex T j))

noncomputable def historyCounterRate {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  if k < T then v k (ω (historyIndex T k)) else 0

theorem historyNoise_update {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyNoise K f T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyNoise K f T k ω + f (k + 1) b -
        pmfMean (K k (ω (historyIndex T k))) (f (k + 1)) := by
  unfold historyNoise
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  have hp : (∑ j ∈ Finset.range k,
      historyIncrement K f T j (Function.update ω (historyIndex T (k + 1)) b)) =
      ∑ j ∈ Finset.range k, historyIncrement K f T j ω := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    simp only [historyIncrement,Function.update_of_ne (historyIndex_ne_succ (by omega : j + 1 ≤ k) hk),
      Function.update_of_ne (historyIndex_ne_succ hjk.le hk)]
  rw [hp]
  simp only [historyIncrement,Function.update_self,
    Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]
  ring

theorem historyCounter_update {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyCounter v T (k + 1) (Function.update ω (historyIndex T (k + 1)) b) =
      historyCounter v T k ω + v k (ω (historyIndex T k)) := by
  unfold historyCounter
  rw [Nat.min_eq_left (by omega : k + 1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (historyIndex_ne_succ (Finset.mem_range.mp hj).le hk)]
  · rw [Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] theorem historyNoise_zero {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T : ℕ) (ω : History α T) :
    historyNoise K f T 0 ω = 0 := by simp [historyNoise]

@[simp] theorem historyCounter_zero {α : Type*} (v : ℕ → α → ℝ)
    (T : ℕ) (ω : History α T) : historyCounter v T 0 ω = 0 := by simp [historyCounter]

theorem historyLaw_current_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T k) ∈ (markovLaw initial K k).support := by
  rw [← historyLaw_marginal initial K T k hk]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨ω,hω,rfl⟩

theorem historyNoise_frozen {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyNoise K f T (k + 1) ω = historyNoise K f T k ω := by
  simp only [historyNoise,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem historyCounter_frozen {α : Type*} (v : ℕ → α → ℝ) (T k : ℕ) (hk : T ≤ k)
    (ω : History α T) : historyCounter v T (k + 1) ω = historyCounter v T k ω := by
  simp only [historyCounter,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k + 1)]

theorem history_noise_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k + 1) b - pmfMean (K k a) (f (k + 1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k + 1) b - pmfMean (K k a) (f (k + 1))) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyNoise K f T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyNoise K f T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyNoise_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω pI hpI
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hpI
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hpI
      rw [historyNoise_update K f T j hj]
      have hb' := hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
      convert hb' using 1; congr 1; ring
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hpI
      subst pI
      rw [historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      rw [pmfMean_sub,pmfMean_const,sub_self]
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      have he (b : α) : historyNoise K f T (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b) - historyNoise K f T j ω =
          f (j + 1) b - pmfMean (K j (ω (historyIndex T j))) (f (j + 1)) := by
        rw [historyNoise_update K f T j hj]
        ring
      simp_rw [he]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyNoise_frozen K f T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ pI hpI
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hpI
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hpI
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hpI
      subst pI
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV


end

end Hagi.Probability
/-!
# HistoryPastMean — past-measurability and the union bound


Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Probability.
HistoryLawPastMean:
historyLaw_past_mean (past-measurable functions have
time-consistent laws), pmfMean_event_union (the finite
union bound for PMF expectations), pmfMean_finset_sum, and
the history_noise_freedman_maximal corollaries — the
prerequisites for the joint two-sided maximal Freedman.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

theorem historyLaw_past_mean {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T j k : ℕ) (hjk : j ≤ k)
    (f : History α T → ℝ)
    (hf : ∀ ω pI, (∀ i : Fin (T+1), i.val ≤ min j T → ω i = pI i) → f ω = f pI) :
    pmfMean (historyLaw initial K T k) f =
      pmfMean (historyLaw initial K T j) f := by
  classical
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | @succ k hjk ih =>
    change pmfMean ((historyLaw initial K T k).bind (historyKernel K T k)) f = _
    rw [pmfMean_bind]
    have he (ω : History α T) : pmfMean (historyKernel K T k ω) f = f ω := by
      by_cases hk : k < T
      · rw [historyKernel,ite_eq_left hk,pmfMean_map]
        have hu (b : α) : f (Function.update ω (historyIndex T (k+1)) b) = f ω := by
          apply hf
          intro i hi
          apply Function.update_of_ne
          intro hh
          have hval := congrArg Fin.val hh
          simp only [historyIndex,Nat.min_eq_left (by omega : k+1 ≤ T)] at hval
          have : i.val ≤ j := hi.trans (Nat.min_le_left _ _)
          omega
        simp_rw [hu]
        exact pmfMean_const _ _
      · rw [historyKernel,ite_eq_right hk,pmfMean_pure]
    simp_rw [he]
    exact ih

lemma historyNoise_past {α : Type*} [Fintype α] (K : ℕ → α → PMF α)
    (f : ℕ → α → ℝ) (T j : ℕ) (ω pI : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = pI i) :
    historyNoise K f T j ω = historyNoise K f T j pI := by
  unfold historyNoise
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  simp only [historyIncrement,h _ hsc,h _ hsn]

lemma historyCounter_past {α : Type*} (v : ℕ → α → ℝ)
    (T j : ℕ) (ω pI : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = pI i) :
    historyCounter v T j ω = historyCounter v T j pI := by
  unfold historyCounter
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  rw [h _ hsc]

lemma pmfMean_finset_sum {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (f : J → α → ℝ) :
    pmfMean p (fun a => ∑ j ∈ s, f j a) = ∑ j ∈ s, pmfMean p (f j) := by
  simp only [pmfMean,Finset.mul_sum]
  exact Finset.sum_comm

open Classical in

theorem pmfMean_event_union {α J : Type*} [Fintype α] (p : PMF α)
    (s : Finset J) (P : J → α → Prop) :
    pmfMean p (fun a => if ∃ j ∈ s, P j a then 1 else 0) ≤
      ∑ j ∈ s, pmfMean p (fun a => if P j a then 1 else 0) := by
  classical
  rw [← pmfMean_finset_sum]
  apply pmfMean_mono
  intro a _
  by_cases h : ∃ j ∈ s, P j a
  · obtain ⟨j,hj,hP⟩ := h
    rw [ite_eq_left ⟨j,hj,hP⟩]
    have hh := Finset.single_le_sum (f := fun j => (if P j a then (1 : ℝ) else 0))
      (fun _ _ => by positivity) hj
    simpa only [ite_eq_left hP] using hh
  · rw [ite_eq_right h]
    positivity

theorem history_noise_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (f v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |f (k+1) b - pmfMean (K k a) (f (k+1))| ≤ c)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b =>
        (f (k+1) b - pmfMean (K k a) (f (k+1)))^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyNoise K f T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyNoise K f T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω pI h
          rw [historyNoise_past K f T j ω pI h,historyCounter_past v T j ω pI h])]
        exact history_noise_freedman initial K f v T c hc hbounded hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl


end

end Hagi.Probability

/-!
# HistoryFreedman — the JOINT ANYTIME maximal Freedman on
paths

Ported verbatim from openai/math,
OAI.Combinatorics.TriangleRemoval.Process.HistoryAdditive:

* `historyAdditive` — additive path functionals
  Σⱼ g(state_j, state_{j+1}) over the first k steps;
* `history_additive_freedman` — the fixed-time tail on
  paths: P[S_k ≥ r, V_k ≤ V] ≤ exp(−r²/(4(V + c·r)));
* `history_additive_freedman_maximal` — THE JOINT ANYTIME
  FORM: P[∃ j ≤ T: S_j ≥ r ∧ V_j ≤ V] ≤ (T+1)·
  exp(−r²/(4(V + c·r))) — the union of the time-uniform
  tails over the horizon (the two-sided |S| form follows
  by applying to S and −S and doubling, 2(T+1)·exp(...)).

0 sorry in the source, 0 here; axioms standard.
-/

namespace Hagi.Probability

section
open scoped BigOperators Topology
open Filter

noncomputable def historyAdditive {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), g j (ω (historyIndex T j)) (ω (historyIndex T (j+1)))

lemma historyAdditive_update {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : k < T) (ω : History α T) (b : α) :
    historyAdditive g T (k+1) (Function.update ω (historyIndex T (k+1)) b) =
      historyAdditive g T k ω + g k (ω (historyIndex T k)) b := by
  unfold historyAdditive
  rw [Nat.min_eq_left (by omega : k+1 ≤ T),Nat.min_eq_left hk.le,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    rw [Function.update_of_ne (historyIndex_ne_succ hjk.le hk),
       Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hk)]
  · rw [Function.update_self,Function.update_of_ne (historyIndex_ne_succ le_rfl hk)]

@[simp] lemma historyAdditive_zero {α : Type*} (g : ℕ → α → α → ℝ)
    (T : ℕ) (ω : History α T) : historyAdditive g T 0 ω = 0 := by
  simp [historyAdditive]

lemma historyAdditive_frozen {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (hk : T ≤ k) (ω : History α T) :
    historyAdditive g T (k+1) ω = historyAdditive g T k ω := by
  simp only [historyAdditive,Nat.min_eq_right hk,Nat.min_eq_right (by omega : T ≤ k+1)]

theorem history_additive_freedman {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  apply finite_freedman (historyInitial initial T) (historyKernel K T)
    (historyAdditive g T) (historyCounter v T) (historyCounterRate v T) c hc
  · intro ω _
    simp only [historyAdditive_zero,historyCounter_zero,le_refl,and_self]
  · intro j ω hω pI hpI
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hpI
      obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hpI
      rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hbounded j hj _ (historyLaw_current_support initial K T j hj.le ω hω) b hb
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hpI
      subst pI
      rw [historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,abs_zero]
      exact hc.le
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact (hmean j hj _ (historyLaw_current_support initial K T j hj.le ω hω)).le
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self]
  · intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj,pmfMean_map,historyCounterRate,ite_eq_left hj]
      simp_rw [historyAdditive_update g T j hj,add_sub_cancel_left]
      exact hvar j hj _ (historyLaw_current_support initial K T j hj.le ω hω)
    · rw [historyKernel,ite_eq_right hj,pmfMean_pure,
        historyAdditive_frozen g T j (Nat.le_of_not_gt hj),sub_self,
        historyCounterRate,ite_eq_right hj,zero_pow (by decide : 2 ≠ 0)]
  · intro j ω _ pI hpI
    by_cases hj : j < T
    · rw [historyKernel,ite_eq_left hj] at hpI
      obtain ⟨b,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hpI
      rw [historyCounter_update v T j hj,historyCounterRate,ite_eq_left hj]
    · rw [historyKernel,ite_eq_right hj,PMF.mem_support_pure_iff] at hpI
      subst pI
      rw [historyCounter_frozen v T j (Nat.le_of_not_gt hj),
        historyCounterRate,ite_eq_right hj,add_zero]
  · exact hr
  · exact hV

lemma historyAdditive_past {α : Type*} (g : ℕ → α → α → ℝ)
    (T j : ℕ) (ω pI : History α T)
    (h : ∀ i : Fin (T+1), i.val ≤ min j T → ω i = pI i) :
    historyAdditive g T j ω = historyAdditive g T j pI := by
  unfold historyAdditive
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < min j T := Finset.mem_range.mp hs
  have hsc : (historyIndex T s).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (Nat.le_of_lt hs')
  have hsn : (historyIndex T (s+1)).val ≤ min j T := by
    simp only [historyIndex]
    exact (Nat.min_le_left _ _).trans (by omega)
  rw [h _ hsc,h _ hsn]

theorem history_additive_freedman_maximal {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T) (Finset.range (T+1))
    (fun j ω => r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T j ω ∧ historyCounter v T j ω ≤ V
          then 1 else 0)) ≤ (T+1 : ℝ)*Real.exp (-r^2/(4*(V+c*r))) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (T+1), Real.exp (-r^2/(4*(V+c*r))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
        rw [historyLaw_past_mean initial K T j T hjT _ (by
          intro ω pI h
          rw [historyAdditive_past g T j ω pI h,historyCounter_past v T j ω pI h])]
        exact history_additive_freedman initial K g v T c hc hbounded hmean hvar j r V hr hV
      _ = _ := by simp
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range,Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl



/-- **Anytime-Freedman с k-зависимыми порогами **:
лестница {r j, V j} по горизонту j ≤ T — обобщение
равнопороговой `history_additive_freedman_maximal`:
P[∃ j ≤ T: r j ≤ S_j ∧ C_j ≤ V_j]
  ≤ Σ_{j=0}^{T} exp(−r j² / (4·(V j + c·r j))).
Каждый член лестницы — собственный Freedman-хвост;
мост законов — `historyLaw_past_mean` (событие j-го
префикса не зависит от «заморозки» после j). -/
theorem anytime_freedman_thresholds {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ)
    (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hV : ∀ j, 0 ≤ V j) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V j then 1 else 0) ≤
      ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
  classical
  have hcov := pmfMean_event_union (historyLaw initial K T T)
    (Finset.range (T+1))
    (fun j ω => r j ≤ historyAdditive g T j ω ∧
      historyCounter v T j ω ≤ V j)
  have hsum : (∑ j ∈ Finset.range (T+1),
      pmfMean (historyLaw initial K T T)
        (fun ω => if r j ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0)) ≤
      ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjT : j ≤ T := by have := Finset.mem_range.mp hj; omega
    rw [historyLaw_past_mean initial K T j T hjT _ (by
      intro ω pI h
      rw [historyAdditive_past g T j ω pI h,
        historyCounter_past v T j ω pI h])]
    exact history_additive_freedman initial K g v T c hc
      hbounded hmean hvar j (r j) (V j) (hr j) (hV j)
  apply le_trans _ hsum
  convert hcov using 1 <;> try rfl
  · apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  · apply Finset.sum_congr rfl
    intro j _
    apply congrArg (pmfMean (historyLaw initial K T T))
    funext ω
    split_ifs <;> rfl

end

end Hagi.Probability

/-!
# FreedmanTwoSided — the |S| form of the joint maximal
Freedman (the Hagi corollary closing the plan's
"two-sided anytime joint" line)

The plan (§1.2) asks for
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ v] ≤ 2(T+1)·exp(−r²/(4(v+cr))).
The ported one-sided maximal form applies to S and to −S
(negation preserves the bound and second-moment conditions;
the mean condition holds with equality); the two-sided
event is the union of the two one-sided events and the
finite union bound (pmfMean_event_union) doubles the
one-sided bound.
-/

namespace Hagi.Probability

open scoped BigOperators

/-- **The two-sided joint anytime Freedman**: for centered
bounded increments with the variance counter,
P[∃j≤T: |S_j| ≥ r ∧ V_j ≤ V] ≤ 2(T+1)·exp(−r²/(4(V+c·r))). -/
theorem history_additive_freedman_two_sided
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support, pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0) ≤
      2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by
  classical
  -- the negated functional satisfies the same conditions
  have hbounded' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |(-g) k a b| ≤ c := by
    intro k hk a ha b hb
    show |-(g k a b)| ≤ c
    rw [abs_neg]
    exact hbounded k hk a ha b hb
  have hmean' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => -(g k a b)) = 0
    have h0 : pmfMean (K k a) (fun b => g k a b) = 0 := hmean k hk a ha
    have hneg : pmfMean (K k a) (fun b => -(g k a b))
        = -pmfMean (K k a) (fun b => g k a b) := by
      have := pmfMean_const_mul (K k a) (-1) (fun b => g k a b)
      simpa using this
    rw [hneg, h0]
    ring
  have hvar' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b)^2) ≤ v k a := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => (-(g k a b))^2) ≤ v k a
    have hsq : pmfMean (K k a) (fun b => (-(g k a b))^2)
        = pmfMean (K k a) (fun b => (g k a b)^2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    rw [hsq]
    exact hvar k hk a ha
  -- the two one-sided maximal bounds
  have h1 := history_additive_freedman_maximal initial K g v T c hc
    hbounded hmean hvar r V hr hV
  have h2 := history_additive_freedman_maximal initial K
    (fun k a b => -g k a b) v T c hc hbounded' hmean' hvar' r V hr hV
  -- negated-functional sums: pointwise identity under funext
  have hnegfun : ∀ ω : History α T,
      (fun (j : ℕ) => historyAdditive (fun k a b => -g k a b) T j ω)
      = fun (j : ℕ) => -historyAdditive g T j ω := by
    intro ω
    funext j
    unfold historyAdditive
    rw [← Finset.sum_neg_distrib]
  -- the two-sided mean splits via the ADDITIVE indicator bound
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
        (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := by
    refine pmfMean_mono _ (fun ω _ => ?_)
    by_cases hex : ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
      historyCounter v T j ω ≤ V
    · rw [ite_eq_left hex]
      by_cases hpos : ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V
      · rw [ite_eq_left hpos]
        have hz : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then 1 else 0) :=
          ite_nonneg (by norm_num) (by norm_num)
        linarith
      · -- S never reaches r upward, but |S| does: so -S does
        obtain ⟨j, hj, habs, hctr⟩ := hex
        have hnegup : r ≤ -historyAdditive g T j ω := by
          by_contra hcon
          push_neg at hcon
          have hS : historyAdditive g T j ω < r :=
            lt_of_not_ge (fun h => hpos ⟨j, hj, h, hctr⟩)
          have habslt : |historyAdditive g T j ω| < r :=
            abs_lt.mpr ⟨by linarith, hS⟩
          linarith
        rw [ite_eq_right hpos,
          ite_eq_left ⟨j, hj, hnegup, hctr⟩]
        norm_num
    · rw [ite_eq_right hex]
      have hz1 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      have hz2 : (0:ℝ) ≤ (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      linarith
  -- mean of the sum = sum of the means; rewrite the negated part
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0))
      = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := by
    rw [pmfMean_add]
    congr 1
    · refine pmfMean_congr _ (fun ω _ => ?_)
      have hj : ∀ j, historyAdditive (fun k a b => -g k a b) T j ω
          = -historyAdditive g T j ω := fun j => congrFun (hnegfun ω) j
      simp only [hj]
  calc pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r ≤ |historyAdditive g T j ω| ∧
          historyCounter v T j ω ≤ V then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)
            + (if ∃ j ≤ T, r ≤ -historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V then (1:ℝ) else 0)) := hsplit
    _ = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V then (1:ℝ) else 0) := hsum
    _ ≤ ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r)))
        + ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) :=
        add_le_add h1 h2
    _ = 2 * ((T : ℝ) + 1) * Real.exp (-r^2/(4*(V+c*r))) := by ring


/-- **Двусторонняя anytime-лестница с k-зависимыми
порогами**: композиция `anytime_freedman_thresholds` (`anytime_freedman_
thresholds`) с двусторонним расщеплением:
P[∃ j ≤ T: |S_j| ≥ r j ∧ C_j ≤ V j] ≤ 2·Σ_j exp(−r j²/(4(V j + c·r j))).
Каждое плечо (S и −S) — своя пороговая лестница. -/
theorem anytime_freedman_thresholds_two_sided
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ)
    (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b)^2) ≤ v k a)
    (r V : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hV : ∀ j, 0 ≤ V j) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V j then 1 else 0) ≤
      2 * ∑ j ∈ Finset.range (T+1),
        Real.exp (-(r j)^2/(4*(V j + c * r j))) := by
  classical
  -- negated functional: same conditions
  have hbounded' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |(-g) k a b| ≤ c := by
    intro k hk a ha b hb
    show |-(g k a b)| ≤ c
    rw [abs_neg]
    exact hbounded k hk a ha b hb
  have hmean' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => -(g k a b)) = 0
    have h0 : pmfMean (K k a) (fun b => g k a b) = 0 := hmean k hk a ha
    have hneg : pmfMean (K k a) (fun b => -(g k a b))
        = -pmfMean (K k a) (fun b => g k a b) := by
      have := pmfMean_const_mul (K k a) (-1) (fun b => g k a b)
      simpa using this
    rw [hneg, h0]
    ring
  have hvar' : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b)^2)
        ≤ v k a := by
    intro k hk a ha
    show pmfMean (K k a) (fun b => (-(g k a b))^2) ≤ v k a
    have hsq : pmfMean (K k a) (fun b => (-(g k a b))^2)
        = pmfMean (K k a) (fun b => (g k a b)^2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    rw [hsq]
    exact hvar k hk a ha
  -- additive indicator split: |S| event ⊆ S-event + (−S)-event
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
        historyCounter v T j ω ≤ V j then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
        (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)) := by
    refine pmfMean_mono _ (fun ω _ => ?_)
    by_cases hex : ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
      historyCounter v T j ω ≤ V j
    · rw [ite_eq_left hex]
      by_cases hpos : ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
        historyCounter v T j ω ≤ V j
      · rw [ite_eq_left hpos]
        have hz : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then 1 else 0) :=
          ite_nonneg (by norm_num) (by norm_num)
        linarith
      · obtain ⟨j, hj, habs, hctr⟩ := hex
        have hnegup : r j ≤ -historyAdditive g T j ω := by
          by_contra hcon
          push_neg at hcon
          have hS : historyAdditive g T j ω < r j :=
            lt_of_not_ge (fun h => hpos ⟨j, hj, h, hctr⟩)
          have habslt : |historyAdditive g T j ω| < r j :=
            abs_lt.mpr ⟨by linarith, hS⟩
          linarith
        rw [ite_eq_right hpos,
          ite_eq_left ⟨j, hj, hnegup, hctr⟩]
        norm_num
    · rw [ite_eq_right hex]
      have hz1 : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      have hz2 : (0:ℝ) ≤ (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
          historyCounter v T j ω ≤ V j then 1 else 0) :=
        ite_nonneg (by norm_num) (by norm_num)
      linarith
  -- second summand: rewrite −S additive as negated functional
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
          + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0))
      = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r j ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0) := by
    rw [pmfMean_add]
    congr 1
    · refine pmfMean_congr _ (fun ω _ => ?_)
      have hj : ∀ j, historyAdditive (fun k a b => -g k a b) T j ω
          = -historyAdditive g T j ω := fun j => by
        unfold historyAdditive
        rw [← Finset.sum_neg_distrib]
      simp only [hj]
  calc pmfMean (historyLaw initial K T T)
        (fun ω => if ∃ j ≤ T, r j ≤ |historyAdditive g T j ω| ∧
          historyCounter v T j ω ≤ V j then 1 else 0)
      ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
            + (if ∃ j ≤ T, r j ≤ -historyAdditive g T j ω ∧
              historyCounter v T j ω ≤ V j then (1:ℝ) else 0)) := hsplit
    _ = pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T, r j ≤ historyAdditive g T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0)
        + pmfMean (historyLaw initial K T T)
          (fun ω => if ∃ j ≤ T,
            r j ≤ historyAdditive (fun k a b => -g k a b) T j ω ∧
            historyCounter v T j ω ≤ V j then (1:ℝ) else 0) := hsum
    _ ≤ ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j)))
        + ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j))) :=
        add_le_add
          (anytime_freedman_thresholds initial K g v T c hc
            hbounded hmean hvar r V hr hV)
          (anytime_freedman_thresholds initial K
            (fun k a b => -g k a b) v T c hc hbounded' hmean' hvar'
            r V hr hV)
    _ = 2 * ∑ j ∈ Finset.range (T+1),
          Real.exp (-(r j)^2/(4*(V j + c * r j))) := by ring

end Hagi.Probability

namespace Hagi

end Hagi


/-!
# Freedman-мост: стохастический безопасный шаг

Мост между мартингальной концентрацией и CertifiedLoop-контрактом:
посылки о шуме стохастического градиентного шага (ограниченный
условный шум, нулевое условное среднее, ограниченная условная
дисперсия) плюс детерминированный drift конвертируются в
высоковероятностную гарантию реализованного спуска.

Строится на адаптивном Freedman-хвосте `history_additive_freedman`
(P[отклонение ≥ r при компенсаторе ≤ V] ≤ exp(−r²/(4(V+c·r)))).

**(variance-компенсатор):** фиксированный-λ Freedman-хвост с
ФАКТИЧЕСКИМ дисперсионным компенсатором (суммой условных
дисперсий) вместо константного σ: суперmartингал
`history_exp_compensated_le`, хвост `history_variance_freedman_lam`,
замкнутый радиус `freedman_variance_radius`
(exp(−r²/(4V)) при c·r ≤ 2V — без линейного члена) и мост
`stochastic_safe_step_variance` (failure = exp(−r²/(4·T·σ))
при c·r ≤ 2·T·σ; в этом режиме строго лучше mixed-радиуса
exp(−r²/(4·(T·σ+c·r)))).

**Что доказано:**

* `historyAdditive_mono` — поточечная монотонность аддитивного
  функционала траектории.
* `driftAdditive` — сумма предсказуемого drift по траектории;
  `historyAdditive_drift_sub` — разложение drift−шум.
* `historyCounter_const` — при константной дисперсионной посылке
  σ компенсатор `historyCounter` детерминирован: (min k T)·σ.
* `freedman_radius_sq` — замкнутая форма радиуса
  R = 2·√(V·L) + 4·c·L: R² ≥ 4·L·(V + c·R) при L ≥ 0.
* `freedman_failure_closed` — с L = −log δ хвост Freedman ≤ δ.
* `CertStochasticStep` — CertStepGen-form контракт: drop,
  drop_pos, failure и whp-закон descent_whp.
* `stochastic_safe_step` — ГЛАВНЫЙ МОСТ: для реализованного
  декремента цели, покрывающего drift минус мартингал-разность,
  drop = T·γ − r достигается с вероятностью ≥ 1 −
  exp(−r²/(4·(T·σ + c·r))).
* `stochastic_safe_step_closed` — то же с замкнутым радиусом
  R = 2·√(T·σ·L) + 4·c·L и failure ≤ δ.

**(полная форма Freedman, Bennett-chord):** хорда Беннетта
`exp_le_chord_nonneg` (для x ∈ [0,3):
eˣ − 1 − x ≤ x²/(2(1−x/3)), доказана с нуля цепочкой из трёх
монотонностей; MGF с хордовым коэффициентом
`pmfMean_exp_chord_le` (λ·c < 3), суперmartingale
`history_exp_chord_compensated_le`, хвост
`history_variance_freedman_chord_lam` и ГЛАВНАЯ
`freedman_full`: P[S ≥ r ∧ C ≤ V] ≤ exp(−r²/(2(V+c·r/3)))
БЕЗ режимной посылки (λ = r/(V+cr/3), λc < 3 автоматически).
Сравнения: `freedman_full_exp_le_mixed_exp` — не хуже mixed
exp(−r²/(4(V+cr))) всегда (константы 4→2, cr→cr/3, равенство
только при cr = 0); с variance-формой exp(−r²/(4V)) —
несравнимо в общем, режимное разбиение c·r/3 ≤ V
(`freedman_full_exp_le_variance_exp`) vs V ≤ c·r/3
(`freedman_variance_exp_le_full_exp`).

**Честные ограничения (premise-form limitations):**

* адаптивного-λ Freedman нет — используется λ-оптимизация
  фиксированного хвоста базовой теоремы; fixed-λ вариант с
  variance-компенсатором, а полный радиус r²/(2(V+cr/3)) хордой Беннетта
  (λ-оптимизация в `freedman_full`, per-instance);
  data-зависимый λ-процесс по-прежнему не строится;
* дисперсионный компенсатор моста — детерминированный порог
  T·σ из посылки условной дисперсии ≤ σ² (посылка (b)); в хвосте
  при этом работает фактический (capped) компенсатор
  min(cond var, σ) ≤ σ глобально, поэтому ветка {C > T·σ} пуста
  и union bound не нужен; улучшение радиуса — только в режиме
  c·r ≤ 2·T·σ (посылка `hrc`), вне режима применима mixed-форма;
* λ выбирается априорно под (r, V) (per-instance),
  данные-зависимый λ-процесс не строится;
* `CertStochasticStep` — самодостаточная структура: `CertStepGen`
  (`Hagi.Cert.StepGen`) живёт в другом слое (import запрещён
  LayerLint); адаптация в `CertStepGen` — задача consumer-слоя.

Посылки все явные, эмпирических констант (`h_emp_`) нет.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability

section
open scoped BigOperators

variable {α : Type*}

/-- Поточечная монотонность `historyAdditive`: если h ≤ h'
при всех аргументах, то и суммы по траектории упорядочены. -/
theorem historyAdditive_mono (h h' : ℕ → α → α → ℝ) (T k : ℕ)
    (ω : History α T)
    (hle : ∀ j a b, h j a b ≤ h' j a b) :
    historyAdditive h T k ω ≤ historyAdditive h' T k ω := by
  unfold historyAdditive
  exact Finset.sum_le_sum fun j _ => hle j _ _

/-- Сумма предсказуемого (зависящего только от текущего
состояния) drift-функционала по первым k шагам траектории. -/
noncomputable def driftAdditive (drift : ℕ → α → ℝ) (T k : ℕ)
    (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), drift j (ω (historyIndex T j))

/-- Аддитивный функционал «drift минус шум» раскладывается в
разность сумм drift и шума. -/
theorem historyAdditive_drift_sub (drift : ℕ → α → ℝ)
    (g : ℕ → α → α → ℝ) (T k : ℕ) (ω : History α T) :
    historyAdditive (fun j a b => drift j a - g j a b) T k ω
      = driftAdditive drift T k ω - historyAdditive g T k ω := by
  unfold historyAdditive driftAdditive
  rw [← Finset.sum_sub_distrib]

/-- При константной дисперсионной посылке компенсатор
`historyCounter` не зависит от траектории: он равен
(min k T)·σ. -/
theorem historyCounter_const (σ : ℝ) (T k : ℕ) (ω : History α T) :
    historyCounter (fun _ _ => σ) T k ω = (min k T : ℕ) * σ := by
  unfold historyCounter
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

section
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Замкнутая форма Freedman-радиуса: для R = 2·√(V·L) + 4·c·L
выполнено R² ≥ 4·L·(V + c·R) (достаточное условие хвоста ≤
exp(−L)). -/
theorem freedman_radius_sq (V c L : ℝ) (hV : 0 ≤ V) (hc : 0 ≤ c)
    (hL : 0 ≤ L) :
    4 * L * (V + c * (2 * Real.sqrt (V * L) + 4 * c * L))
      ≤ (2 * Real.sqrt (V * L) + 4 * c * L) ^ 2 := by
  have hVL : 0 ≤ V * L := by positivity
  have hs2 : Real.sqrt (V * L) ^ 2 = V * L := Real.sq_sqrt hVL
  have hsn : 0 ≤ Real.sqrt (V * L) := Real.sqrt_nonneg _
  nlinarith [hs2, mul_nonneg (mul_nonneg hc hL) hsn]

/-- С L = −log δ (δ ∈ (0, 1)) замкнутый радиус
R = 2·√(V·L) + 4·c·L даёт хвост Freedman ≤ δ. -/
theorem freedman_failure_closed (V c δ : ℝ) (hV : 0 ≤ V) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ))))) ≤ δ := by
  have hL : 0 < -Real.log δ := by
    have hlt : Real.log δ < Real.log 1 := Real.log_lt_log hδ hδ1
    have h2 : Real.log δ < 0 := by simpa using hlt
    linarith
  have hVL : 0 ≤ V * (-Real.log δ) := by positivity
  have hsn : 0 ≤ Real.sqrt (V * (-Real.log δ)) :=
    Real.sqrt_nonneg _
  have hRnn : 0 ≤ c * (2 * Real.sqrt (V * (-Real.log δ))) :=
    mul_nonneg hc.le (mul_nonneg (by norm_num) hsn)
  have hcl : 0 < c * (-Real.log δ) := mul_pos hc hL
  have h4 : 0 < 4 * c * (-Real.log δ) := by nlinarith [hcl]
  have hRpos : 0 < c * (4 * c * (-Real.log δ)) := mul_pos hc h4
  have hX : 0 < c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ)) := by nlinarith [hRnn, hRpos]
  have hVX : 0 < V + c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ)) := by nlinarith [hV, hX]
  have hden : 0 < 4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
      + 4 * c * (-Real.log δ))) := mul_pos (by norm_num) hVX
  have hkey := freedman_radius_sq V c (-Real.log δ) hV hc.le hL.le
  have hdiv : -(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)))) ≤ Real.log δ := by
    rw [div_le_iff₀ hden]
    nlinarith [hkey]
  have hexp : Real.exp (-(2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)) ^ 2
      / (4 * (V + c * (2 * Real.sqrt (V * (-Real.log δ))
        + 4 * c * (-Real.log δ)))))
      ≤ Real.exp (Real.log δ) :=
      Real.exp_le_exp.mpr hdiv
  rwa [Real.exp_log hδ] at hexp

/-- CertStepGen-form контракт для стохастического шага:
положительный drop и whp-закон реализованного спуска
(вероятность недостижения drop ≤ failure). Аналог полей
drop/drop_pos/risk канонического сертификационного ядра;
вероятностная версия поля descent. -/
structure CertStochasticStep {Ω : Type*} [Fintype Ω]
    (law : PMF Ω) (realized : Ω → ℝ) where
  /-- Сертифицированная нижняя граница реализованного спуска. -/
  drop : ℝ
  drop_pos : 0 < drop
  /-- Верхняя граница вероятности недостижения drop. -/
  failure : ℝ
  /-- Вероятность события {drop ≤ realized} не меньше 1 − failure. -/
  descent_whp : pmfMean law
      (fun ω => if drop ≤ realized ω then 1 else 0) ≥ 1 - failure

/-- **Freedman-мост (главный)**: пусть на горизонте T ≥ 1 шагов

(a) шум g — мартингал-разность с ограничением |g| ≤ c,
    нулевым условным средним и условной дисперсией ≤ σ²
    (посылки `h_noise_bounded`/`h_noise_cond_mean`/
    `h_noise_cond_var`);
(b) детерминированный drift не хуже γ в шаге
    (`h_drift_floor`);
(c) реализованный декремент цели покрывает drift минус шум
    (`h_step_descent`).

Тогда drop = T·γ − r достигается с вероятностью ≥
1 − exp(−r²/(4·(T·σ + c·r))): `stochastic_safe_step_whp`
(Prop-форма) и обёртка `stochastic_safe_step`. -/
theorem stochastic_safe_step_whp (initial : PMF α) (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * (T * σ + c * r))) := by
    classical
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    -- поточечный спуск: шум-событие {S ≤ r} влечёт drop ≤ Σh
    have hmono : ∀ ω : History α T,
        historyAdditive (fun k a b => drift k a - g k a b) T T ω
          ≤ historyAdditive h T T ω :=
      fun ω => historyAdditive_mono _ _ T T ω
        (fun k a b => h_step_descent k a b)
    have hsplit := historyAdditive_drift_sub drift g T T
    have hfloor : ∀ ω : History α T,
        (T : ℝ) * γ ≤ driftAdditive drift T T ω := by
      intro ω
      unfold driftAdditive
      simp only [Nat.min_self]
      calc (T : ℝ) * γ = ∑ _j ∈ Finset.range T, γ := by
            rw [Finset.sum_const, Finset.card_range]; simp
        _ ≤ _ := Finset.sum_le_sum
          fun j _ => h_drift_floor j (ω (historyIndex T j))
    have hcover : ∀ ω : History α T,
        historyAdditive g T T ω ≤ r →
        T * γ - r ≤ historyAdditive h T T ω := by
      intro ω hSr
      have h1 := hmono ω
      rw [hsplit ω] at h1
      have h2 := hfloor ω
      linarith
    -- компенсатор детерминирован: C = T·σ
    have hcst : ∀ ω : History α T,
        historyCounter (fun _ _ => σ) T T ω = T * σ :=
      fun ω => by rw [historyCounter_const σ T T ω, Nat.min_self]
    -- базовый Freedman-хвост на константном компенсаторе
    have htail := history_additive_freedman initial K g
      (fun _ _ => σ) T c hc h_noise_bounded h_noise_cond_mean
      h_noise_cond_var T r (T * σ) hr
        (mul_nonneg hT'.le hσ)
    simp only [hcst, le_refl, and_true] at htail
    -- поточечная цепочка индикаторов
    have hpt1 : ∀ ω : History α T,
        (if T * γ - r ≤ historyAdditive h T T ω then (1 : ℝ) else 0)
          ≥ (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0) := by
      intro ω
      by_cases hS : historyAdditive g T T ω ≤ r
      · have hcov := hcover ω hS
        simp [hcov, hS]
      · simp only [hS, ite_false, ge_iff_le]
        split_ifs <;> norm_num
    have hpt2 : ∀ ω : History α T,
        (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
          + (if r ≤ historyAdditive g T T ω
              ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
              then (1 : ℝ) else 0) ≥ 1 := by
      intro ω
      rw [hcst ω]
      by_cases hS : historyAdditive g T T ω ≤ r
      · by_cases hrS : r ≤ historyAdditive g T T ω <;>
          simp [hS, hrS]
      · have hrS : r ≤ historyAdditive g T T ω := by
          have hne : ¬(historyAdditive g T T ω ≤ r) := hS
          linarith
        simp [hS, hrS]
    -- вероятностная цепочка
    have hev1 : pmfMean (historyLaw initial K T T)
        (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
        ≥ pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => hpt1 ω)
    have hev2 : pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0)
        ≥ 1 - pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
            then 1 else 0) := by
      have hsum : pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω
                ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                then (1 : ℝ) else 0))
          = pmfMean (historyLaw initial K T T)
              (fun ω => if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + pmfMean (historyLaw initial K T T)
              (fun ω => if r ≤ historyAdditive g T T ω
                  ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                  then (1 : ℝ) else 0) :=
        pmfMean_add _ _ _
      have hge : (1 : ℝ) ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω
                ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
                then (1 : ℝ) else 0)) :=
        le_trans (le_of_eq (pmfMean_const (historyLaw initial K T T) 1).symm)
          (pmfMean_mono (historyLaw initial K T T)
            (fun ω _ => hpt2 ω))
      rw [hsum] at hge
      linarith
    have hmonoC : pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter (fun _ _ => σ) T T ω ≤ T * σ
            then 1 else 0)
        ≤ pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => by
        by_cases h1 : r ≤ historyAdditive g T T ω
        · by_cases h2 : historyCounter (fun _ _ => σ) T T ω ≤ T * σ <;>
            simp [h1, h2]
        · simp [h1])
    linarith [hev1, hev2, hmonoC, htail]

/-- Обёртка-сертификат: `stochastic_safe_step_whp` в форме
`CertStochasticStep`. -/
noncomputable def stochastic_safe_step (initial : PMF α) (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) where
  drop := T * γ - r
  drop_pos := by
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  failure := Real.exp (-r ^ 2 / (4 * (T * σ + c * r)))
  descent_whp := stochastic_safe_step_whp initial K T hT γ c σ r hγ hc hσ
    hr hdrop h g drift h_noise_bounded h_noise_cond_mean h_noise_cond_var
    h_step_descent h_drift_floor

/-- **Freedman-мост, замкнутый радиус**: то же, что
`stochastic_safe_step`, с явным радиусом
R = 2·√(T·σ·L) + 4·c·L, L = −log δ, и failure ≤ δ. -/
noncomputable def stochastic_safe_step_closed (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ δ : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdrop : 2 * Real.sqrt (T * σ * (-Real.log δ))
        + 4 * c * (-Real.log δ) < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) := by
  classical
  have hstep := stochastic_safe_step_whp initial K T hT γ c σ
    (2 * Real.sqrt (T * σ * (-Real.log δ))
      + 4 * c * (-Real.log δ))
    hγ hc hσ (by
      have hL : 0 < -Real.log δ := by
        have hlt : Real.log δ < Real.log 1 :=
          Real.log_lt_log hδ hδ1
        have h2 : Real.log δ < 0 := by simpa using hlt
        linarith
      have hVL : 0 ≤ T * σ * (-Real.log δ) := by positivity
      have hsn : 0 ≤ Real.sqrt (T * σ * (-Real.log δ)) :=
        Real.sqrt_nonneg _
      have hcl : 0 < c * (-Real.log δ) := mul_pos hc hL
      have h4 : 0 < 4 * c * (-Real.log δ) := by nlinarith [hcl]
      nlinarith [hsn, h4])
    hdrop h g drift h_noise_bounded h_noise_cond_mean
    h_noise_cond_var h_step_descent h_drift_floor
  have htail := freedman_failure_closed (T * σ) c δ
    (by
      have hL : 0 < -Real.log δ := by
        have hlt : Real.log δ < Real.log 1 :=
          Real.log_lt_log hδ hδ1
        have h2 : Real.log δ < 0 := by simpa using hlt
        linarith
      positivity)
    hc hδ hδ1
  refine ⟨T * γ - (2 * Real.sqrt (T * σ * (-Real.log δ))
      + 4 * c * (-Real.log δ)), ?_, δ, ?_⟩
  · have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  · linarith [htail]

end

section
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Capped дисперсионный компенсатор min(фактическая условная
дисперсия, σ) поточечно ограничен (min k T)·σ — глобально,
без посылок о support. Это ключ к покрытию ветки {C > V}:
при V = T·σ она пуста, union bound не нужен. -/
theorem historyCounter_var_le (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (T k : ℕ) (σ : ℝ) (ω : History α T) :
    historyCounter (fun j a => min
      (pmfMean (K j a) (fun b => g j a b ^ 2)) σ) T k ω
      ≤ (min k T : ℕ) * σ := by
  unfold historyCounter
  calc ∑ j ∈ Finset.range (min k T),
      (fun j a => min (pmfMean (K j a) (fun b => g j a b ^ 2)) σ) j
        (ω (historyIndex T j))
      ≤ ∑ _j ∈ Finset.range (min k T), σ :=
        Finset.sum_le_sum fun j _ => min_le_right _ _
    _ = (min k T : ℕ) * σ := by
        rw [Finset.sum_const, Finset.card_range]; simp

/-- **Variance-compensator суперmartингал**: при
ограниченном шуме (|g| ≤ c), нулевом условном среднем и
условной дисперсии ≤ v, для λ ≥ 0 с λ·c ≤ 1 экспоненциальный
компенсированный потенциал exp(λ·S_k − λ²·C_k) — суперmartingale
на траекториях: его среднее по historyLaw ≤ 1. Здесь C_k —
ФАКТИЧЕСКАЯ сумма условных дисперсий (компенсатор v), а не
константа. Одношаговое ядро — `pmfMean_exp_le` (MGF с
квадратичным variance-членом). -/
theorem history_exp_compensated_le (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) :
    pmfMean (historyLaw initial K T k)
      (fun ω => Real.exp (lam * historyAdditive g T k ω
        - lam ^ 2 * historyCounter v T k ω)) ≤ 1 := by
  classical
  set F : ℕ → History α T → ℝ := fun j ω =>
    Real.exp (lam * historyAdditive g T j ω
      - lam ^ 2 * historyCounter v T j ω) with hF
  have hone : ∀ j : ℕ, ∀ ω : History α T,
      ω ∈ (historyLaw initial K T j).support →
      pmfMean (historyKernel K T j ω) (F (j + 1)) ≤ F j ω := by
    intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel, ite_eq_left hj, pmfMean_map]
      have hsupp := historyLaw_current_support initial K T j hj.le ω hω
      have hfac : ∀ b : α, F (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b)
          = F j ω * Real.exp (lam * g j (ω (historyIndex T j)) b
              - lam ^ 2 * v j (ω (historyIndex T j))) := by
        intro b
        simp only [hF]
        rw [historyAdditive_update g T j hj, historyCounter_update v T j hj,
          ← Real.exp_add]
        congr 1
        ring
      simp_rw [hfac]
      rw [pmfMean_const_mul]
      have hmgf := pmfMean_exp_le (K j (ω (historyIndex T j)))
        (fun b => g j (ω (historyIndex T j)) b) c
        (v j (ω (historyIndex T j))) lam hlam hclam
        (fun b hb => hbounded j hj _ hsupp b hb)
        (by rw [← hmean j hj _ hsupp])
        (hvar j hj _ hsupp)
      have hsplit : pmfMean (K j (ω (historyIndex T j)))
          (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b
            - lam ^ 2 * v j (ω (historyIndex T j))))
          = Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * pmfMean (K j (ω (historyIndex T j)))
              (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)) := by
        rw [← pmfMean_const_mul]
        apply pmfMean_congr
        intro b _
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hstep1 : F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 * v j (ω (historyIndex T j)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmgf
                (by positivity : (0 : ℝ) ≤ Real.exp
                  (-lam ^ 2 * v j (ω (historyIndex T j)))))
              (by positivity : (0 : ℝ) ≤ F j ω)
      calc F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (-lam ^ 2 * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 * v j (ω (historyIndex T j)))) := hstep1
      _ = F j ω := by
            rw [← Real.exp_add]
            have hzero : -lam ^ 2 * v j (ω (historyIndex T j))
                + lam ^ 2 * v j (ω (historyIndex T j)) = 0 := by ring
            rw [hzero, Real.exp_zero, mul_one]
    · rw [historyKernel, ite_eq_right (by omega : ¬ j < T), pmfMean_pure]
      simp only [hF]
      rw [historyAdditive_frozen g T j (by omega : T ≤ j),
        historyCounter_frozen v T j (by omega : T ≤ j)]
  induction k with
  | zero => simp
  | succ k ih =>
      have hunfold : pmfMean (historyLaw initial K T (k + 1)) (F (k + 1))
          = pmfMean (historyLaw initial K T k)
            (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1))) := by
        change pmfMean ((historyLaw initial K T k).bind
          (historyKernel K T k)) (F (k + 1)) = _
        rw [pmfMean_bind]
      rw [hunfold]
      have hzero : pmfMean (historyLaw initial K T k)
          (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1)))
          = pmfMean (historyLaw initial K T k)
            (fun ω => if ω ∈ (historyLaw initial K T k).support
              then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0) := by
        apply pmfMean_congr
        intro ω hω
        simp [hω]
      rw [hzero]
      have hmono : pmfMean (historyLaw initial K T k)
          (fun ω => if ω ∈ (historyLaw initial K T k).support
            then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0)
          ≤ pmfMean (historyLaw initial K T k) (F k) := by
            apply pmfMean_mono
            intro ω _
            by_cases hω : ω ∈ (historyLaw initial K T k).support
            · simpa [hω] using hone k ω hω
            · simp [hω]; positivity
      have hFk : pmfMean (historyLaw initial K T k) (F k)
          = pmfMean (historyLaw initial K T k)
            (fun ω => Real.exp (lam * historyAdditive g T k ω
              - lam ^ 2 * historyCounter v T k ω)) := by
            rfl
      exact hmono.trans (hFk.trans_le ih)

/-- **Fixed-λ Freedman-хвост с фактическим компенсатором**
P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−λ·r + λ²·V) для любого
λ ∈ [0, 1/c] и детерминированного порога V ≥ 0. Компенсатор
C_k — фактическая сумма условных дисперсий (не константа). -/
theorem history_variance_freedman_lam (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * c ≤ 1)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-lam * r + lam ^ 2 * V) :=
  pmfMean_compensated_tail _ (historyAdditive g T k) (historyCounter v T k)
    lam r V hlam
    (history_exp_compensated_le initial K g v T c lam hlam hclam
      hbounded hmean hvar k)

/-- **Замкнутый радиус с variance-компенсатором**:
оптимизация λ = r/(2·V) в режиме c·r ≤ 2·V (λ·c ≤ 1) даёт
P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−r²/(4·V)) — БЕЗ линейного члена,
строго сильнее базового радиуса exp(−r²/(4·(V+c·r))) при
c > 0, r > 0 в этом режиме. -/
theorem freedman_variance_radius (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 < V)
    (hrc : c * r ≤ 2 * V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0) ≤ Real.exp (-r ^ 2 / (4 * V)) := by
  have hlam : (0 : ℝ) ≤ r / (2 * V) := by positivity
  have hclam : r / (2 * V) * c ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * V)).mpr
    linarith
  have htail := history_variance_freedman_lam initial K g v T c (r / (2 * V))
    hlam hclam hbounded hmean hvar k r V hr hV.le
  have hexp : -(r / (2 * V)) * r + (r / (2 * V)) ^ 2 * V
      = -r ^ 2 / (4 * V) := by
    field_simp
    ring
  rw [hexp] at htail
  exact htail

/-- **Freedman-мост, variance-форма (главный)**: при тех же
посылках, что `stochastic_safe_step_whp`, плюс режим
`hrc : c·r ≤ 2·T·σ`, drop = T·γ − r достигается с вероятностью
≥ 1 − exp(−r²/(4·T·σ)) — радиус без линейного члена, строго
лучше mixed exp(−r²/(4·(T·σ+c·r))) в этом режиме. Компенсатор
в хвосте — фактический (capped) дисперсионный процесс
min(cond var, σ) ≤ σ глобально, поэтому ветка {C > T·σ} пуста
и union bound не нужен. Порог T·σ — детерминированный,
apriori наблюдаемый (premise-form). -/
theorem stochastic_safe_step_variance_whp (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hrc : c * r ≤ 2 * ((T : ℝ) * σ))
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * ((T : ℝ) * σ))) := by
    classical
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hmono : ∀ ω : History α T,
        historyAdditive (fun k a b => drift k a - g k a b) T T ω
          ≤ historyAdditive h T T ω :=
      fun ω => historyAdditive_mono _ _ T T ω
        (fun k a b => h_step_descent k a b)
    have hsplit := historyAdditive_drift_sub drift g T T
    have hfloor : ∀ ω : History α T,
        (T : ℝ) * γ ≤ driftAdditive drift T T ω := by
      intro ω
      unfold driftAdditive
      simp only [Nat.min_self]
      calc (T : ℝ) * γ = ∑ _j ∈ Finset.range T, γ := by
            rw [Finset.sum_const, Finset.card_range]; simp
        _ ≤ _ := Finset.sum_le_sum
          fun j _ => h_drift_floor j (ω (historyIndex T j))
    have hcover : ∀ ω : History α T,
        historyAdditive g T T ω ≤ r →
        T * γ - r ≤ historyAdditive h T T ω := by
      intro ω hSr
      have h1 := hmono ω
      rw [hsplit ω] at h1
      have h2 := hfloor ω
      linarith
    set v : ℕ → α → ℝ :=
      fun k a => min (pmfMean (K k a) (fun b => g k a b ^ 2)) σ with hv
    have hvarv : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
        pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a := by
      intro k _ a ha
      exact le_min_iff.mpr ⟨le_rfl, h_noise_cond_var k (by omega) a ha⟩
    have hVpos : (0 : ℝ) < (T : ℝ) * σ := by
      by_contra hcon
      push_neg at hcon
      have hle : c * r ≤ 0 := by linarith [hrc]
      have h1 : 0 < c * r := by positivity
      linarith
    have htail := freedman_variance_radius initial K g v T c hc
      h_noise_bounded h_noise_cond_mean hvarv T r ((T : ℝ) * σ) hr hVpos hrc
    have hcongr : pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0)
        = pmfMean (historyLaw initial K T T)
          (fun ω => if r ≤ historyAdditive g T T ω
            ∧ historyCounter v T T ω ≤ (T : ℝ) * σ then 1 else 0) := by
      apply pmfMean_congr
      intro ω _
      have hcb := historyCounter_var_le K g T T σ ω
      rw [← hv, Nat.min_self] at hcb
      simp [hcb]
    rw [← hcongr] at htail
    have hpt1 : ∀ ω : History α T,
        (if T * γ - r ≤ historyAdditive h T T ω then (1 : ℝ) else 0)
          ≥ (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0) := by
      intro ω
      by_cases hS : historyAdditive g T T ω ≤ r
      · have hcov := hcover ω hS
        simp [hcov, hS]
      · simp only [hS, ite_false, ge_iff_le]
        split_ifs <;> norm_num
    have hev1 : pmfMean (historyLaw initial K T T)
        (fun ω => if T * γ - r ≤ historyAdditive h T T ω then 1 else 0)
        ≥ pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0) :=
      pmfMean_mono _ (fun ω _ => hpt1 ω)
    have hswitch : pmfMean (historyLaw initial K T T)
        (fun ω => if historyAdditive g T T ω ≤ r then 1 else 0)
        ≥ 1 - pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω then 1 else 0) := by
      have hpt2 : ∀ ω : History α T,
          (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
          + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0) ≥ 1 := by
        intro ω
        by_cases hS : historyAdditive g T T ω ≤ r
        · by_cases hrS : r ≤ historyAdditive g T T ω <;>
            simp [hS, hrS]
        · have hrS : r ≤ historyAdditive g T T ω :=
            (not_le.mp hS).le
          simp [hS, hrS]
      have hsum : pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0))
          = pmfMean (historyLaw initial K T T)
              (fun ω => if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + pmfMean (historyLaw initial K T T)
              (fun ω => if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0) :=
        pmfMean_add _ _ _
      have hge : (1 : ℝ) ≤ pmfMean (historyLaw initial K T T)
          (fun ω => (if historyAdditive g T T ω ≤ r then (1 : ℝ) else 0)
            + (if r ≤ historyAdditive g T T ω then (1 : ℝ) else 0)) :=
        le_trans (le_of_eq (pmfMean_const (historyLaw initial K T T) 1).symm)
          (pmfMean_mono (historyLaw initial K T T) (fun ω _ => hpt2 ω))
      rw [hsum] at hge
      linarith
    linarith

/-- Обёртка-сертификат: variance-форма моста в форме
`CertStochasticStep`; failure = exp(−r²/(4·T·σ)) в режиме
c·r ≤ 2·T·σ. -/
noncomputable def stochastic_safe_step_variance (initial : PMF α)
    (K : ℕ → α → PMF α)
    (T : ℕ) (hT : 0 < T) (γ c σ r : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hσ : 0 ≤ σ) (hr : 0 < r)
    (hrc : c * r ≤ 2 * ((T : ℝ) * σ))
    (hdrop : r < T * γ)
    (h g : ℕ → α → α → ℝ) (drift : ℕ → α → ℝ)
    (h_noise_bounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (h_noise_cond_mean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (h_noise_cond_var : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ σ)
    (h_step_descent : ∀ k a b, drift k a - g k a b ≤ h k a b)
    (h_drift_floor : ∀ k a, γ ≤ drift k a) :
    CertStochasticStep (historyLaw initial K T T)
      (historyAdditive h T T) where
  drop := T * γ - r
  drop_pos := by
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    linarith
  failure := Real.exp (-r ^ 2 / (4 * ((T : ℝ) * σ)))
  descent_whp := stochastic_safe_step_variance_whp initial K T hT γ c σ r
    hγ hc hσ hr hrc hdrop h g drift h_noise_bounded h_noise_cond_mean
    h_noise_cond_var h_step_descent h_drift_floor

end

section stochasticSafeStep
open scoped BigOperators
open Set

variable {α : Type*} [Fintype α]

/-! ## Bennett-chord Freedman — полная форма r²/(2(V+c·r/3))

Убирает пины MGF-константа 1 и
отсутствие λ-оптимизации. Ядро — хорда Беннетта (доказана
из принципа: Mathlib такой
леммы не содержит):
для x ∈ [0,3): exp x − 1 − x ≤ x²/(2(1−x/3)). -/

/-- Первый шаг цепочки: eˣ·(1−x) ≤ 1 при x ≥ 0
(производная −x·eˣ ≤ 0). -/
theorem exp_mul_one_sub_le_one (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x * (1 - x) ≤ 1 := by
  have hn : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.exp u * (1 - u))
      (- t * Real.exp t) t := by
    intro t
    have h := (Real.hasDerivAt_exp t).mul
      ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
    change Real.exp t * (1 - t) + Real.exp t * (0 - 1) = -t * Real.exp t
    ring
  have hdo : DifferentiableOn ℝ (fun t => Real.exp t * (1 - t)) (Ici 0) :=
    fun t _ => (hn t).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun t => Real.exp t * (1 - t)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ)) hdo.continuousOn ?_ ?_
    · intro t _
      exact (hn t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      rw [(hn t).deriv]
      nlinarith [ht0, Real.exp_pos t]
  have h0 : (fun t : ℝ => Real.exp t * (1 - t)) 0 = 1 := by norm_num
  calc (fun t : ℝ => Real.exp t * (1 - t)) x
      ≤ (fun t : ℝ => Real.exp t * (1 - t)) 0 :=
        hanti (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx
    _ = 1 := h0

/-- Второй шаг: eˣ·(2−x) − (2+x) ≤ 0 при x ≥ 0. -/
theorem exp_mul_two_sub_le (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x * (2 - x) - (2 + x) ≤ 0 := by
  have hm : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Real.exp u * (2 - u) - (2 + u))
      (Real.exp t * (1 - t) - 1) t := by
    intro t
    have h := ((Real.hasDerivAt_exp t).mul
      ((hasDerivAt_const t (2:ℝ)).sub (hasDerivAt_id t))).sub
      ((hasDerivAt_const t (2:ℝ)).add (hasDerivAt_id t))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
    change Real.exp t * (2 - t) + Real.exp t * (0 - 1) - (0 + 1)
      = Real.exp t * (1 - t) - 1
    ring
  have hdo : DifferentiableOn ℝ (fun t => Real.exp t * (2 - t) - (2 + t))
      (Ici 0) := fun t _ => (hm t).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun t => Real.exp t * (2 - t) - (2 + t)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ)) hdo.continuousOn ?_ ?_
    · intro t _
      exact (hm t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      rw [(hm t).deriv]
      exact sub_nonpos.mpr (exp_mul_one_sub_le_one t ht0)
  have h0 : (fun t : ℝ => Real.exp t * (2 - t) - (2 + t)) 0 = 0 := by norm_num
  calc (fun t : ℝ => Real.exp t * (2 - t) - (2 + t)) x
      ≤ (fun t : ℝ => Real.exp t * (2 - t) - (2 + t)) 0 :=
        hanti (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx
    _ = 0 := h0

/-- **Хорда Беннетта** (ядро): для 0 ≤ x < 3,
exp x − 1 − x ≤ x²/(2·(1 − x/3)). Доказательство: h(x) :=
(1−x/3)·(eˣ−1−x) − x²/2 антиубывает на [0,∞) (h' = m/3, m
антиубывает по `exp_mul_two_sub_le`), h(0) = 0; деление на
1 − x/3 > 0. -/
theorem exp_le_chord_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx3 : x < 3) :
    Real.exp x - 1 - x ≤ x ^ 2 / (2 * (1 - x / 3)) := by
  have hh : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => (1 - u / 3) * (Real.exp u - 1 - u)
        - u ^ 2 / 2)
      ((Real.exp t * (2 - t) - (2 + t)) / 3) t := by
    intro t
    have ha : HasDerivAt (fun u : ℝ => 1 - u / 3) _ t :=
      (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const (3:ℝ))
    have hb : HasDerivAt (fun u : ℝ => Real.exp u - 1 - u) _ t :=
      ((Real.hasDerivAt_exp t).sub (hasDerivAt_const t (1:ℝ))).sub
        (hasDerivAt_id t)
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) _ t := (hasDerivAt_id t).pow 2
    have h := ((ha.mul hb).sub (hsq.div_const (2:ℝ)))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
    norm_num
    ring
  have hdo : DifferentiableOn ℝ (fun t => (1 - t / 3) * (Real.exp t - 1 - t)
      - t ^ 2 / 2) (Ici 0) :=
    fun t _ => (hh t).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn (fun t => (1 - t / 3) * (Real.exp t - 1 - t)
      - t ^ 2 / 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ)) hdo.continuousOn ?_ ?_
    · intro t _
      exact (hh t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      rw [(hh t).deriv]
      have hml := exp_mul_two_sub_le t ht0
      nlinarith [hml]
  have hle : (1 - x / 3) * (Real.exp x - 1 - x) - x ^ 2 / 2 ≤ 0 := by
    simpa using hanti (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx0) hx0
  have hden : 0 < 1 - x / 3 := by
    have h1 : x / 3 < 1 := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
      linarith
    linarith
  have key : (1 - x / 3) * (Real.exp x - 1 - x) ≤ x ^ 2 / 2 := by linarith
  have h2d : 0 < 2 * (1 - x / 3) := by linarith
  rw [le_div_iff₀ h2d]
  nlinarith [key, hden]

/-- Отрицательная ветвь: при x ≤ 0, exp x ≤ 1 + x + x²/2
(Тейлор с остатком, e^ξ ≤ 1; через монотонность w' = eˣ−1−x ≥ 0
по `Real.add_one_le_exp`). -/
theorem exp_le_quad_of_nonpos (x : ℝ) (hx : x ≤ 0) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 := by
  have hw : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp u - 1 - u - u ^ 2 / 2)
        (Real.exp t - 1 - t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => Real.exp u - 1 - u) _ t :=
      ((Real.hasDerivAt_exp t).sub (hasDerivAt_const t (1:ℝ))).sub
        (hasDerivAt_id t)
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) _ t := (hasDerivAt_id t).pow 2
    have h := h1.sub (hsq.div_const (2:ℝ))
    refine (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))).congr_deriv ?_
    norm_num
  have hdo : DifferentiableOn ℝ (fun t => Real.exp t - 1 - t - t ^ 2 / 2)
      (Iic 0) := fun t _ => (hw t).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun t => Real.exp t - 1 - t - t ^ 2 / 2) (Iic 0) :=
    monotoneOn_of_deriv_nonneg (convex_Iic (0:ℝ)) hdo.continuousOn
      (fun t _ => (hw t).differentiableAt.differentiableWithinAt)
      (by intro t _
          rw [(hw t).deriv]
          have hben := Real.add_one_le_exp t
          linarith)
  have h0 : (fun t : ℝ => Real.exp t - 1 - t - t ^ 2 / 2) 0 = 0 := by norm_num
  have hle := hmono (mem_Iic.mpr hx) (mem_Iic.mpr (le_refl 0)) hx
  simpa using hle

/-- **MGF с хордой Беннетта**: при 0 ≤ c, |X| ≤ c, E X ≤ 0,
E X² ≤ v, 0 ≤ λ и λ·c < 3 (строго — знаменатель хорды положителен):
E[exp(λX)] ≤ exp(λ²·v/(2(1−λc/3))). Заменяет константу 1 леммы
`pmfMean_exp_le` на хордовый коэффициент 1/(2(1−λc/3)) — это и
есть Bennett-ускорение. -/
theorem pmfMean_exp_chord_le (p : PMF α)
    (X : α → ℝ) (c v lam : ℝ) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hclam : lam * c < 3)
    (hbounded : ∀ a ∈ p.support, |X a| ≤ c)
    (hmean : pmfMean p X ≤ 0)
    (hvar : pmfMean p (fun a => X a ^ 2) ≤ v) :
    pmfMean p (fun a => Real.exp (lam * X a))
      ≤ Real.exp (lam ^ 2 * v / (2 * (1 - lam * c / 3))) := by
  have hden : 0 < 1 - lam * c / 3 := by
    have h1 : lam * c / 3 < 1 := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
      linarith [hclam]
    linarith
  have hpt (a : α) (ha : a ∈ p.support) :
      Real.exp (lam * X a) ≤ 1 + lam * X a
        + lam ^ 2 / (2 * (1 - lam * c / 3)) * X a ^ 2 := by
    by_cases hx : 0 ≤ lam * X a
    · have hxlc : lam * X a ≤ lam * c :=
        calc lam * X a ≤ |lam * X a| := le_abs_self _
          _ = |lam| * |X a| := abs_mul lam (X a)
          _ = lam * |X a| := by rw [abs_of_nonneg hlam]
          _ ≤ lam * c := mul_le_mul_of_nonneg_left
            (hbounded a ha) hlam
      have hx3 : lam * X a < 3 := lt_of_le_of_lt hxlc hclam
      have hchord := exp_le_chord_nonneg (lam * X a) hx hx3
      have hdenx : 0 < 2 * (1 - lam * X a / 3) := by
        have hdiv : lam * X a / 3 ≤ lam * c / 3 :=
          div_le_div_of_nonneg_right hxlc (by norm_num : (0:ℝ) ≤ 3)
        nlinarith [hden]
      have hdenc : 0 < 2 * (1 - lam * c / 3) := by nlinarith [hden]
      have hdenle : 2 * (1 - lam * c / 3) ≤ 2 * (1 - lam * X a / 3) := by
        have hdiv : lam * X a / 3 ≤ lam * c / 3 :=
          div_le_div_of_nonneg_right hxlc (by norm_num : (0:ℝ) ≤ 3)
        linarith
      have hx2 : 0 ≤ (lam * X a) ^ 2 := sq_nonneg _
      have hstep2 : (lam * X a) ^ 2 / (2 * (1 - lam * X a / 3))
          ≤ (lam * X a) ^ 2 / (2 * (1 - lam * c / 3)) := by
        rw [div_le_div_iff₀ hdenx hdenc]
        nlinarith [hdenle, hx2]
      have hfin := hchord.trans hstep2
      have hring : (lam * X a) ^ 2 / (2 * (1 - lam * c / 3))
          = lam ^ 2 / (2 * (1 - lam * c / 3)) * X a ^ 2 := by
        field_simp
      rw [hring] at hfin
      linarith
    · have hnlt : lam * X a < 0 := lt_of_not_ge hx
      have hnq := exp_le_quad_of_nonpos (lam * X a) (le_of_lt hnlt)
      have hdenc : 0 < 2 * (1 - lam * c / 3) := by nlinarith [hden]
      have hco : lam ^ 2 / 2
          ≤ lam ^ 2 / (2 * (1 - lam * c / 3)) := by
        have hdd : 2 * (1 - lam * c / 3) ≤ 2 * 1 := by
          have hlc0 : 0 ≤ lam * c := mul_nonneg hlam hc
          nlinarith [hden]
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hdenc]
        nlinarith [hdd, sq_nonneg lam]
      have hsq : (lam * X a) ^ 2 = lam ^ 2 * X a ^ 2 := by ring
      rw [hsq] at hnq
      nlinarith [hnq, hco, sq_nonneg (X a)]
  calc pmfMean p (fun a => Real.exp (lam * X a))
      ≤ pmfMean p (fun a => 1 + lam * X a
        + lam ^ 2 / (2 * (1 - lam * c / 3)) * X a ^ 2) :=
        pmfMean_mono p hpt
    _ = 1 + lam * pmfMean p X
        + lam ^ 2 / (2 * (1 - lam * c / 3))
          * pmfMean p (fun a => X a ^ 2) := by
        rw [pmfMean_add, pmfMean_add, pmfMean_const, pmfMean_const_mul,
          pmfMean_const_mul]
    _ ≤ 1 + lam * pmfMean p X
        + lam ^ 2 / (2 * (1 - lam * c / 3)) * v := by
        have hs := mul_le_mul_of_nonneg_left hmean hlam
        have hv := mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
        have hk : lam ^ 2 / (2 * (1 - lam * c / 3)) * v
            ≥ lam ^ 2 / (2 * (1 - lam * c / 3))
              * pmfMean p (fun a => X a ^ 2) :=
          mul_le_mul_of_nonneg_left hvar (by
            have hd2 : 0 < 2 * (1 - lam * c / 3) := by nlinarith [hden]
            apply div_nonneg (sq_nonneg lam) hd2.le)
        linarith
    _ ≤ Real.exp (lam ^ 2 / (2 * (1 - lam * c / 3)) * v) := by
        have h2 := Real.add_one_le_exp
          (lam ^ 2 / (2 * (1 - lam * c / 3)) * v)
        have hs := mul_le_mul_of_nonneg_left hmean hlam
        linarith
    _ = Real.exp (lam ^ 2 * v / (2 * (1 - lam * c / 3))) := by
        rw [div_mul_eq_mul_div]


/-- **Chord-compensated суперmartingale**: при
ограниченном шуме (|g| ≤ c, 0 ≤ c), нулевом условном среднем и
условной дисперсии ≤ v, для λ ≥ 0 с λ·c < 3 экспоненциальный
потенциал exp(λ·S_k − (λ²/(2(1−λc/3)))·C_k) — суперmartingale:
его среднее по historyLaw ≤ 1. Зеркало
`history_exp_compensated_le` с хордовым коэффициентом вместо 1. -/
theorem history_exp_chord_compensated_le (initial : PMF α)
    (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hclam : lam * c < 3)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) :
    pmfMean (historyLaw initial K T k)
      (fun ω => Real.exp (lam * historyAdditive g T k ω
        - lam ^ 2 / (2 * (1 - lam * c / 3))
          * historyCounter v T k ω)) ≤ 1 := by
  classical
  set F : ℕ → History α T → ℝ := fun j ω =>
    Real.exp (lam * historyAdditive g T j ω
      - lam ^ 2 / (2 * (1 - lam * c / 3))
        * historyCounter v T j ω) with hF
  have hone : ∀ j : ℕ, ∀ ω : History α T,
      ω ∈ (historyLaw initial K T j).support →
      pmfMean (historyKernel K T j ω) (F (j + 1)) ≤ F j ω := by
    intro j ω hω
    by_cases hj : j < T
    · rw [historyKernel, ite_eq_left hj, pmfMean_map]
      have hsupp := historyLaw_current_support initial K T j hj.le ω hω
      have hfac : ∀ b : α, F (j + 1)
          (Function.update ω (historyIndex T (j + 1)) b)
          = F j ω * Real.exp (lam * g j (ω (historyIndex T j)) b
              - lam ^ 2 / (2 * (1 - lam * c / 3))
                * v j (ω (historyIndex T j))) := by
        intro b
        simp only [hF]
        rw [historyAdditive_update g T j hj, historyCounter_update v T j hj,
          ← Real.exp_add]
        congr 1
        ring
      simp_rw [hfac]
      rw [pmfMean_const_mul]
      have hmgf := pmfMean_exp_chord_le (K j (ω (historyIndex T j)))
        (fun b => g j (ω (historyIndex T j)) b) c
        (v j (ω (historyIndex T j))) lam hc hlam hclam
        (fun b hb => hbounded j hj _ hsupp b hb)
        (by rw [← hmean j hj _ hsupp])
        (hvar j hj _ hsupp)
      rw [← div_mul_eq_mul_div] at hmgf
      have hsplit : pmfMean (K j (ω (historyIndex T j)))
          (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b
            - lam ^ 2 / (2 * (1 - lam * c / 3))
              * v j (ω (historyIndex T j))))
          = Real.exp (- lam ^ 2 / (2 * (1 - lam * c / 3))
              * v j (ω (historyIndex T j)))
            * pmfMean (K j (ω (historyIndex T j)))
              (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)) := by
        rw [← pmfMean_const_mul]
        apply pmfMean_congr
        intro b _
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hstep1 : F j ω * (Real.exp (- lam ^ 2 / (2 * (1 - lam * c / 3))
          * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (- lam ^ 2 / (2 * (1 - lam * c / 3))
            * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 / (2 * (1 - lam * c / 3))
              * v j (ω (historyIndex T j)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmgf
                (by positivity : (0 : ℝ) ≤ Real.exp
                  (- lam ^ 2 / (2 * (1 - lam * c / 3))
                    * v j (ω (historyIndex T j)))))
              (by positivity : (0 : ℝ) ≤ F j ω)
      calc F j ω * (Real.exp (- lam ^ 2 / (2 * (1 - lam * c / 3))
          * v j (ω (historyIndex T j)))
          * pmfMean (K j (ω (historyIndex T j)))
            (fun b => Real.exp (lam * g j (ω (historyIndex T j)) b)))
          ≤ F j ω * (Real.exp (- lam ^ 2 / (2 * (1 - lam * c / 3))
            * v j (ω (historyIndex T j)))
            * Real.exp (lam ^ 2 / (2 * (1 - lam * c / 3))
              * v j (ω (historyIndex T j)))) := hstep1
      _ = F j ω := by
            rw [← Real.exp_add]
            have hzero : -lam ^ 2 / (2 * (1 - lam * c / 3))
                * v j (ω (historyIndex T j))
                + lam ^ 2 / (2 * (1 - lam * c / 3))
                  * v j (ω (historyIndex T j)) = 0 := by
              ring
            rw [hzero, Real.exp_zero, mul_one]
    · rw [historyKernel, ite_eq_right (by omega : ¬ j < T), pmfMean_pure]
      simp only [hF]
      rw [historyAdditive_frozen g T j (by omega : T ≤ j),
        historyCounter_frozen v T j (by omega : T ≤ j)]
  induction k with
  | zero => simp
  | succ k ih =>
      have hunfold : pmfMean (historyLaw initial K T (k + 1)) (F (k + 1))
          = pmfMean (historyLaw initial K T k)
            (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1))) := by
        change pmfMean ((historyLaw initial K T k).bind
          (historyKernel K T k)) (F (k + 1)) = _
        rw [pmfMean_bind]
      rw [hunfold]
      have hzero : pmfMean (historyLaw initial K T k)
          (fun ω => pmfMean (historyKernel K T k ω) (F (k + 1)))
          = pmfMean (historyLaw initial K T k)
            (fun ω => if ω ∈ (historyLaw initial K T k).support
              then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0) := by
        apply pmfMean_congr
        intro ω hω
        simp [hω]
      rw [hzero]
      have hmono : pmfMean (historyLaw initial K T k)
          (fun ω => if ω ∈ (historyLaw initial K T k).support
            then pmfMean (historyKernel K T k ω) (F (k + 1)) else 0)
          ≤ pmfMean (historyLaw initial K T k) (F k) := by
            apply pmfMean_mono
            intro ω _
            by_cases hω : ω ∈ (historyLaw initial K T k).support
            · simpa [hω] using hone k ω hω
            · simp [hω]; positivity
      have hFk : pmfMean (historyLaw initial K T k) (F k)
          = pmfMean (historyLaw initial K T k)
            (fun ω => Real.exp (lam * historyAdditive g T k ω
              - lam ^ 2 / (2 * (1 - lam * c / 3))
                * historyCounter v T k ω)) := by
            rfl
      exact hmono.trans (hFk.trans_le ih)

/-- Хвостовая лемма с общим компенсаторным коэффициентом μ ≥ 0
(обобщение `pmfMean_compensated_tail` на случай exp(λX − μV)
с μ ≠ λ²). -/
theorem pmfMean_chord_tail {α : Type*} [Fintype α] (p : PMF α)
    (X V : α → ℝ) (lam mu r v : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hmgf : pmfMean p (fun a => Real.exp (lam * X a - mu * V a)) ≤ 1) :
    pmfMean p (fun a => if r ≤ X a ∧ V a ≤ v then 1 else 0) ≤
      Real.exp (-lam * r + mu * v) := by
  classical
  have hevent (a : α) :
      (if r ≤ X a ∧ V a ≤ v then (1 : ℝ) else 0) ≤
        Real.exp (lam * X a - mu * V a) * Real.exp (-lam * r + mu * v) := by
    split_ifs with ha
    · rw [← Real.exp_add, Real.one_le_exp_iff]
      have hx := mul_le_mul_of_nonneg_left ha.1 hlam
      have hv := mul_le_mul_of_nonneg_left ha.2 hmu
      linarith
    · positivity
  calc
    _ ≤ pmfMean p (fun a =>
        Real.exp (lam * X a - mu * V a) * Real.exp (-lam * r + mu * v)) :=
      pmfMean_mono p (fun a _ => hevent a)
    _ = pmfMean p (fun a => Real.exp (lam * X a - mu * V a)) *
        Real.exp (-lam * r + mu * v) := pmfMean_mul_const _ _ _
    _ ≤ 1 * Real.exp (-lam * r + mu * v) :=
      mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
    _ = _ := one_mul _

/-- **Fixed-λ chord-хвост**: для λ ≥ 0 с λ·c < 3
и детерминированного порога V ≥ 0:
P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−λ·r + λ²·V/(2(1−λc/3))). -/
theorem history_variance_freedman_chord_lam (initial : PMF α)
    (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c lam : ℝ) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hclam : lam * c < 3)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0)
      ≤ Real.exp (-lam * r + lam ^ 2 * V / (2 * (1 - lam * c / 3))) := by
  have h := pmfMean_chord_tail _ (historyAdditive g T k)
    (historyCounter v T k) lam (lam ^ 2 / (2 * (1 - lam * c / 3))) r V hlam
    (by
      have hden : 0 < 1 - lam * c / 3 := by
        have h1 : lam * c / 3 < 1 := by
          rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
          linarith [hclam]
        linarith
      exact div_nonneg (sq_nonneg lam)
        (by nlinarith [hden] : (0:ℝ) ≤ 2 * (1 - lam * c / 3)))
    (history_exp_chord_compensated_le initial K g v T c lam hc hlam hclam
      hbounded hmean hvar k)
  rw [← div_mul_eq_mul_div]
  exact h

/-- **Полная форма Freedman** (ГЛАВНЫЙ): при ограниченном
центрированном шуме с условной дисперсией ≤ v, для r > 0, V > 0,
БЕЗ режимной посылки:
P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−r²/(2(V + c·r/3))).
λ-оптимизация λ = r/(V + cr/3) (λ·c < 3 автоматически при V > 0);
замыкает честные пины (MGF-константа 1, отсутствие
λ-оптимизации). -/
theorem freedman_full (initial : PMF α) (K : ℕ → α → PMF α)
    (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 < V) :
    pmfMean (historyLaw initial K T k)
      (fun ω => if r ≤ historyAdditive g T k ω ∧ historyCounter v T k ω ≤ V
        then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (2 * (V + c * r / 3))) := by
  set Vt : ℝ := V + c * r / 3 with hVt
  have hVtpos : 0 < Vt := by
    have hcr : 0 ≤ c * r := mul_nonneg hc hr.le
    have : 0 ≤ c * r / 3 := by positivity
    linarith
  set lam : ℝ := r / Vt with hlam_def
  have hlam : 0 ≤ lam := by rw [hlam_def]; apply div_nonneg hr.le hVtpos.le
  have hclam : lam * c < 3 := by
    have hstep : lam * c = (c * r) / Vt := by
      rw [hlam_def]
      field_simp
    rw [hstep, div_lt_iff₀ hVtpos]
    have hcr : 0 ≤ c * r := mul_nonneg hc hr.le
    have hVt3 : 3 * Vt = 3 * V + c * r := by ring
    nlinarith
  have htail := history_variance_freedman_chord_lam initial K g v T c lam
    hc hlam hclam hbounded hmean hvar k r V hr hV.le
  have hkey : 1 - lam * c / 3 = V / Vt := by
    rw [hlam_def]
    field_simp
    ring
  have hexp1 : -lam * r + lam ^ 2 * V / (2 * (1 - lam * c / 3))
      = -r ^ 2 / (2 * Vt) := by
    rw [hkey, hlam_def]
    field_simp
    ring
  rw [hexp1, hVt] at htail
  exact htail

/-- **Сравнение с mixed-формой **: полная
форма ≤ mixed-формы exp(−r²/(4(V+c·r))) при r ≥ 0, c ≥ 0, V ≥ 0 —
константы 4 → 2 и c·r → c·r/3, БЕЗ режимной посылки. Равенство
только при c·r = 0. -/
theorem freedman_full_exp_le_mixed_exp (r V c : ℝ) (hr : 0 < r)
    (hV : 0 ≤ V) (hc : 0 < c) :
    Real.exp (-r ^ 2 / (2 * (V + c * r / 3)))
      ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  apply Real.exp_le_exp.mpr
  have hcr : 0 < c * r := mul_pos hc hr
  have hnn : 0 ≤ r ^ 2 := sq_nonneg r
  have h4 : (0:ℝ) < 4 * (V + c * r) := by
    have : 0 < V + c * r := by linarith
    positivity
  have h2 : (0:ℝ) < 2 * (V + c * r / 3) := by
    have : 0 ≤ V + c * r / 3 := by
      have : 0 ≤ c * r / 3 := by positivity
      linarith
    positivity
  rw [div_le_div_iff₀ h2 h4]
  nlinarith [hcr, hnn]

/-- **Режимное сравнение с variance-формой ** (честность):
при c·r/3 ≤ V полная форма не хуже variance-радиуса
exp(−r²/(4V)); при V ≤ c·r/3 наоборот — формы несравнимы
глобально, режимная посылка явная. -/
theorem freedman_full_exp_le_variance_exp (r V c : ℝ) (hr : 0 < r)
    (hV : 0 < V) (hc : 0 ≤ c) (hrc : c * r / 3 ≤ V) :
    Real.exp (-r ^ 2 / (2 * (V + c * r / 3)))
      ≤ Real.exp (-r ^ 2 / (4 * V)) := by
  apply Real.exp_le_exp.mpr
  have hnn : 0 ≤ r ^ 2 := sq_nonneg r
  have h4 : (0:ℝ) < 4 * V := by positivity
  have h2 : (0:ℝ) < 2 * (V + c * r / 3) := by
    have : 0 ≤ c * r / 3 := by positivity
    have : 0 ≤ V + c * r / 3 := by linarith
    positivity
  rw [div_le_div_iff₀ h2 h4]
  nlinarith [hnn, hrc]

/-- Обратное режимное сравнение: при V ≤ c·r/3
variance-радиус exp(−r²/(4V)) не хуже полной формы. -/
theorem freedman_variance_exp_le_full_exp (r V c : ℝ) (hr : 0 < r)
    (hV : 0 < V) (hc : 0 < c) (hvr : V ≤ c * r / 3) :
    Real.exp (-r ^ 2 / (4 * V))
      ≤ Real.exp (-r ^ 2 / (2 * (V + c * r / 3))) := by
  apply Real.exp_le_exp.mpr
  have hnn : 0 ≤ r ^ 2 := sq_nonneg r
  have h4 : (0:ℝ) < 4 * V := by positivity
  have h2 : (0:ℝ) < 2 * (V + c * r / 3) := by
    have hcr : 0 < c * r := mul_pos hc hr
    have : 0 ≤ c * r / 3 := by positivity
    have : 0 < V + c * r / 3 := by linarith
    positivity
  rw [div_le_div_iff₀ h4 h2]
  nlinarith [hnn, hvr]

end stochasticSafeStep

end Hagi.Probability
set_option linter.style.header false

/-!
# Freedman для адаптированных дисперсий — история-зависимое q

В `freedman_tail_low` условное
распределение шага — один и тот же вектор q для каждого шага и
каждого префикса, σ — константа. Здесь оба ограничения сняты
на конечной prodPq-машине (Markov-kernel-форма `freedman_full` уже
adapted; здесь — конечный формализм, потребляемый success-теоремами):

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
  строго сильнее σ = 1-хвоста exp(−Δ²/(2(n+Δ))).

**Честные границы**: b — константа (диапазон приращений общий
для шагов); anytime-форма и data-зависимый λ — открыто и здесь
(на Markov-машине anytime-форма есть: `anytime_freedman_thresholds`);
случай V = 0 не выписан
(требуем 0 < V, как 0 < sig у `freedman_tail_low`).
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

Хвост строго сильнее σ = 1-версии
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
      simpa using congrArg (fun pI => S (t + 1) pI
        - m t (Fin.init (α := fun _ => V) pI))
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

/-!
# Fixed-terminal Freedman confidence for a fixed finite family

The probability input is the existing finite Markov history law.  The two-sided
fixed-terminal tail is obtained from `history_additive_freedman` at `k = T` on
`g` and `-g`; the family estimate is one union bound over a pre-fixed finset.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FreedmanFamilyConfidence

open Hagi.Probability
open scoped BigOperators

private theorem historyAdditive_neg {α : Type*}
    (g : ℕ → α → α → ℝ) (T k : ℕ) (ω : History α T) :
    historyAdditive (fun k a b => -g k a b) T k ω = -historyAdditive g T k ω := by
  unfold historyAdditive
  rw [← Finset.sum_neg_distrib]

private theorem history_additive_freedman_two_sided_fixed
    {α : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (g : ℕ → α → α → ℝ) (v : ℕ → α → ℝ)
    (T : ℕ) (c : ℝ) (hc : 0 < c)
    (hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g k a b| ≤ c)
    (hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g k a) = 0)
    (hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a)
    (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
        then 1 else 0) ≤ 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
  classical
  have hbounded_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support,
        |(fun k a b => -g k a b) k a b| ≤ c := by
    intro k hk a ha b hb
    exact (abs_neg (g k a b)).le.trans (hbounded k hk a ha b hb)
  have hmean_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) ((fun k a b => -g k a b) k a) = 0 := by
    intro k hk a ha
    have h := pmfMean_const_mul (K k a) (-1) (g k a)
    rw [hmean k hk a ha, mul_zero] at h
    simpa only [neg_one_mul] using h
  have hvar_neg : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => ((fun k a b => -g k a b) k a b) ^ 2) ≤ v k a := by
    intro k hk a ha
    have hsq : pmfMean (K k a) (fun b => (-(g k a b)) ^ 2) =
        pmfMean (K k a) (fun b => (g k a b) ^ 2) :=
      pmfMean_congr (K k a) (fun b _ => neg_sq (g k a b))
    exact hsq.le.trans (hvar k hk a ha)
  have hpos := history_additive_freedman initial K g v T c hc
    hbounded hmean hvar T r V hr hV
  have hneg := history_additive_freedman initial K
    (fun k a b => -g k a b) v T c hc hbounded_neg hmean_neg hvar_neg T r V hr hV
  have hsplit : pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
        then 1 else 0) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω =>
          (if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
            then (1 : ℝ) else 0) +
          (if r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
            then (1 : ℝ) else 0)) := by
    apply pmfMean_mono
    intro ω _
    by_cases hbad : r ≤ |historyAdditive g T T ω| ∧ historyCounter v T T ω ≤ V
    · rw [ite_eq_left hbad]
      by_cases hpos : r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
      · rw [ite_eq_left hpos]
        exact le_add_of_nonneg_right (by positivity)
      · have hneg' : r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V := by
          refine ⟨?_, hbad.2⟩
          have hslt : historyAdditive g T T ω < r := lt_of_not_ge (fun h => hpos ⟨h, hbad.2⟩)
          by_contra hcon
          have hcon' : -historyAdditive g T T ω < r := lt_of_not_ge hcon
          have habslt : |historyAdditive g T T ω| < r :=
            abs_lt.mpr ⟨by linarith, hslt⟩
          linarith
        rw [ite_eq_right hpos, ite_eq_left hneg']
        norm_num
    · rw [ite_eq_right hbad]
      positivity
  have hsum : pmfMean (historyLaw initial K T T)
      (fun ω =>
        (if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then (1 : ℝ) else 0) +
        (if r ≤ -historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then (1 : ℝ) else 0)) =
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive g T T ω ∧ historyCounter v T T ω ≤ V
          then 1 else 0) +
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ historyAdditive (fun k a b => -g k a b) T T ω ∧
          historyCounter v T T ω ≤ V then 1 else 0) := by
    rw [pmfMean_add]
    congr 1
    apply pmfMean_congr
    intro ω _
    rw [historyAdditive_neg]
  calc
    _ ≤ _ := hsplit
    _ = _ := hsum
    _ ≤ Real.exp (-r ^ 2 / (4 * (V + c * r))) +
        Real.exp (-r ^ 2 / (4 * (V + c * r))) := add_le_add hpos hneg
    _ = 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by ring

private theorem pmfMean_compl_indicator_lower_bound
    {α : Type*} [Fintype α] (p : PMF α) (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good] (bound : ℝ)
    (hcompl : ∀ ω, Good ω ↔ ¬Bad ω)
    (hbad : pmfMean p (fun ω => if Bad ω then 1 else 0) ≤ bound) :
    1 - bound ≤ pmfMean p (fun ω => if Good ω then 1 else 0) := by
  classical
  have heq : pmfMean p (fun ω => if Good ω then 1 else 0) =
      1 - pmfMean p (fun ω => if Bad ω then 1 else 0) := by
    calc
      _ = pmfMean p (fun ω => (1 : ℝ) - (if Bad ω then 1 else 0)) := by
        apply pmfMean_congr
        intro ω _
        by_cases hB : Bad ω
        · have hG : ¬Good ω := fun h => (hcompl ω).mp h hB
          simp only [hB, hG, ite_true, ite_false]
          norm_num
        · have hG : Good ω := (hcompl ω).mpr hB
          simp only [hB, hG, ite_true, ite_false]
          norm_num
      _ = pmfMean p (fun _ => (1 : ℝ)) - pmfMean p (fun ω => if Bad ω then 1 else 0) :=
        pmfMean_sub p (fun _ => 1) (fun ω => if Bad ω then 1 else 0)
      _ = _ := by rw [pmfMean_const]
  rw [heq]
  linarith

/-- Simultaneous fixed-terminal two-sided Freedman confidence for a pre-fixed
finite family on the existing finite Markov history law. -/
theorem finite_family_freedman_confidence
    {α ι : Type*} [Fintype α]
    (initial : PMF α) (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (g : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (c r V : ℝ) (hc : 0 < c) (hr : 0 < r) (hV : 0 ≤ V)
    (hbounded : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      ∀ b ∈ (K k a).support, |g i k a b| ≤ c)
    (hmean : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (g i k a) = 0)
    (hvar : ∀ i ∈ s, ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
      pmfMean (K k a) (fun b => (g i k a b) ^ 2) ≤ v i k a) :
    1 - 2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))) ≤
      pmfMean (historyLaw initial K T T)
        (fun ω => if ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
          |historyAdditive (g i) T T ω| < r then 1 else 0) := by
  classical
  have htail (i : ι) (hi : i ∈ s) :
      pmfMean (historyLaw initial K T T)
        (fun ω => if r ≤ |historyAdditive (g i) T T ω| ∧
          historyCounter (v i) T T ω ≤ V then 1 else 0) ≤
        2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) :=
    history_additive_freedman_two_sided_fixed initial K (g i) (v i) T c hc
      (hbounded i hi) (hmean i hi) (hvar i hi) r V hr hV
  have hunion := pmfMean_event_union (historyLaw initial K T T) s
    (fun i ω => r ≤ |historyAdditive (g i) T T ω| ∧ historyCounter (v i) T T ω ≤ V)
  have hsum : (∑ i ∈ s, pmfMean (historyLaw initial K T T)
      (fun ω => if r ≤ |historyAdditive (g i) T T ω| ∧
        historyCounter (v i) T T ω ≤ V then 1 else 0)) ≤
      2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))) := by
    calc
      _ ≤ ∑ _i ∈ s, 2 * Real.exp (-r ^ 2 / (4 * (V + c * r))) :=
        Finset.sum_le_sum (fun i hi => htail i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcompl : ∀ ω : History α T,
      (∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
        |historyAdditive (g i) T T ω| < r) ↔
      ¬(∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
        historyCounter (v i) T T ω ≤ V) := by
    intro ω
    constructor
    · intro hgood ⟨i, hi, hradius, hcounter⟩
      exact (not_lt_of_ge hradius) (hgood i hi hcounter)
    · intro hgood i hi hcounter
      by_contra hradius
      exact hgood ⟨i, hi, le_of_not_gt hradius, hcounter⟩
  have hconf := pmfMean_compl_indicator_lower_bound (historyLaw initial K T T)
    (fun ω => ∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
      historyCounter (v i) T T ω ≤ V)
    (fun ω => ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (g i) T T ω| < r)
    (2 * (s.card : ℝ) * Real.exp (-r ^ 2 / (4 * (V + c * r))))
    hcompl (by
      apply le_trans ?_ hsum
      convert hunion using 1
      · apply congrArg (pmfMean (historyLaw initial K T T))
        funext ω
        split_ifs <;> rfl
      · apply Finset.sum_congr rfl
        intro i _
        apply congrArg (pmfMean (historyLaw initial K T T))
        funext ω
        split_ifs <;> rfl)
  refine hconf.trans_eq ?_
  apply pmfMean_congr
  intro ω _
  by_cases hbad : ∃ i ∈ s, r ≤ |historyAdditive (g i) T T ω| ∧
    historyCounter (v i) T T ω ≤ V
  · have hgood : ¬(∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (g i) T T ω| < r) := fun h => (hcompl ω).mp h hbad
    simp only [hgood, ite_false]
  · have _hgood := (hcompl ω).mpr hbad
    rfl

/-- On the simultaneous good event, the two selected counter guards transfer
an observed gap to the corresponding conditional-risk gap with loss `2 * r`. -/
theorem finite_family_selected_conditional_gap_of_good
    {α ι : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (f : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (b : ι) (σ : History α T → ι) (r V : ℝ) (ω : History α T)
    (hb : b ∈ s) (hσ : σ ω ∈ s)
    (hgood : ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
        T T ω| < r)
    (hbv : historyCounter (v b) T T ω ≤ V)
    (hσv : historyCounter (v (σ ω)) T T ω ≤ V) :
    (historyAdditive (fun k a next => f b (k + 1) a next) T T ω -
      historyAdditive (fun k a next => f (σ ω) (k + 1) a next) T T ω) - 2 * r ≤
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f b (k + 1) a next)) T T ω -
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f (σ ω) (k + 1) a next)) T T ω := by
  have hcenter (i : ι) :
      historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
          T T ω =
        historyAdditive (fun k a next => f i (k + 1) a next) T T ω -
        historyAdditive (fun k a _ =>
          pmfMean (K k a) (fun next => f i (k + 1) a next)) T T ω := by
    unfold historyAdditive
    rw [Finset.sum_sub_distrib]
  have hbc := abs_lt.mp (hgood b hb hbv)
  have hσc := abs_lt.mp (hgood (σ ω) hσ hσv)
  rw [hcenter b] at hbc
  rw [hcenter (σ ω)] at hσc
  linarith

/-- A strict observed baseline-minus-selected gap gives a strictly positive
conditional-risk gap on the existing simultaneous Good event. -/
theorem finite_family_selected_conditional_gap_pos_of_good
    {α ι : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (T : ℕ)
    (s : Finset ι) (f : ι → ℕ → α → α → ℝ) (v : ι → ℕ → α → ℝ)
    (b : ι) (σ : History α T → ι) (r V : ℝ) (ω : History α T)
    (hb : b ∈ s) (hσ : σ ω ∈ s)
    (hgood : ∀ i ∈ s, historyCounter (v i) T T ω ≤ V →
      |historyAdditive (fun k a next =>
        f i (k + 1) a next - pmfMean (K k a) (fun next => f i (k + 1) a next))
        T T ω| < r)
    (hbv : historyCounter (v b) T T ω ≤ V)
    (hσv : historyCounter (v (σ ω)) T T ω ≤ V)
    (hobserved : 2 * r <
      historyAdditive (fun k a next => f b (k + 1) a next) T T ω -
      historyAdditive (fun k a next => f (σ ω) (k + 1) a next) T T ω) :
    0 < historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f b (k + 1) a next)) T T ω -
      historyAdditive (fun k a _ =>
        pmfMean (K k a) (fun next => f (σ ω) (k + 1) a next)) T T ω := by
  have hgap := finite_family_selected_conditional_gap_of_good
    K T s f v b σ r V ω hb hσ hgood hbv hσv
  linarith

end Hagi.Probability.FreedmanFamilyConfidence
