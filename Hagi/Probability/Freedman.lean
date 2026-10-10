/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.Azuma
set_option linter.style.header false

/-!
# Freedman вместо Azuma — дисперсионная адаптация (§AF/§AX)

Азума мажорирует приращения диапазоном [−c, c]: хвост
exp(−Δ²/(2nc²)). Если типичный шаг МАЛ (дисперсия σ² ≪ c²),
Азума расточительна. Freedman (слот 4/T4 аудита-волны-3:
2609.37787 скалярная L∞-форма; 2607.18899 совместная форма)
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
  с вероятностью ≥ 1 − exp(−Δ²/(2(nσ² + Δ))). При σ² = 1
  в точности воспроизводит; при σ² < 1 хвост СИЛЬНЕЕ.

**Честные границы**: σ² — измеряемая посылка (условная
дисперсия при каждом префиксе — runtime-измерение, не следствие
iid); b — конструкторский диапазон приращений. Совместная форма
(M ≥ x И V ≤ v с предсказуемой V, 2607.18899) и anytime-форма
(∃t, 2606.31449) — открыто.
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
дисперсией σ² (Σ q·S² ≤ σ² при каждом префиксе — runtime-посылка,
сильнее [0,1]-грубости σ² = 1 в):

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

end Hagi.Probability

namespace Hagi
export Hagi.Probability (exp_tail_two freedman_lemma_prefix freedman_mgf freedman_tail_low cond_var_le_second adaptive_success_freedman)
end Hagi
