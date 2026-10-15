/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

open Finset Real Set

/-!
# Хорда экспоненты (R498)

Выпуклость e^{r*y} через ConvexOn.comp_linearMap даёт хорду:
e^{r*x} <= ((b-x)/(b-a)) e^{r a} + ((x-a)/(b-a)) e^{r b} для
x in [a,b], a < b. Базовый кирпич Hoeffding/Bennett CGF-оценок.
Процесс-урок: приоритет оператора `•` выше `/` — веса в smul
нужны в скобках: `((b - x) / (b - a)) • a`.
-/
theorem exp_chord {a b x : ℝ} (hab : a < b) (hxa : a ≤ x) (hxb : x ≤ b)
    (r : ℝ) :
    Real.exp (r * x)
      ≤ (b - x) / (b - a) * Real.exp (r * a)
        + (x - a) / (b - a) * Real.exp (r * b) := by
  have hc0 : ConvexOn ℝ (⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r) ⁻¹' univ)
      (Real.exp ∘ ⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)) :=
    convexOn_exp.comp_linearMap (LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)
  have hc : ConvexOn ℝ univ (fun y => Real.exp (r * y)) := by
    refine hc0.congr (fun y _ => ?_)
    simp [LinearMap.smulRight]
    ring
  have hmem1 : (a:ℝ) ∈ (univ : Set ℝ) := trivial
  have hmem2 : (b:ℝ) ∈ (univ : Set ℝ) := trivial
  have hw1 : (0:ℝ) ≤ (b - x) / (b - a) := by positivity
  have hw2 : (0:ℝ) ≤ (x - a) / (b - a) := by positivity
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    rw [← add_div]
    have hnum : b - x + (x - a) = b - a := by ring
    rw [hnum]
    exact div_self (by linarith : b - a ≠ 0)
  have hconv := hc.2 hmem1 hmem2 hw1 hw2 hsum
  -- hconv : exp (r * (w1 • a + w2 • b)) <= w1 • exp (r a) + w2 • exp (r b)
  have hcombo : ((b - x) / (b - a)) • (a:ℝ) + ((x - a) / (b - a)) • (b:ℝ) = x := by
    have hne : b - a ≠ 0 := by linarith
    rw [smul_eq_mul, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [show (b - x) * a + (x - a) * b = (b - a) * x from by ring]
    exact mul_div_cancel_left₀ x hne
  rw [hcombo] at hconv
  simpa using hconv

/-! ## Шаг Хёффдинга: взвешенное хордовое MGF (R499)

E_q e^{r(g - mu)} <= ((b-mu)/(b-a)) e^{r(a-mu)} + ((mu-a)/(b-a)) e^{r(b-mu)}:
хорда R498 суммируется с весами q, аффинные веса усредняются к
барицентру (sum q (b - g) = b - mu, sum q (g - a) = mu - a),
константы выносятся из сумм через mul_sum-коммутационный simp.
-/
theorem hoeffding_chord_mgf {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (a b : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (hab : a < b) (r : ℝ) :
    ∑ v : V, q v * Real.exp (r * (g v - ∑ x : V, q x * g x))
      ≤ (b - ∑ x : V, q x * g x) / (b - a) * Real.exp (r * (a - ∑ x : V, q x * g x))
        + (∑ x : V, q x * g x - a) / (b - a)
          * Real.exp (r * (b - ∑ x : V, q x * g x)) := by
  set μ := ∑ x : V, q x * g x with hμd
  -- per-vertex chord on [a - mu, b - mu]
  have hdev : ∀ v : V, (a - μ) ≤ (g v - μ) ∧ (g v - μ) ≤ (b - μ) := by
    intro v
    constructor <;> linarith [hlo v, hhi v]
  have hlt : a - μ < b - μ := by linarith
  -- sum the chord with weights
  have hchord : ∀ v : V, q v * Real.exp (r * (g v - μ))
      ≤ q v * ((b - μ - (g v - μ)) / (b - μ - (a - μ)) * Real.exp (r * (a - μ))
        + (g v - μ - (a - μ)) / (b - μ - (a - μ)) * Real.exp (r * (b - μ))) :=
    fun v => mul_le_mul_of_nonneg_left
      (exp_chord (a := a - μ) (b := b - μ) hlt (hdev v).1 (hdev v).2 r)
      (le_of_lt (hq v))
  refine le_trans (Finset.sum_le_sum (fun v _ => hchord v)) ?_
  · -- sum of weights times chord = RHS (weights sum to 1)
    have h1 : ∑ v : V, q v * (((b - μ) - (g v - μ)) / (b - μ - (a - μ))
          * Real.exp (r * (a - μ))
        + ((g v - μ) - (a - μ)) / (b - μ - (a - μ)) * Real.exp (r * (b - μ)))
        = ∑ v : V, q v * ((b - g v) / (b - a) * Real.exp (r * (a - μ))
          + (g v - a) / (b - a) * Real.exp (r * (b - μ))) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hden : b - μ - (a - μ) = b - a := by ring
      rw [hden]
      ring
    rw [h1]
    -- now average the affine weights
    have hwavg1 : ∑ v : V, q v * ((b - g v) / (b - a))
        = (b - μ) / (b - a) := by
      have : ∀ v : V, q v * ((b - g v) / (b - a))
          = (q v * (b - g v)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => this v)]
      rw [← Finset.sum_div]
      have hbg : ∑ v : V, q v * (b - g v) = b - μ := by
        have hsplit : ∀ v : V, q v * (b - g v) = q v * b - q v * g v := by
          intro v; ring
        rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
        rw [Finset.sum_sub_distrib]
        have hqb : ∑ v : V, q v * b = b := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) b),
            ← Finset.mul_sum, hq1, mul_one]
        rw [hqb]
      rw [hbg]
    have hwavg2 : ∑ v : V, q v * ((g v - a) / (b - a))
        = (μ - a) / (b - a) := by
      have : ∀ v : V, q v * ((g v - a) / (b - a))
          = (q v * (g v - a)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => this v)]
      rw [← Finset.sum_div]
      have hga : ∑ v : V, q v * (g v - a) = μ - a := by
        have hsplit : ∀ v : V, q v * (g v - a) = q v * g v - q v * a := by
          intro v; ring
        rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
        rw [Finset.sum_sub_distrib]
        have hqa : ∑ v : V, q v * a = a := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a)]
          rw [← Finset.mul_sum, hq1, mul_one]
        rw [hqa]
      rw [hga]
    -- distribute the sum over the two terms
    have hsplit : ∑ v : V, q v * ((b - g v) / (b - a) * Real.exp (r * (a - μ))
        + (g v - a) / (b - a) * Real.exp (r * (b - μ)))
        = ∑ v : V, q v * ((b - g v) / (b - a)) * Real.exp (r * (a - μ))
          + ∑ v : V, q v * ((g v - a) / (b - a)) * Real.exp (r * (b - μ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hsplit]
    have e1 : ∑ v : V, q v * ((b - g v) / (b - a)) * Real.exp (r * (a - μ))
        = (∑ v : V, q v * ((b - g v) / (b - a))) * Real.exp (r * (a - μ)) := by
      simp [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    have e2 : ∑ v : V, q v * ((g v - a) / (b - a)) * Real.exp (r * (b - μ))
        = (∑ v : V, q v * ((g v - a) / (b - a))) * Real.exp (r * (b - μ)) := by
      simp [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    rw [e1, e2, hwavg1, hwavg2]

/-! ## Хорда логарифма (R500)

Вогнутость ln: (1-w) ln a + w ln b <= ln((1-w)a + w b) для
a,b > 0, 0 < w < 1. Через strictConcaveOn_log_Ioi.concaveOn;
двухточечный Jensen. Основа для вариационных KL-шагов
(взвешенные log-sum оценки). -/
theorem log_chord {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℝ)
    (hw : 0 < w) (hw2 : w < 1) :
    (1 - w) * Real.log a + w * Real.log b
      ≤ Real.log ((1 - w) * a + w * b) := by
  have hc : ConcaveOn ℝ (Ioi (0:ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hma : (a:ℝ) ∈ Ioi (0:ℝ) := ha
  have hmb : (b:ℝ) ∈ Ioi (0:ℝ) := hb
  have hw1 : (0:ℝ) ≤ 1 - w := by linarith
  have hsum : (1 - w) + w = 1 := by ring
  have h := hc.2 hma hmb hw1 (le_of_lt hw) hsum
  -- h : log ((1-w) • a + w • b) >= (1-w) • log a + w • log b
  have hcombo : ((1 - w)) • (a:ℝ) + (w) • (b:ℝ) = (1 - w) * a + w * b := by
    rw [smul_eq_mul, smul_eq_mul]
  rw [hcombo] at h
  simpa using h

/-! ## Взвешенное AM-GM (R501)

a^{1-w} * b^w <= (1-w) a + w b для a,b > 0, w in (0,1):
экспоненцирование хорды логарифма R500; rpow-канал через
log_rpow + exp_log (positivity для rpow-положительности). -/
theorem amgm_weighted {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℝ)
    (hw : 0 < w) (hw2 : w < 1) :
    a ^ (1 - w) * b ^ w ≤ (1 - w) * a + w * b := by
  have h := log_chord ha hb w hw hw2
  -- (1-w) ln a + w ln b = ln (a^(1-w) * b^w)
  have hexp : Real.exp ((1 - w) * Real.log a + w * Real.log b)
      = a ^ (1 - w) * b ^ w := by
    rw [Real.exp_add]
    rw [show Real.exp ((1 - w) * Real.log a) = a ^ (1 - w) from by
      rw [← Real.log_rpow ha (1 - w),
        Real.exp_log (by positivity : (0:ℝ) < a ^ (1 - w))],
     show Real.exp (w * Real.log b) = b ^ w from by
      rw [← Real.log_rpow hb w,
        Real.exp_log (by positivity : (0:ℝ) < b ^ w)]]
  -- exp monotone
  refine le_trans (le_of_eq hexp.symm) ?_
  exact le_trans (Real.exp_le_exp.mpr h)
    (le_of_eq (Real.exp_log (by positivity : (0:ℝ) < (1 - w) * a + w * b)))

/-! ## Неравенство Юнга (R502)

x*y <= x^p/p + y^q/q для x,y >= 0, 1 < p, 1/p + 1/q = 1:
обобщённый AM-GM R501 на X = x^p, Y = y^q с весом 1/q,
степени сокращаются каналом (z^r)^(1/r) = z (log_rpow +
exp_log); degenerate-случаи через zero_rpow + positivity.
Фундамент Hölder/Minkowski-вертикали. -/
theorem young_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p q : ℝ}
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    x * y ≤ x ^ p / p + y ^ q / q := by
  have hq : 1 < q := by
    have hp0 : (0:ℝ) < p := by linarith
    have hpp : 1 / p < 1 := by
      field_simp
      nlinarith [hp0]
    have : (1:ℝ) / q = 1 - 1 / p := by linarith [hpq]
    have hqpos : (0:ℝ) < q := by
      have hsub : (0:ℝ) < 1 - 1 / p := by linarith
      have := this
      by_contra hc
      push_neg at hc
      have h1 : (1:ℝ) / q ≤ 0 := by
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith
        · linarith
      rw [this] at h1
      linarith
    have hp1pos : (0:ℝ) < 1 / p := by positivity
    show (1:ℝ) < q
    by_contra hq1
    push_neg at hq1
    have h2 : (1:ℝ) / q ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hqpos]
      linarith
    rw [this] at h2
    linarith
  rcases eq_or_lt_of_le hx with hx' | hx'
  · -- x = 0
    have hpp0 : (0:ℝ) < p := by linarith
    have hxp : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith : (p:ℝ) ≠ 0)
    rw [← hx', hxp]
    norm_num
    positivity
  · rcases eq_or_lt_of_le hy with hy' | hy'
    · -- y = 0
      have hqq0 : (0:ℝ) < q := by linarith
      have hyq : (0:ℝ) ^ q = 0 := Real.zero_rpow (by linarith : (q:ℝ) ≠ 0)
      rw [← hy', hyq]
      norm_num
      positivity
    · -- x, y > 0: generalized AM-GM on X = x^p, Y = y^q, w = 1/q
      have hp0 : (0:ℝ) < p := by linarith
      have hq0 : (0:ℝ) < q := by linarith
      have hxp : (0:ℝ) < x ^ p := by positivity
      have hyq : (0:ℝ) < y ^ q := by positivity
      have hw : (0:ℝ) < 1 / q := by positivity
      have hw2 : 1 / q < 1 := by
        rw [div_lt_one hq0]
        linarith
      have hgam := amgm_weighted hxp hyq (1 / q) hw hw2
      -- (x^p)^(1-1/q) (y^q)^(1/q) <= (1-1/q) x^p + (1/q) y^q
      -- 1 - 1/q = 1/p
      have hsub : (1:ℝ) - 1 / q = 1 / p := by linarith [hpq]
      -- power lemma
      have hkey2 : ∀ z : ℝ, ∀ r : ℝ, 0 < z → 0 < r →
          (z ^ r) ^ (1 / r) = z := by
        intro z r hz hr
        have h1 : (z ^ r) ^ (1 / r) = Real.exp ((1 / r) * Real.log (z ^ r)) := by
          rw [← Real.log_rpow (by positivity : (0:ℝ) < z ^ r) (1 / r)]
          exact Real.exp_log (by positivity : (0:ℝ) < (z ^ r) ^ (1 / r)) |>.symm
        rw [h1, Real.log_rpow hz r]
        rw [show (1:ℝ) / r = r⁻¹ from by field_simp, ← mul_assoc, mul_comm r⁻¹ r,
          mul_inv_cancel₀ (by positivity : (r:ℝ) ≠ 0), one_mul, Real.exp_log hz]
      have he1 : (x ^ p) ^ (1 - 1 / q) = x := by
        rw [hsub]
        exact hkey2 x p hx' hp0
      have he2 : (y ^ q) ^ (1 / q) = y := hkey2 y q hy' hq0
      rw [he1, he2] at hgam
      -- RHS: (1-1/q) x^p + (1/q) y^q = x^p/p + y^q/q
      have hconv : (1 - 1 / q) * x ^ p + (1 / q) * y ^ q
          = x ^ p / p + y ^ q / q := by
        rw [hsub]
        rw [one_div_mul_eq_div, one_div_mul_eq_div]
      rw [← hconv]
      exact hgam

/-! ## Конечный Гёльдер (R503)

sum |a*b| <= (sum |a|^p)^{1/p} * (sum |b|^q)^{1/q} для
сопряжённых 1/p+1/q=1: нормировка X=|a|/PA, Y=|b|/PB,
per-term Young R502, суммирование; PA^p = sum |a|^p через
rpow_mul (1/p*p=1); degenerate-случаи SA=0/SB=0 через
single_le_sum + zero_rpow. Замыкает Young->Hoelder
вертикаль (Minkowski далее). -/
theorem hoelder_finite {V : Type*} [Fintype V] (a b : V → ℝ) {p q : ℝ}
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    ∑ v : V, |a v * b v|
      ≤ (∑ v : V, |a v| ^ p) ^ (1 / p) * (∑ v : V, |b v| ^ q) ^ (1 / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hpp : (1:ℝ) / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hq : 1 < q := by
    have h1 : (1:ℝ) / q = 1 - 1 / p := by linarith [hpq]
    have hqpos : (0:ℝ) < q := by
      by_contra hc
      push_neg at hc
      have h2 : (1:ℝ) / q ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) hc
      rw [h1] at h2
      linarith
    show (1:ℝ) < q
    by_contra hq1
    push_neg at hq1
    have h3 : (1:ℝ) / q ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hqpos]
      linarith
    rw [h1] at h3
    have hp1pos : (0:ℝ) < 1 / p := by positivity
    linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hSAnn : (0:ℝ) ≤ ∑ w : V, |a w| ^ p :=
    Finset.sum_nonneg (fun v _ => show (0:ℝ) ≤ |a v| ^ p by positivity)
  have hSBnn : (0:ℝ) ≤ ∑ w : V, |b w| ^ q :=
    Finset.sum_nonneg (fun v _ => show (0:ℝ) ≤ |b v| ^ q by positivity)
  rcases eq_or_lt_of_le hSAnn with hSA0 | hSApos
  · -- SA = 0 => a = 0
    have haz : ∀ v : V, |a v| = 0 := by
      intro v
      by_contra hv
      push_neg at hv
      have hterm : (0:ℝ) < |a v| ^ p := by positivity
      have hsingle : |a v| ^ p ≤ ∑ w : V, |a w| ^ p :=
        Finset.single_le_sum
          (fun w _ => show (0:ℝ) ≤ |a w| ^ p by positivity) (Finset.mem_univ v)
      rw [← hSA0] at hsingle
      linarith
    have hL : ∑ v : V, |a v * b v| = 0 := by
      refine Finset.sum_eq_zero (fun v _ => ?_)
      simp [abs_mul, haz v]
    rw [hL, ← hSA0, Real.zero_rpow (by positivity : (1:ℝ) / p ≠ 0), zero_mul]
  · rcases eq_or_lt_of_le hSBnn with hSB0 | hSBpos
    · have hbz : ∀ v : V, |b v| = 0 := by
        intro v
        by_contra hv
        push_neg at hv
        have hterm : (0:ℝ) < |b v| ^ q := by positivity
        have hsingle : |b v| ^ q ≤ ∑ w : V, |b w| ^ q :=
          Finset.single_le_sum
            (fun w _ => show (0:ℝ) ≤ |b w| ^ q by positivity) (Finset.mem_univ v)
        rw [← hSB0] at hsingle
        linarith
      have hL : ∑ v : V, |a v * b v| = 0 := by
        refine Finset.sum_eq_zero (fun v _ => ?_)
        simp [abs_mul, hbz v]
      rw [hL, ← hSB0, Real.zero_rpow (by positivity : (1:ℝ) / q ≠ 0), mul_zero]
    · -- main case
      set PA : ℝ := (∑ w : V, |a w| ^ p) ^ (1 / p) with hPA
      set PB : ℝ := (∑ w : V, |b w| ^ q) ^ (1 / q) with hPB
      have hPApos : (0:ℝ) < PA := by
        rw [hPA]
        apply Real.rpow_pos_of_pos hSApos
      have hPBpos : (0:ℝ) < PB := by
        rw [hPB]
        apply Real.rpow_pos_of_pos hSBpos
      have hyoung : ∀ v : V,
          (|a v| / PA) * (|b v| / PB) ≤ (|a v| / PA) ^ p / p + (|b v| / PB) ^ q / q :=
        fun v => young_two (div_nonneg (abs_nonneg _) hPApos.le)
          (div_nonneg (abs_nonneg _) hPBpos.le) hp hpq
      have hsum2 : ∑ v : V, (|a v| / PA) ^ p = 1 := by
        have hpow : ∀ v : V, (|a v| / PA) ^ p = |a v| ^ p / PA ^ p :=
          fun v => div_rpow (abs_nonneg _) hPApos.le p
        rw [Finset.sum_congr rfl (fun v _ => hpow v), ← Finset.sum_div]
        have hPAp : PA ^ p = ∑ w : V, |a w| ^ p := by
          rw [hPA, ← Real.rpow_mul (show (0:ℝ) ≤ ∑ w : V, |a w| ^ p by positivity),
            show (1:ℝ) / p * p = 1 from by field_simp, Real.rpow_one]
        rw [hPAp]
        exact div_self hSApos.ne'
      have hsum3 : ∑ v : V, (|b v| / PB) ^ q = 1 := by
        have hpow : ∀ v : V, (|b v| / PB) ^ q = |b v| ^ q / PB ^ q :=
          fun v => div_rpow (abs_nonneg _) hPBpos.le q
        rw [Finset.sum_congr rfl (fun v _ => hpow v), ← Finset.sum_div]
        have hPBq : PB ^ q = ∑ w : V, |b w| ^ q := by
          rw [hPB, ← Real.rpow_mul (show (0:ℝ) ≤ ∑ w : V, |b w| ^ q by positivity),
            show (1:ℝ) / q * q = 1 from by field_simp, Real.rpow_one]
        rw [hPBq]
        exact div_self hSBpos.ne'
      have hLHS : ∑ v : V, (|a v| / PA) * (|b v| / PB)
          = (∑ v : V, |a v * b v|) / (PA * PB) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [abs_mul, div_mul_div_comm _ _ _ _]
      have hchain : (∑ v : V, |a v * b v|) / (PA * PB) ≤ 1 := by
        have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hyoung v)
        rw [hLHS] at hs
        rw [Finset.sum_add_distrib] at hs
        have hnorm : ∑ v : V, (|a v| / PA) ^ p / p
            + ∑ v : V, (|b v| / PB) ^ q / q = 1 := by
          rw [← Finset.sum_div, ← Finset.sum_div, hsum2, hsum3]
          rw [hpq]
        rw [hnorm] at hs
        exact hs
      rw [div_le_iff₀ (show (0:ℝ) < PA * PB from mul_pos hPApos hPBpos)] at hchain
      rwa [one_mul] at hchain

/-! ## Конечный Минковский (R504)

(sum |a+b|^p)^{1/p} <= (sum |a|^p)^{1/p} + (sum |b|^p)^{1/p}:
разложение X = sum |a+b|*|a+b|^{p-1}, треугольник,
Гёльдер R503 на оба слагаемых с ключевым тождеством
(|a+b|^{p-1})^q = |a+b|^p ((p-1)q = p из p*q = p+q),
финал через X = X^{1/p}*X^{1/q} и сокращение
le_of_mul_le_mul_right. Замыкает Young->Hoelder->Minkowski
вертикаль. -/
theorem minkowski_finite {V : Type*} [Fintype V] (a b : V → ℝ) {p q : ℝ}
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    (∑ v : V, |a v + b v| ^ p) ^ (1 / p)
      ≤ (∑ v : V, |a v| ^ p) ^ (1 / p)
        + (∑ v : V, |b v| ^ p) ^ (1 / p) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hpp : (1:ℝ) / p < 1 := by
    rw [div_lt_one hp0]; linarith
  have hq : 1 < q := by
    have h1 : (1:ℝ) / q = 1 - 1 / p := by linarith [hpq]
    have hqpos : (0:ℝ) < q := by
      by_contra hc
      push_neg at hc
      have h2 : (1:ℝ) / q ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      rw [h1] at h2
      linarith
    show (1:ℝ) < q
    by_contra hq1
    push_neg at hq1
    have h3 : (1:ℝ) / q ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hqpos]; linarith
    rw [h1] at h3
    have hp1pos : (0:ℝ) < 1 / p := by positivity
    linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hpqmul : p * q = p + q := by
    have h1 : p * q * (1 / p + 1 / q) = p * q * 1 := by rw [hpq]
    have h2 : p * q * (1 / p + 1 / q)
        = p * q / p + p * q / q := by ring
    have h3 : p * q / p = q := by
      field_simp
    have h4 : p * q / q = p := by
      field_simp
    rw [h2, h3, h4, mul_one] at h1
    linarith
  have hp1q : (p - 1) * q = p := by nlinarith [hpqmul]
  set X : ℝ := ∑ v : V, |a v + b v| ^ p with hX
  have hXnn : (0:ℝ) ≤ X := Finset.sum_nonneg
    (fun v _ => show (0:ℝ) ≤ |a v + b v| ^ p by positivity)
  rcases eq_or_lt_of_le hXnn with hX0 | hXpos
  · rw [← hX0, Real.zero_rpow (by positivity : (1:ℝ) / p ≠ 0)]
    positivity
  · -- decomposition: X = sum |a+b| * |a+b|^(p-1)
    have hsplit : X = ∑ v : V, |a v + b v| * |a v + b v| ^ (p - 1) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h1 : |a v + b v| ^ p
          = |a v + b v| ^ (1 + (p - 1)) := by
        congr 1
        ring
      rw [h1]
      rw [Real.rpow_add' (abs_nonneg _) (by linarith : (1:ℝ) + (p - 1) ≠ 0)]
      rw [Real.rpow_one]
    -- triangle
    have htri : ∑ v : V, |a v + b v| * |a v + b v| ^ (p - 1)
        ≤ ∑ v : V, (|a v| + |b v|) * |a v + b v| ^ (p - 1) := by
      refine Finset.sum_le_sum (s := Finset.univ) (fun v _ => ?_)
      exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)
    -- expand
    have hexp : ∑ v : V, (|a v| + |b v|) * |a v + b v| ^ (p - 1)
        = ∑ v : V, |a v| * |a v + b v| ^ (p - 1)
          + ∑ v : V, |b v| * |a v + b v| ^ (p - 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    -- power identity
    have hpowkey : (fun v => (|a v + b v| ^ (p - 1)) ^ q)
        = (fun v => |a v + b v| ^ p) := by
      funext v
      rw [← Real.rpow_mul (abs_nonneg _) (p - 1) q, hp1q]
    -- Hoelder both
    have hH1 : ∑ v : V, |a v| * |a v + b v| ^ (p - 1)
        ≤ (∑ v : V, |a v| ^ p) ^ (1 / p) * X ^ (1 / q) := by
      have h := hoelder_finite (fun v => a v)
        (fun v => |a v + b v| ^ (p - 1)) hp hpq
      have habs : ∀ v : V, |a v * |a v + b v| ^ (p - 1)|
          = |a v| * |a v + b v| ^ (p - 1) := by
        intro v
        rw [abs_mul]
        congr 1
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤ |a v + b v| ^ (p - 1))
      have habs2 : ∑ v : V, abs (|a v + b v| ^ (p - 1)) ^ q
          = ∑ v : V, (|a v + b v| ^ (p - 1)) ^ q := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        congr 1
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤ |a v + b v| ^ (p - 1))
      rw [Finset.sum_congr rfl (fun v _ => habs v), habs2, hpowkey, ← hX] at h
      exact h
    have hH2 : ∑ v : V, |b v| * |a v + b v| ^ (p - 1)
        ≤ (∑ v : V, |b v| ^ p) ^ (1 / p) * X ^ (1 / q) := by
      have h := hoelder_finite (fun v => b v)
        (fun v => |a v + b v| ^ (p - 1)) hp hpq
      have habs : ∀ v : V, |b v * |a v + b v| ^ (p - 1)|
          = |b v| * |a v + b v| ^ (p - 1) := by
        intro v
        rw [abs_mul]
        congr 1
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤ |a v + b v| ^ (p - 1))
      have habs2 : ∑ v : V, abs (|a v + b v| ^ (p - 1)) ^ q
          = ∑ v : V, (|a v + b v| ^ (p - 1)) ^ q := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        congr 1
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤ |a v + b v| ^ (p - 1))
      rw [Finset.sum_congr rfl (fun v _ => habs v), habs2, hpowkey, ← hX] at h
      exact h
    -- chain
    have hchain : X ≤ ((∑ v : V, |a v| ^ p) ^ (1 / p)
        + (∑ v : V, |b v| ^ p) ^ (1 / p)) * X ^ (1 / q) := by
      calc X = ∑ v : V, |a v + b v| * |a v + b v| ^ (p - 1) := hsplit
        _ ≤ ∑ v : V, (|a v| + |b v|) * |a v + b v| ^ (p - 1) := htri
        _ = ∑ v : V, |a v| * |a v + b v| ^ (p - 1)
            + ∑ v : V, |b v| * |a v + b v| ^ (p - 1) := hexp
        _ ≤ (∑ v : V, |a v| ^ p) ^ (1 / p) * X ^ (1 / q)
            + (∑ v : V, |b v| ^ p) ^ (1 / p) * X ^ (1 / q) :=
          add_le_add hH1 hH2
        _ = ((∑ v : V, |a v| ^ p) ^ (1 / p)
            + (∑ v : V, |b v| ^ p) ^ (1 / p)) * X ^ (1 / q) := by ring
    -- factor: X = X^{1/p} * X^{1/q}
    have hXsplit : X ^ (1 / p) * X ^ (1 / q) = X := by
      rw [← Real.rpow_add' hXnn (by
        rw [hpq]; norm_num : (1:ℝ) / p + 1 / q ≠ 0), hpq, Real.rpow_one]
    have hXqpos : (0:ℝ) < X ^ (1 / q) := Real.rpow_pos_of_pos hXpos _
    -- cancel: X^{1/p} * X^{1/q} <= C * X^{1/q}  =>  X^{1/p} <= C
    -- hchain : X <= C * X^{1/q}; write X = X^{1/p} * X^{1/q} on the left only
    have hstep : X ^ (1 / p) * X ^ (1 / q)
        ≤ (((∑ v : V, |a v| ^ p) ^ (1 / p)
            + (∑ v : V, |b v| ^ p) ^ (1 / p)) * X ^ (1 / q)) := by
      rw [hXsplit]
      exact hchain
    exact le_of_mul_le_mul_right hstep hXqpos

/-! ## Сравнение норм L1 <= Lp (R505)

sum |g| <= (sum |g|^p)^{1/p} * n^{1/q}: Hoelder R503 с
константной второй функцией 1; sum |1|^q = n. Базовый
кирпич норм-сравнений для оценок качества/объёма. -/
theorem lp_one_le_card {V : Type*} [Fintype V] (g : V → ℝ) {p q : ℝ}
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    ∑ v : V, |g v|
      ≤ (∑ v : V, |g v| ^ p) ^ (1 / p)
        * (Fintype.card V : ℝ) ^ (1 / q) := by
  have h := hoelder_finite (V := V) g (fun _ : V => (1:ℝ)) hp hpq
  -- RHS second factor: (sum 1^q)^{1/q} = card^{1/q}
  have hone : (∑ v : V, (|(1:ℝ)| ^ q)) = (Fintype.card V : ℝ) := by
    have h1 : ∀ v : V, (|(1:ℝ)| ^ q) = 1 := by
      intro v
      rw [abs_one, one_rpow]
    rw [Finset.sum_congr rfl (fun v _ => h1 v)]
    rw [Finset.sum_const]
    simp
  rw [hone] at h
  -- LHS: |g v * 1| = |g v|
  have hL : ∑ v : V, |g v * (1:ℝ)| = ∑ v : V, |g v| := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [mul_one]
  rwa [hL] at h

/-! ## Взвешенный Гёльдер (R506)

sum w*|a*b| <= (sum w|a|^p)^{1/p} * (sum w|b|^q)^{1/q} для
w >= 0: поглощение веса w = w^{1/p} * w^{1/q} (rpow_add при
w>0, zero_rpow при w=0), применяем невзвешенный Гёльдер R503
к (w^{1/p}|a|, w^{1/q}|b|) и сворачиваем (w^{1/p})^p = w.
Ключ к вероятностным Lp-оценкам HAGI (средние по q-мерам). -/
theorem hoelder_weighted {V : Type*} [Fintype V] (w a b : V → ℝ) {p q : ℝ}
    (hw : ∀ v, 0 ≤ w v) (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    ∑ v : V, w v * |a v * b v|
      ≤ (∑ v : V, w v * |a v| ^ p) ^ (1 / p)
        * (∑ v : V, w v * |b v| ^ q) ^ (1 / q) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hpp : (1:ℝ) / p < 1 := by
    rw [div_lt_one hp0]; linarith
  have hq1 : (1:ℝ) < q := by
    have h1 : (1:ℝ) / q = 1 - 1 / p := by linarith [hpq]
    have hqpos : (0:ℝ) < q := by
      by_contra hc
      push_neg at hc
      have h2 : (1:ℝ) / q ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) hc
      rw [h1] at h2
      linarith
    by_contra hq1'
    push_neg at hq1'
    have h3 : (1:ℝ) / q ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hqpos]; linarith
    rw [h1] at h3
    have hp1pos : (0:ℝ) < 1 / p := by positivity
    linarith
  have hpne : (1:ℝ) / p ≠ 0 := by positivity
  have hqne : (1:ℝ) / q ≠ 0 := by positivity
  -- absorb weights: w = w^{1/p} * w^{1/q}
  have habsorb : ∀ v : V, w v * |a v * b v|
      = (w v ^ (1 / p) * |a v|) * (w v ^ (1 / q) * |b v|) := by
    intro v
    rw [abs_mul]
    have hkey : w v ^ (1 / p) * w v ^ (1 / q) = w v := by
      by_cases hwv : w v = 0
      · rw [hwv, Real.zero_rpow hpne,
          Real.zero_rpow hqne, zero_mul]
      · have hwvpos : (0:ℝ) < w v := lt_of_le_of_ne (hw v)
          (fun h => hwv h.symm)
        rw [← Real.rpow_add hwvpos, hpq, Real.rpow_one]
    linear_combination (|b v| * |a v|) * hkey.symm
  rw [Finset.sum_congr rfl (fun v _ => habsorb v)]
  -- apply unweighted Hoelder to the absorbed functions
  have h := hoelder_finite (fun v => w v ^ (1 / p) * |a v|)
    (fun v => w v ^ (1 / q) * |b v|) hp hpq
  -- simplify RHS factors: (w^{1/p}|a|)^p = w |a|^p
  have hfac1 : ∀ v : V, abs (w v ^ (1 / p) * |a v|) ^ p = w v * |a v| ^ p := by
    intro v
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw v) (1 / p)) (abs_nonneg _))]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw v) (1 / p))
      (abs_nonneg _)]
    rw [← Real.rpow_mul (hw v), show (1:ℝ) / p * p = 1 from by field_simp,
      Real.rpow_one]
  have hfac2 : ∀ v : V, abs (w v ^ (1 / q) * |b v|) ^ q = w v * |b v| ^ q := by
    intro v
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw v) (1 / q)) (abs_nonneg _))]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw v) (1 / q))
      (abs_nonneg _)]
    rw [← Real.rpow_mul (hw v), show (1:ℝ) / q * q = 1 from by field_simp,
      Real.rpow_one]
  rw [Finset.sum_congr rfl (fun v _ => hfac1 v),
    Finset.sum_congr rfl (fun v _ => hfac2 v)] at h
  have habsL : ∀ v : V, abs (w v ^ (1 / p) * |a v| * (w v ^ (1 / q) * |b v|))
      = w v * |a v * b v| := by
    intro v
    have h1 : abs (w v ^ (1 / p) * |a v|) = w v ^ (1 / p) * |a v| :=
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw v) (1 / p))
        (abs_nonneg _))
    have h2 : abs (w v ^ (1 / q) * |b v|) = w v ^ (1 / q) * |b v| :=
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hw v) (1 / q))
        (abs_nonneg _))
    rw [abs_mul, h1, h2]
    exact (habsorb v).symm
  rw [Finset.sum_congr rfl (fun v _ => habsL v)] at h
  rw [Finset.sum_congr rfl (fun v _ => (habsorb v).symm)]
  exact h

/-! ## Среднее <= RMS-мощность (R507)

Взвешенное E|g| <= (E|g|^p)^{1/p} при sum w = 1:
взвешенный Гёльдер R506 с константной второй функцией;
мгновенное следствие. Ключ к Jensen/Lyapunov-оценкам. -/
theorem lp_mean_le_rms {V : Type*} [Fintype V] (w g : V → ℝ) {p q : ℝ}
    (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v : V, w v = 1)
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    ∑ v : V, w v * |g v|
      ≤ (∑ v : V, w v * |g v| ^ p) ^ (1 / p) := by
  have h := hoelder_weighted w g (fun _ => (1:ℝ)) hw hp hpq
  -- second factor: (sum w * |1|^q)^{1/q} = (sum w)^{1/q} = 1
  have hone : (∑ v : V, w v * |(1:ℝ)| ^ q) = 1 := by
    have h1 : ∀ v : V, w v * |(1:ℝ)| ^ q = w v := by
      intro v
      rw [abs_one, one_rpow, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => h1 v), hw1]
  rw [hone] at h
  -- second factor becomes 1^{1/q} = 1
  rw [one_rpow, mul_one] at h
  -- LHS: |g v * 1| = |g v|
  have hL : ∑ v : V, w v * |g v * (1:ℝ)| = ∑ v : V, w v * |g v| := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [mul_one]
  rwa [hL] at h

/-! ## Взвешенный Минковский (R508)

(sum w|a+b|^p)^{1/p} <= (sum w|a|^p)^{1/p} + (sum w|b|^p)^{1/p}
для w >= 0: та же схема R504 (разложение/треугольник),
взвешенный Гёльдер R506 на оба слагаемых, сокращение
le_of_mul_le_mul_right. Полная взвешенная Lp-вертикаль. -/
theorem minkowski_weighted {V : Type*} [Fintype V] (w a b : V → ℝ) {p q : ℝ}
    (hw : ∀ v, 0 ≤ w v) (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    (∑ v : V, w v * |a v + b v| ^ p) ^ (1 / p)
      ≤ (∑ v : V, w v * |a v| ^ p) ^ (1 / p)
        + (∑ v : V, w v * |b v| ^ p) ^ (1 / p) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hpp : (1:ℝ) / p < 1 := by
    rw [div_lt_one hp0]; linarith
  have hq : 1 < q := by
    have h1 : (1:ℝ) / q = 1 - 1 / p := by linarith [hpq]
    have hqpos : (0:ℝ) < q := by
      by_contra hc
      push_neg at hc
      have h2 : (1:ℝ) / q ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) hc
      rw [h1] at h2
      linarith
    show (1:ℝ) < q
    by_contra hq1
    push_neg at hq1
    have h3 : (1:ℝ) / q ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ hqpos]; linarith
    rw [h1] at h3
    have hp1pos : (0:ℝ) < 1 / p := by positivity
    linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hpqmul : p * q = p + q := by
    have h1 : p * q * (1 / p + 1 / q) = p * q * 1 := by rw [hpq]
    have h2 : p * q * (1 / p + 1 / q)
        = p * q / p + p * q / q := by ring
    have h3 : p * q / p = q := by field_simp
    have h4 : p * q / q = p := by field_simp
    rw [h2, h3, h4, mul_one] at h1
    linarith
  have hp1q : (p - 1) * q = p := by nlinarith [hpqmul]
  set X : ℝ := ∑ v : V, w v * |a v + b v| ^ p with hX
  have hXnn : (0:ℝ) ≤ X := Finset.sum_nonneg
    (fun v _ => mul_nonneg (hw v) (by positivity : (0:ℝ) ≤ |a v + b v| ^ p))
  rcases eq_or_lt_of_le hXnn with hX0 | hXpos
  · rw [← hX0, Real.zero_rpow (by positivity : (1:ℝ) / p ≠ 0)]
    exact add_nonneg (Real.rpow_nonneg (Finset.sum_nonneg
      (fun v _ => mul_nonneg (hw v) (by positivity : (0:ℝ) ≤ |a v| ^ p))) _)
      (Real.rpow_nonneg (Finset.sum_nonneg
        (fun v _ => mul_nonneg (hw v) (by positivity : (0:ℝ) ≤ |b v| ^ p))) _)
  · -- decomposition: X = sum w |a+b| * |a+b|^(p-1)
    have hsplit : X = ∑ v : V, w v * (|a v + b v| * |a v + b v| ^ (p - 1)) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h1 : |a v + b v| ^ p
          = |a v + b v| ^ (1 + (p - 1)) := by
        congr 1
        ring
      rw [h1, Real.rpow_add' (abs_nonneg _)
        (by linarith : (1:ℝ) + (p - 1) ≠ 0), Real.rpow_one]
    -- triangle
    have htri : ∑ v : V, w v * (|a v + b v| * |a v + b v| ^ (p - 1))
        ≤ ∑ v : V, w v * ((|a v| + |b v|) * |a v + b v| ^ (p - 1)) := by
      refine Finset.sum_le_sum (s := Finset.univ) (fun v _ => ?_)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (abs_add_le _ _)
          (by positivity : (0:ℝ) ≤ |a v + b v| ^ (p - 1))) (hw v)
    -- expand
    have hexp : ∑ v : V, w v * ((|a v| + |b v|) * |a v + b v| ^ (p - 1))
        = ∑ v : V, w v * (|a v| * |a v + b v| ^ (p - 1))
          + ∑ v : V, w v * (|b v| * |a v + b v| ^ (p - 1)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    -- power identity
    have hpowkey : (fun v => (|a v + b v| ^ (p - 1)) ^ q)
        = (fun v => |a v + b v| ^ p) := by
      funext v
      rw [← Real.rpow_mul (abs_nonneg _) (p - 1) q, hp1q]
    -- weighted Hoelder both
    have hH1 : ∑ v : V, w v * (|a v| * |a v + b v| ^ (p - 1))
        ≤ (∑ v : V, w v * |a v| ^ p) ^ (1 / p) * X ^ (1 / q) := by
      have h := hoelder_weighted w (fun v => a v)
        (fun v => |a v + b v| ^ (p - 1)) hw hp hpq
      have habs : ∀ v : V, w v * |a v * |a v + b v| ^ (p - 1)|
          = w v * (|a v| * |a v + b v| ^ (p - 1)) := by
        intro v
        rw [abs_mul, abs_of_nonneg
          (Real.rpow_nonneg (abs_nonneg (a v + b v)) (p - 1))]
      rw [Finset.sum_congr rfl (fun v _ => habs v)] at h
      have habs3 : ∀ v : V, w v * abs (|a v + b v| ^ (p - 1)) ^ q
          = w v * (|a v + b v| ^ (p - 1)) ^ q := by
        intro v
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (a v + b v)) (p - 1))]
      rw [Finset.sum_congr rfl (fun v _ => habs3 v)] at h
      have hpk : ∀ v : V, w v * (|a v + b v| ^ (p - 1)) ^ q
          = w v * |a v + b v| ^ p := by
        intro v
        have hk : (|a v + b v| ^ (p - 1)) ^ q = |a v + b v| ^ p :=
          congrFun hpowkey v
        rw [hk]
      rw [Finset.sum_congr rfl (fun v _ => hpk v), ← hX] at h
      exact h
    have hH2 : ∑ v : V, w v * (|b v| * |a v + b v| ^ (p - 1))
        ≤ (∑ v : V, w v * |b v| ^ p) ^ (1 / p) * X ^ (1 / q) := by
      have h := hoelder_weighted w (fun v => b v)
        (fun v => |a v + b v| ^ (p - 1)) hw hp hpq
      have habs : ∀ v : V, w v * |b v * |a v + b v| ^ (p - 1)|
          = w v * (|b v| * |a v + b v| ^ (p - 1)) := by
        intro v
        rw [abs_mul, abs_of_nonneg
          (Real.rpow_nonneg (abs_nonneg (a v + b v)) (p - 1))]
      rw [Finset.sum_congr rfl (fun v _ => habs v)] at h
      have habs3 : ∀ v : V, w v * abs (|a v + b v| ^ (p - 1)) ^ q
          = w v * (|a v + b v| ^ (p - 1)) ^ q := by
        intro v
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (a v + b v)) (p - 1))]
      rw [Finset.sum_congr rfl (fun v _ => habs3 v)] at h
      have hpk : ∀ v : V, w v * (|a v + b v| ^ (p - 1)) ^ q
          = w v * |a v + b v| ^ p := by
        intro v
        have hk : (|a v + b v| ^ (p - 1)) ^ q = |a v + b v| ^ p :=
          congrFun hpowkey v
        rw [hk]
      rw [Finset.sum_congr rfl (fun v _ => hpk v), ← hX] at h
      exact h
    -- chain
    have hchain : X ≤ ((∑ v : V, w v * |a v| ^ p) ^ (1 / p)
        + (∑ v : V, w v * |b v| ^ p) ^ (1 / p)) * X ^ (1 / q) := by
      calc X = ∑ v : V, w v * (|a v + b v| * |a v + b v| ^ (p - 1)) := hsplit
        _ ≤ ∑ v : V, w v * ((|a v| + |b v|) * |a v + b v| ^ (p - 1)) := htri
        _ = ∑ v : V, w v * (|a v| * |a v + b v| ^ (p - 1))
            + ∑ v : V, w v * (|b v| * |a v + b v| ^ (p - 1)) := hexp
        _ ≤ (∑ v : V, w v * |a v| ^ p) ^ (1 / p) * X ^ (1 / q)
            + (∑ v : V, w v * |b v| ^ p) ^ (1 / p) * X ^ (1 / q) :=
          add_le_add hH1 hH2
        _ = ((∑ v : V, w v * |a v| ^ p) ^ (1 / p)
            + (∑ v : V, w v * |b v| ^ p) ^ (1 / p)) * X ^ (1 / q) := by ring
    -- factor and cancel
    have hXsplit : X ^ (1 / p) * X ^ (1 / q) = X := by
      rw [← Real.rpow_add' hXnn (by
        rw [hpq]; norm_num : (1:ℝ) / p + 1 / q ≠ 0), hpq, Real.rpow_one]
    have hXqpos : (0:ℝ) < X ^ (1 / q) := Real.rpow_pos_of_pos hXpos _
    have hstep : X ^ (1 / p) * X ^ (1 / q)
        ≤ ((∑ v : V, w v * |a v| ^ p) ^ (1 / p)
            + (∑ v : V, w v * |b v| ^ p) ^ (1 / p)) * X ^ (1 / q) := by
      rw [hXsplit]
      exact hchain
    exact le_of_mul_le_mul_right hstep hXqpos
