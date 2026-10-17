/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

open Real Filter Topology

/-!
# Телесный угол гиперсферы и «пик размерностей» (R520)

Ω_n = 2π^{n/2} / Γ(n/2) — площадь поверхности единичной (n−1)-сферы
(полный телесный угол n-мерного пространства). Ключевые факты:
* рекуррента Ω_{n+2} = (2π/n)·Ω_n;
* геометрическое доминирование обеих ветвей (чётной от 8, нечётной от 9);
* collapse: Ω_n → 0 при n → ∞ («проклятие размерности»);
* Ω_7 = 16π³/15 — дискретный пик (непрерывный максимум n ≈ 7.257).

HAGI-связка: дисциплина роста эффективной размерностью d_eff, не шириной
(FactorizedBPW, режим d_eff ≤ 8), и легитимность жёсткого прунинга
(фоновая тепловая масса направлений против конденсированного каркаса).
-/

namespace Hagi
/-- Полный телесный угол (площадь поверхности единичной 
(n−1)-сферы) в n-мерном евклидовом пространстве:
Ω_n = 2π^{n/2} / Γ(n/2). Максимум при n ≈ 7.257
(дискретно: n = 7), затем collapse к нулю:
Γ(n/2) ~ (n/2)! растёт быстрее π^{n/2}. -/
noncomputable def sphericalAngle (n : ℕ) : ℝ :=
  2 * π ^ ((n:ℝ) / 2) / Real.Gamma ((n:ℝ) / 2)

/-- Рекуррента телесных углов: Ω_{n+2} = (2π/n)·Ω_n. -/
theorem sphericalAngle_add_two {n : ℕ} (hn : 0 < n) :
    sphericalAngle (n+2) = (2 * π / (n:ℝ)) * sphericalAngle n := by
  unfold sphericalAngle
  have hd : (0:ℝ) < (n:ℝ)/2 := by positivity
  rw [show (((n:ℕ)+2 : ℕ) : ℝ) / 2 = (n:ℝ)/2 + 1 by push_cast; ring]
  rw [Real.Gamma_add_one (ne_of_gt hd), Real.rpow_add (by positivity), Real.rpow_one]
  push_cast
  ring

/-- Фактор рекурренты < 1 начиная с n ≥ 8 (2π/n ≤ π/4 < 1). -/
theorem sphericalAngle_factor_lt_one {n : ℕ} (hn : 8 ≤ n) :
    2 * π / (n:ℝ) < 1 := by
  have h1 : (0:ℝ) < (n:ℝ) := by positivity
  have hn2 : (π:ℝ) < (n:ℝ)/2 := by
    have hp : (π:ℝ) < 4 := Real.pi_lt_four
    have hk : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith
  exact (div_lt_one h1).mpr (by nlinarith)

/-- Геометрическое доминирование чётной ветви: Ω_{8+2j} ≤ (π/4)^j·Ω_8. -/
theorem sphericalAngle_even_geo (j : ℕ) :
    sphericalAngle (8 + 2*j) ≤ (π/4) ^ (j:ℕ) * sphericalAngle 8 := by
  induction j with
  | zero => simp
  | succ m ih =>
    have h8 : (8:ℝ) ≤ ((8+2*m:ℕ):ℝ) := by exact_mod_cast (by omega : (8:ℕ) ≤ 8+2*m)
    have hn : (0:ℝ) < ((8+2*m:ℕ):ℝ) := by positivity
    have hle : 2 * π / ((8+2*m:ℕ):ℝ) ≤ π/4 := by
      rw [div_le_iff₀ hn]
      field_simp
      nlinarith [Real.pi_pos]
    have hstep : sphericalAngle (8 + 2*(m+1))
        = (2*π/((8+2*m:ℕ):ℝ)) * sphericalAngle (8+2*m) := by
      have h6 : 8 + 2*(m+1) = (8+2*m) + 2 := by omega
      rw [h6, sphericalAngle_add_two (by omega)]

    rw [hstep]
    have hΩpos : (0:ℝ) ≤ sphericalAngle (8+2*m) := by
      unfold sphericalAngle
      apply div_nonneg (by positivity)
      exact le_of_lt (Real.Gamma_pos_of_pos (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_right hle hΩpos) ?_
    have hnn : (0:ℝ) ≤ π/4 := by positivity
    have hform : (π/4) * ((π/4)^(m:ℕ) * sphericalAngle 8)
        = (π/4)^(m+1) * sphericalAngle 8 :=
      by ring
    exact le_trans (mul_le_mul_of_nonneg_left ih hnn) (le_of_eq hform)


/-- Геометрическое доминирование нечётной ветви: Ω_{9+2j} ≤ (π/4)^j·Ω_9
(якорь 9: первый фактор 2π/9 < π/4, т.к. 8 < 9). -/
theorem sphericalAngle_odd_geo (j : ℕ) :
    sphericalAngle (9 + 2*j) ≤ (π/4) ^ (j:ℕ) * sphericalAngle 9 := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hn : (0:ℝ) < ((9+2*m:ℕ):ℝ) := by positivity
    have hle : 2 * π / ((9+2*m:ℕ):ℝ) ≤ π/4 := by
      rw [div_le_iff₀ hn]
      have hp : (0:ℝ) < π := Real.pi_pos
      have hf : (π:ℝ) < 4 := Real.pi_lt_four
      have hc : ((9+2*m:ℕ):ℝ) = 9 + 2 * (m:ℝ) := by push_cast; ring
      rw [hc]
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hstep : sphericalAngle (9 + 2*(m+1))
        = (2*π/((9+2*m:ℕ):ℝ)) * sphericalAngle (9+2*m) := by
      have h6 : 9 + 2*(m+1) = (9+2*m) + 2 := by omega
      rw [h6, sphericalAngle_add_two (show (0:ℕ) < 9+2*m by omega)]
    rw [hstep]
    have hΩpos : (0:ℝ) ≤ sphericalAngle (9+2*m) := by
      unfold sphericalAngle
      apply div_nonneg (by positivity)
      exact le_of_lt (Real.Gamma_pos_of_pos (by positivity))
    have hnn : (0:ℝ) ≤ π/4 := by positivity
    have hform : (π/4) * ((π/4)^(m:ℕ) * sphericalAngle 9)
        = (π/4)^(m+1) * sphericalAngle 9 := by ring
    exact le_trans (mul_le_mul_of_nonneg_right hle hΩpos)
      (le_trans (mul_le_mul_of_nonneg_left ih hnn) (le_of_eq hform))

/-- Классификация хвоста: всякое n ≥ 8 лежит в чётной (8+2j)
или нечётной (9+2j) ветви. -/
theorem tail_parity_split (n : ℕ) (hn : 8 ≤ n) :
    ∃ j, n = 8 + 2*j ∨ n = 9 + 2*j := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · refine ⟨(n-8)/2, Or.inl ?_⟩
    have h2 : n = 2 * (n/2) := by omega
    omega
  · refine ⟨(n-9)/2, Or.inr ?_⟩
    have h2 : n = 2 * (n/2) + 1 := by omega
    omega


/-- Сводная геометрическая оценка хвоста: Ω_n ≤ C·(π/4)^j на ветви. -/
theorem sphericalAngle_tail_bound {n : ℕ} (hn : 8 ≤ n) :
    ∃ j, (n = 8 + 2*j ∨ n = 9 + 2*j)
      ∧ sphericalAngle n ≤ (π/4)^(j:ℕ) * max (sphericalAngle 8) (sphericalAngle 9) := by
  obtain ⟨j, hj⟩ := tail_parity_split n hn
  refine ⟨j, hj, ?_⟩
  rcases hj with he | ho
  · rw [he]
    calc sphericalAngle (8 + 2*j)
        ≤ (π/4)^(j:ℕ) * sphericalAngle 8 := sphericalAngle_even_geo j
      _ ≤ (π/4)^(j:ℕ) * max (sphericalAngle 8) (sphericalAngle 9) := by
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · rw [ho]
    calc sphericalAngle (9 + 2*j)
        ≤ (π/4)^(j:ℕ) * sphericalAngle 9 := sphericalAngle_odd_geo j
      _ ≤ (π/4)^(j:ℕ) * max (sphericalAngle 8) (sphericalAngle 9) := by
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- **Collapse телесного угла**: Ω_n → 0 при n → ∞. Гамма-функция
(Γ(n/2) ~ (n/2)!) растёт быстрее π^{n/2}. Формальное ядро тезиса
«после 7D телесный угол быстро стремится к нулю»; непрерывный
максимум Ω в точке n ≈ 7.257, дискретный пик Ω_7 = 16π³/15. -/
theorem sphericalAngle_tendsto_zero :
    Tendsto sphericalAngle atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr0 : (0:ℝ) ≤ π/4 := by positivity
  have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (π/4:ℝ)) hr0
    (by nlinarith [Real.pi_lt_four])
  have hgeo := hbase.mul_const (max (sphericalAngle 8) (sphericalAngle 9))
  -- hgeo : Tendsto (fun j => (π/4)^j * C) atTop (nhds (0 * C))
  have hbig : ∀ n : ℕ, 8 ≤ n → ∃ j, 8 ≤ n ∧ (n = 8 + 2*j ∨ n = 9 + 2*j) ∧
      sphericalAngle n ≤ (π/4)^(j:ℕ) * max (sphericalAngle 8) (sphericalAngle 9) :=
    fun n hn => by
      obtain ⟨j, hj⟩ := tail_parity_split n hn
      refine ⟨j, hn, hj, ?_⟩
      rcases hj with he | ho
      · rw [he]
        exact le_trans (sphericalAngle_even_geo j)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
      · rw [ho]
        exact le_trans (sphericalAngle_odd_geo j)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  -- unfold the tendsto of the geometric envelope via Membership
  have hgeoMem := Metric.tendsto_nhds.mp hgeo ε hε
  -- extract J from the eventually-statement via mem_atTop_sets
  have hEv : ∀ᶠ j in atTop,
      (π/4)^(j:ℕ) * max (sphericalAngle 8) (sphericalAngle 9) < ε :=
    Filter.Eventually.mono hgeoMem (fun j hj => by
      rw [Real.dist_eq, zero_mul, sub_zero] at hj
      rwa [abs_mul, abs_pow, abs_of_pos (show (0:ℝ) < π/4 by positivity),
        abs_of_nonneg (by unfold sphericalAngle; positivity)] at hj)
  obtain ⟨J, hJ⟩ := mem_atTop_sets.mp hEv
  refine mem_atTop_sets.mpr ⟨2*J + 10, ?_⟩
  intro n hn
  have hnJ : (2:ℕ) * J + 10 ≤ n := hn
  have hnn : 8 ≤ n := by omega
  obtain ⟨j, h8n, hpar, hb⟩ := hbig n hnn
  have hJj : J ≤ j := by
    rcases hpar with he | ho
    · omega
    · omega
  have hbound := hJ j hJj
  have habs : |sphericalAngle n| = sphericalAngle n :=
    abs_of_nonneg (by unfold sphericalAngle; positivity)
  simp only [Set.mem_setOf_eq] at *
  rw [Real.dist_eq, sub_zero, habs]
  exact lt_of_le_of_lt hb hbound

/-- Ω_6 = π³ (Γ(3) = 2). -/
theorem sphericalAngle_six : sphericalAngle 6 = π^3 := by
  unfold sphericalAngle
  norm_num [Real.Gamma_two]

/-- Ω_7 = 16π³/15: пик телесного угла (Γ(7/2) = 15√π/8 через
зацепку Γ(x+1) = x·Γ(x) от Γ(1/2) = √π). -/
theorem sphericalAngle_seven : sphericalAngle 7 = 16 * π^3 / 15 := by
  unfold sphericalAngle
  have h3 : Real.Gamma (5/2 : ℝ) = 3/2 * (1/2 * √π) := by
    have h1 : Real.Gamma (1/2 : ℝ) = √π := Gamma_one_half_eq
    have h2 : Real.Gamma (3/2 : ℝ) = (1/2:ℝ) * √π := by
      rw [show (3/2:ℝ) = (1/2:ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num), h1]
    rw [show (5/2:ℝ) = (3/2:ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num), h2]
  have hexp : (π:ℝ) ^ (((7:ℕ):ℝ) / 2) = π^((3:ℝ)) * π^((1:ℝ)/2) := by
    have he : ((7:ℕ):ℝ) / 2 = (3:ℝ) + 1/2 := by norm_num
    rw [he, Real.rpow_add (by positivity)]
  have hg : Real.Gamma (((7:ℕ):ℝ)/2) = 15 * √π / 8 := by
    rw [show ((7:ℕ):ℝ)/2 = (5/2:ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num), h3]
    ring
  have hsq : (π:ℝ) ^ ((1:ℝ)/2) = √π := (Real.sqrt_eq_rpow π).symm
  rw [hexp, hg, hsq]
  field_simp
  have hfin : 2 * π^(3:ℝ) * 8 = 16 * π^(3:ℝ) := by ring
  rw [hfin]
  simp



theorem div6_eq_div3 (x : ℝ) : 2 * x / 6 = x / 3 := by
  field_simp
  ring
theorem pi_lt_16_5' : (π:ℝ) < 16/5 := by linarith [pi_lt_d2]
theorem Omega_8' : sphericalAngle 8 = π^4/3 := by
  unfold sphericalAngle
  have h : Real.Gamma ((4:ℕ):ℝ) = 6 := by norm_num
  rw [show ((8:ℕ):ℝ)/2 = ((4:ℕ):ℝ) from by norm_num, h, Real.rpow_natCast]
  exact div6_eq_div3 (π^4)
theorem Omega_7_gt_Omega_6 : sphericalAngle 6 < sphericalAngle 7 := by
  rw [sphericalAngle_six, sphericalAngle_seven]
  have h3 : (0:ℝ) < π^3 := by positivity
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 15)]
  linarith
theorem Omega_7_gt_Omega_8 : sphericalAngle 8 < sphericalAngle 7 := by
  rw [Omega_8', sphericalAngle_seven]
  have hπ : (π:ℝ) < 16/5 := pi_lt_16_5'
  have h3pos : (0:ℝ) < π^3 := by positivity
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
  rw [show (16:ℝ) * π^3 / 15 * 3 = 16 * π^3 / 5 from by field_simp; ring]
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 5)]
  nlinarith [hπ, h3pos]


/-! ## Дигамма-мосты (R562 шаг 1): ψ-значения в целых точках —
фундамент числового брекета континуального пика x* (ψ(x/2) =
ln π). -/

/-- Гармоническая форма ψ(n+1): значение в точке 3. -/
theorem digamma_three_eq :
    Complex.digamma ((2:ℕ) + 1)
      = ((3:ℚ) / 2 - eulerMascheroniConstant : ℝ) := by
  rw [Complex.digamma_nat_add_one 2]; push_cast [harmonic];
    norm_num [harmonic]

/-- Гармоническая форма ψ(n+1): значение в точке 4. -/
theorem digamma_four_eq :
    Complex.digamma ((3:ℕ) + 1)
      = ((11:ℚ) / 6 - eulerMascheroniConstant : ℝ) := by
  rw [Complex.digamma_nat_add_one 3]; push_cast [harmonic];
    norm_num [harmonic]

/-- Нижняя скобка: ψ(3)-значение ниже ln π при γ > 3/2 − ln π. -/
theorem digamma_three_below_logpi
    (hγlo : (1.5:ℝ) - Real.log Real.pi < eulerMascheroniConstant) :
    (((3:ℚ)/2 : ℝ) - eulerMascheroniConstant) < Real.log Real.pi := by
  linarith

/-- Верхняя скобка: ψ(4)-значение выше ln π при
γ < 11/6 − ln π. -/
theorem digamma_four_above_logpi
    (hγhi : eulerMascheroniConstant < (11:ℝ)/6 - Real.log Real.pi) :
    Real.log Real.pi < (((11:ℚ)/6 : ℝ) - eulerMascheroniConstant) := by
  linarith


/-- Полузначение ψ(1/2) = −2·ln 2 − γ (Mathlib-форма). -/
theorem digamma_half_value :
    Complex.digamma (1/2 : ℂ)
      = -2 * (Complex.log 2) - (eulerMascheroniConstant : ℂ) :=
  Complex.digamma_one_half

/-- Рефлексия Эйлера: ψ(1−s) = ψ(s) + π·cot(π·s) — мост для
симметрии ψ относительно 1/2 (фундамент дубль-формулы и
вилки отрицательных аргументов). -/
theorem digamma_reflection_bridge {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    Complex.digamma (1 - s)
      = Complex.digamma s + (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * s) := by
  exact Complex.digamma_one_sub hs

/-- Рекуррента ψ(s+1) = ψ(s) + 1/s — мост лестницы шагов -/
theorem digamma_recurrence_bridge {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    Complex.digamma (s + 1) = Complex.digamma s + s⁻¹ := by
  exact Complex.digamma_apply_add_one s hs


/-- ψ непрерывна на правой полуплоскости {Re w > 2} (R566):
Γ дифференцируема и ненулевая вне полюсов −ℕ₀, ψ = Γ'/Γ. -/
theorem digamma_continuousOn_right :
    ContinuousOn (fun w : ℂ => Complex.digamma w) {w : ℂ | 2 < w.re} := by
  have hpole : ∀ m : ℕ, ∀ w : ℂ, w = -(m : ℂ) → ¬ (2 : ℝ) < w.re := by
    intro m w hcon
    subst hcon
    have h1 : (-(m:ℂ)).re = -(m:ℝ) := by
      rw [Complex.neg_re]; simp
    rw [h1]
    linarith
  have hD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 2 < w.re} := by
    intro w hw
    have hne : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m hcon =>
      hpole m w hcon hw
    exact (Complex.differentiableAt_Gamma w hne).differentiableWithinAt
  have hAn : AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 2 < w.re} :=
    hD.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hAnD : AnalyticOnNhd ℂ (deriv Complex.Gamma) {w : ℂ | 2 < w.re} :=
    hAn.deriv
  have hcontD : ContinuousOn (deriv Complex.Gamma) {w : ℂ | 2 < w.re} :=
    fun w hw => (hAnD w hw).continuousAt.continuousWithinAt
  have hcontG : ContinuousOn Complex.Gamma {w : ℂ | 2 < w.re} :=
    fun w hw => (hAn w hw).continuousAt.continuousWithinAt
  have hnz : ∀ w ∈ {w : ℂ | 2 < w.re}, Complex.Gamma w ≠ 0 := by
    intro w hw
    exact Complex.Gamma_ne_zero (fun m hcon => hpole m w hcon hw)
  have hdig : Complex.digamma
      = fun w => deriv Complex.Gamma w / Complex.Gamma w := by
    funext w; rw [Complex.digamma_def]; rfl
  rw [hdig]
  exact hcontD.div hcontG hnz

/-- Вещественная ветвь ψ: t ↦ Re ψ(t) непрерывна на [3,4] (R566)
— композиция непрерывного вложения ℝ→ℂ, ψ (непрерывной на
{Re > 2}) и Re. -/
theorem digamma_re_continuousOn :
    ContinuousOn (fun t : ℝ => (Complex.digamma (t : ℂ)).re)
      (Set.Icc 3 4) := by
  have hembed : Continuous (fun t : ℝ => (t : ℂ)) := by fun_prop
  have hrel : ∀ t : ℝ, t ∈ Set.Icc 3 4 → (t : ℂ) ∈ {w : ℂ | 2 < w.re} := by
    intro t ht
    have hre : ((t : ℂ)).re = t := Complex.ofReal_re t
    simp only [Set.mem_ofPred_eq, hre]
    linarith [ht.1]
  have hpsion : ContinuousOn (fun w : ℂ => Complex.digamma w)
      {w : ℂ | 2 < w.re} := digamma_continuousOn_right
  have hcomp1 : ContinuousOn (fun w : ℂ => (Complex.digamma w).re)
      {w : ℂ | 2 < w.re} :=
    (Continuous.continuousOn Complex.continuous_re).comp hpsion
      (fun w _ => Set.mem_univ _)
  exact hcomp1.comp hembed.continuousOn hrel

/-- **IVT корня диагаммы (R566)**: при γ-брекетах
(1.5 − ln π < γ < 11/6 − ln π) существует s ∈ (3,4) с
Re ψ(s) = ln π — фундамент континуального пика x* = 2s ∈ (6,8). -/
theorem digamma_logpi_root_exists
    (hγlo : (1.5:ℝ) - Real.log Real.pi < eulerMascheroniConstant)
    (hγhi : eulerMascheroniConstant < (11:ℝ)/6 - Real.log Real.pi) :
    ∃ s : ℝ, s ∈ Set.Ioo (3:ℝ) 4 ∧
      (Complex.digamma (s:ℂ)).re = Real.log Real.pi := by
  set g : ℝ → ℝ := fun t => (Complex.digamma (t:ℂ)).re with hgdef
  have hcont : ContinuousOn g (Set.Icc (3:ℝ) 4) :=
    digamma_re_continuousOn
  have h3 : g 3 = (3:ℝ)/2 - eulerMascheroniConstant := by
    have h := digamma_three_eq
    have hre := congrArg Complex.re h
    rw [Complex.ofReal_re] at hre
    have hshow : g 3 = (Complex.digamma ((2:ℕ) + 1)).re := by
      norm_num [hgdef]
    rw [hshow]; exact hre
  have h4 : g 4 = (11:ℝ)/6 - eulerMascheroniConstant := by
    have h := digamma_four_eq
    have hre := congrArg Complex.re h
    rw [Complex.ofReal_re] at hre
    have hshow : g 4 = (Complex.digamma ((3:ℕ) + 1)).re := by
      norm_num [hgdef]
    rw [hshow]; exact hre
  have hlo : g 3 < Real.log Real.pi := by
    rw [h3]; exact digamma_three_below_logpi hγlo
  have hhi : Real.log Real.pi < g 4 := by
    rw [h4]; exact digamma_four_above_logpi hγhi
  have hsub := intermediate_value_Ioo (a := (3:ℝ)) (b := 4)
    (by norm_num) hcont
  have hmem : Real.log Real.pi ∈ Set.Ioo (g 3) (g 4) :=
    ⟨hlo, hhi⟩
  obtain ⟨s, hs_in, hs_eq⟩ := hsub hmem
  exact ⟨s, hs_in, hs_eq⟩

/-- **Континуальный пик (R568)**: при γ-брекетах существует
x* ∈ (6,8) с пик-условием Re ψ(x*/2) = ln π — замыкание
корне-теоремы R566 подстановкой x* = 2s. -/
theorem digamma_peak_exists
    (hγlo : (1.5:ℝ) - Real.log Real.pi < eulerMascheroniConstant)
    (hγhi : eulerMascheroniConstant < (11:ℝ)/6 - Real.log Real.pi) :
    ∃ x : ℝ, x ∈ Set.Ioo (6:ℝ) 8 ∧
      (Complex.digamma (x / 2 : ℂ)).re = Real.log Real.pi := by
  obtain ⟨s, hs_in, hs_eq⟩ := digamma_logpi_root_exists hγlo hγhi
  refine ⟨2 * s, ⟨by linarith [hs_in.1, hs_in.2],
    by linarith [hs_in.1, hs_in.2]⟩, ?_⟩
  have hcast : ((2 * s : ℝ) / 2 : ℂ) = (s : ℂ) := by
    push_cast
    field_simp
  rw [hcast]
  exact hs_eq

end Hagi
