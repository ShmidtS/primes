/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

set_option linter.style.header false

namespace Hagi.Optimization

/-!
# PolarExpressCert — скалярный interval-сертификат Newton-Schulz
(Polar-Express, P3 карты C537)

Polar-Express заменяет SVD-ортогонализацию тремя шагами
Newton-Schulz с minimax-коэффициентами (нечётные полиномы
`p(x) = a·x + b·x³ + c·x⁵`). Здесь формализована СКАЛЯРНАЯ
спектральная гарантия — без SVD и без матричной механики.

## Сертифицируемое (honest scope)

Для рационализованных коэффициентов (float → ближайшие ℚ,
знаменатель ≤ 10⁴):

- шаг 1: `(10151/2500, −17483/2500, 9623/2500)`;
- шаг 2: `(5429/2000, −25159/10000, 1963/2500)`;
- шаг 3: `(9473/5000, −1119/1000, 2201/10000)`;

композиция трёх шагов переводит спектральный бокс `[1/1000, 1]`
ТОЧНО (рациональные границы, доказаны, не float-близко) в

  `[9/512, 1049/1024] ≈ [0.0176, 1.0244]`:

  x ∈ [1/1000, 1] → p₁(x) ∈ [1/256, 1313/1024] →
  p₂(p₁(x)) ∈ [5/512, 601/512] → p₃(p₂(p₁(x))) ∈ [9/512, 1049/1024].

Интерпретация: спектрального взрыва нет — верх спектра остаётся
в пределах 2.5% от 1; малые σ остаются малыми.

## Что НЕ сертифицируется (minimax-заметка)

Заявка Polar-Express (CosSim 0.99339 при −40% FLOP) — матричная и
эмпирическая. Здесь сертифицирован только скалярный спектральный
факт: полином-композиция сжимает спектральный диапазон в бокс
вокруг 1 сверху. Численный интервал `[0.9564, 0.9806]` из заявки
НЕ воспроизводится на старте `[1/1000, 1]` (p(0.001) ≈ 0.004 —
малые сингулярные значения не подтягиваются к 1 за 3 шага);
честный финальный интервал — `[9/512, 1049/1024]` (числа —
прогон на рационалах, `.tmp/C545/coeffs.py`). Перенос на
сингулярные значения матрицы (p(σᵢ(A)) через функциональное
исчисление нечётного полинома) — вне масштаба шага; матричное
следствие существовало бы при σᵢ ∈ [1/1000, 1] как поточечное
применение `polar_express_cycle_cert` к каждому σᵢ.

## Механика

p'(x) = Q(x²), Q(y) = a + 3b·y + 5c·y² (квадратичный по y, ветви
вверх). Критические точки иррациональны, поэтому каждый шаг
разбит на монотонные куски с рациональными концами и «зазоры»
шириной 1/1024 вокруг критических точек, закрытые мономиальным
смешанным боксом `p5_monomial_box`. Знаки Q на кусках:
`polarQ_nonneg_left` (Q антимонотонен до вершины),
`polarQ_nonpos_mid` (хорд-тождество Q = хорда − 5c·λ(1−λ)W²),
`polarQ_nonneg_right` (Q монотонен после вершины). Монотонность
p — из знака производной (`monotoneOn_of_deriv_nonneg` /
`antitoneOn_of_deriv_nonpos`).
-/

/-- Полином шага Newton-Schulz: `a·x + b·x³ + c·x⁵`. -/
def p5 (a b c x : ℝ) : ℝ := a * x + b * x ^ 3 + c * x ^ 5

/-- Производная `p5` как квадратичная форма от `y = x²`. -/
def polarQ (a b c y : ℝ) : ℝ := a + 3 * b * y + 5 * c * y ^ 2

theorem hasDerivAt_p5 (a b c x : ℝ) :
    HasDerivAt (p5 a b c) (polarQ a b c (x * x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => a * x) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have h2 : HasDerivAt (fun x : ℝ => b * x ^ 3) (b * (3 * x ^ 2)) x :=
    (hasDerivAt_pow 3 x).const_mul b
  have h3 : HasDerivAt (fun x : ℝ => c * x ^ 5) (c * (5 * x ^ 4)) x :=
    (hasDerivAt_pow 5 x).const_mul c
  have hsum := (h1.add h2).add h3
  unfold p5 polarQ
  convert hsum using 1; ring

/-- `Q ≥ 0` слева от вершины: Q антимонотонен на `[0, E]`
(Q' = 3b + 10c·y ≤ 0 при y ≤ E) и Q(E) ≥ 0. -/
theorem polarQ_nonneg_left (a b c y E : ℝ) (_hc : 0 ≤ c) (_hy : 0 ≤ y)
    (hyE : y ≤ E) (hv : 3 * b + 10 * c * E ≤ 0) (hQ : 0 ≤ polarQ a b c E) :
    0 ≤ polarQ a b c y := by
  have key : polarQ a b c y - polarQ a b c E
      = (y - E) * (3 * b + 5 * c * (y + E)) := by unfold polarQ; ring
  have hs : 3 * b + 5 * c * (y + E) ≤ 0 := by nlinarith
  nlinarith

/-- `Q ≥ 0` справа от вершины: Q монотонен после `D`. -/
theorem polarQ_nonneg_right (a b c y D : ℝ) (_hc : 0 ≤ c) (hyD : D ≤ y)
    (hv : 0 ≤ 3 * b + 10 * c * D) (hQ : 0 ≤ polarQ a b c D) :
    0 ≤ polarQ a b c y := by
  have key : polarQ a b c y - polarQ a b c D
      = (y - D) * (3 * b + 5 * c * (y + D)) := by unfold polarQ; ring
  have hs : 0 ≤ 3 * b + 5 * c * (y + D) := by nlinarith
  nlinarith

/-- `Q ≤ 0` между корнями: хорд-тождество
`Q(y) = λ·Q(Y₁) + (1−λ)·Q(Y₂) − 5c·λ(1−λ)·(Y₂−Y₁)²`. -/
theorem polarQ_nonpos_mid (a b c y Y1 Y2 : ℝ) (hY1 : Y1 ≤ y) (hy2 : y ≤ Y2)
    (hQ1 : polarQ a b c Y1 ≤ 0) (hQ2 : polarQ a b c Y2 ≤ 0) (hc : 0 ≤ c) :
    polarQ a b c y ≤ 0 := by
  rcases eq_or_lt_of_le (le_trans hY1 hy2) with hEq | hlt
  · have hy : y = Y1 := by linarith
    subst hy; exact hQ1
  have hWpos : 0 < Y2 - Y1 := by linarith
  have hlam1 : 0 ≤ (Y2 - y) / (Y2 - Y1) := by
    apply div_nonneg _ (by linarith : (0:ℝ) ≤ Y2 - Y1)
    linarith
  have hlam2 : (Y2 - y) / (Y2 - Y1) ≤ 1 := by
    apply (div_le_one (by linarith : (0:ℝ) < Y2 - Y1)).2
    linarith
  have ident : polarQ a b c y = (Y2 - y) / (Y2 - Y1) * polarQ a b c Y1
      + (1 - (Y2 - y) / (Y2 - Y1)) * polarQ a b c Y2
      - 5 * c * ((Y2 - y) / (Y2 - Y1)) * (1 - (Y2 - y) / (Y2 - Y1))
        * (Y2 - Y1) * (Y2 - Y1) := by
    unfold polarQ; field_simp; ring
  have hcorr : 0 ≤ 5 * c * ((Y2 - y) / (Y2 - Y1)) * (1 - (Y2 - y) / (Y2 - Y1))
      * (Y2 - Y1) * (Y2 - Y1) := by
    have h2 : (0:ℝ) ≤ 1 - (Y2 - y) / (Y2 - Y1) := by linarith
    have h3 : (0:ℝ) ≤ (Y2 - Y1) * (Y2 - Y1) := by nlinarith
    have h5 : (0:ℝ) ≤ 5 * c := by linarith
    nlinarith [mul_nonneg (mul_nonneg h5 hlam1) (mul_nonneg h2 h3)]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam1 hQ1]

/-- Мономиальный смешанный бокс на `[u, v]` (узкие зазоры):
`a ≥ 0, b ≤ 0, c ≥ 0, 0 ≤ u ≤ x ≤ v`. -/
theorem p5_monomial_box (a b c u v x : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hxu : u ≤ x) (hxv : x ≤ v) :
    a * u + b * v ^ 3 + c * u ^ 5 ≤ p5 a b c x ∧
    p5 a b c x ≤ a * v + b * u ^ 3 + c * v ^ 5 := by
  have hx : 0 ≤ x := le_trans hu hxu
  have hv : 0 ≤ v := le_trans hx hxv
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hp3 : 0 ≤ x ^ 3 := by positivity
  have hv3 : 0 ≤ v ^ 3 := by positivity
  have hu5 : 0 ≤ u ^ 5 := by positivity
  have hv5 : 0 ≤ v ^ 5 := by positivity
  have h3 : x ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hx hxv 3
  have h3' : u ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hu hxu 3
  have h5 : u ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ hu hxu 5
  have h5' : x ^ 5 ≤ v ^ 5 := pow_le_pow_left₀ hx hxv 5
  have e1 : a * u ≤ a * x := mul_le_mul (le_refl a) hxu hu ha
  have e2 : b * v ^ 3 ≤ b * x ^ 3 := by nlinarith
  have e5 : c * u ^ 5 ≤ c * x ^ 5 := by nlinarith
  have e1' : a * x ≤ a * v := mul_le_mul (le_refl a) hxv hx ha
  have e2' : b * x ^ 3 ≤ b * u ^ 3 := by nlinarith
  have e5' : c * x ^ 5 ≤ c * v ^ 5 := by nlinarith
  exact ⟨add_le_add (add_le_add e1 e2) e5, add_le_add (add_le_add e1' e2') e5'⟩

/-- Монотонность куска из знака Q на внутренности. -/
theorem p5_monotoneOn_of_Q (a b c u v : ℝ)
    (hQ : ∀ z ∈ Set.Ioo u v, 0 ≤ polarQ a b c (z * z)) :
    MonotoneOn (p5 a b c) (Set.Icc u v) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
  · unfold p5; fun_prop
  · intro z hz
    exact ((hasDerivAt_p5 a b c z).differentiableAt).differentiableWithinAt
  · intro z hz
    rw [(hasDerivAt_p5 a b c z).deriv]
    rw [interior_Icc] at hz
    exact hQ z hz

/-- Антимонотонность куска из знака Q на внутренности. -/
theorem p5_antitoneOn_of_Q (a b c u v : ℝ)
    (hQ : ∀ z ∈ Set.Ioo u v, polarQ a b c (z * z) ≤ 0) :
    AntitoneOn (p5 a b c) (Set.Icc u v) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc u v)
  · unfold p5; fun_prop
  · intro z hz
    exact ((hasDerivAt_p5 a b c z).differentiableAt).differentiableWithinAt
  · intro z hz
    rw [(hasDerivAt_p5 a b c z).deriv]
    rw [interior_Icc] at hz
    exact hQ z hz


section Steps

/-- Общий шаговой сертификат (верхний конец домена в «up»-регионе):
кусочная структура A (up) → зазор G1 → B (down) → зазор G2 → C (up).
Точные границы кусков + мономиальные боксы на зазорах 1/1024. -/
theorem polar_express_step_bound_up (a b c lo hi e1 c1 e2 d1 BL BH : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 0) (hc : 0 ≤ c) (hlo : 0 ≤ lo)
    (hg0 : lo ≤ e1) (hg1 : e1 ≤ c1) (hg2 : c1 ≤ e2) (hg3 : e2 ≤ d1) (hg4 : d1 ≤ hi)
    (hA1 : 3 * b + 10 * c * (e1 * e1) ≤ 0) (hA2 : 0 ≤ polarQ a b c (e1 * e1))
    (hB1 : polarQ a b c (c1 * c1) ≤ 0) (hB2 : polarQ a b c (e2 * e2) ≤ 0)
    (hC1 : 0 ≤ 3 * b + 10 * c * (d1 * d1)) (hC2 : 0 ≤ polarQ a b c (d1 * d1))
    (hn1 : BL ≤ p5 a b c lo) (hn2 : BL ≤ p5 a b c e2) (hn3 : BL ≤ p5 a b c d1)
    (hn4 : BL ≤ a * e1 + b * c1 ^ 3 + c * e1 ^ 5)
    (hn5 : BL ≤ a * e2 + b * d1 ^ 3 + c * e2 ^ 5)
    (hx1 : p5 a b c e1 ≤ BH) (hx2 : p5 a b c c1 ≤ BH) (hx3 : p5 a b c hi ≤ BH)
    (hx4 : a * c1 + b * e1 ^ 3 + c * c1 ^ 5 ≤ BH)
    (hx5 : a * d1 + b * e2 ^ 3 + c * d1 ^ 5 ≤ BH)
    {x : ℝ} (hxlo : lo ≤ x) (hxhi : x ≤ hi) : BL ≤ p5 a b c x ∧ p5 a b c x ≤ BH := by
  have hQA : ∀ z ∈ Set.Ioo lo e1, 0 ≤ polarQ a b c (z * z) := by
    intro z ⟨hz1, hz2⟩
    have hz0 : 0 ≤ z := by linarith
    apply polarQ_nonneg_left a b c (z * z) (e1 * e1) hc (by nlinarith) _ hA1 hA2
    nlinarith
  have hQB : ∀ z ∈ Set.Ioo c1 e2, polarQ a b c (z * z) ≤ 0 := by
    intro z ⟨hz1, hz2⟩
    have hc10 : 0 ≤ c1 := by linarith [hg0, hg1, hlo]
    exact polarQ_nonpos_mid a b c (z * z) (c1 * c1) (e2 * e2)
      (by nlinarith) (by nlinarith) hB1 hB2 hc
  have hQC : ∀ z ∈ Set.Ioo d1 hi, 0 ≤ polarQ a b c (z * z) := by
    intro z ⟨hz1, hz2⟩
    exact polarQ_nonneg_right a b c (z * z) (d1 * d1) hc (by nlinarith) hC1 hC2
  rcases le_or_gt x e1 with hxA | hxA
  · -- кусок A: монотонный рост
    have hmono := p5_monotoneOn_of_Q a b c lo e1 hQA
    have hm : p5 a b c lo ≤ p5 a b c x :=
      hmono ⟨le_refl lo, hg0⟩ ⟨hxlo, hxA⟩ hxlo
    have hM : p5 a b c x ≤ p5 a b c e1 :=
      hmono ⟨hxlo, hxA⟩ ⟨hg0, le_refl e1⟩ hxA
    exact ⟨le_trans hn1 hm, le_trans hM hx1⟩
  rcases le_or_gt x c1 with hxG1 | hxG1
  · -- зазор G1: мономиальный бокс
    have hbox := p5_monomial_box a b c e1 c1 x ha hb hc (by linarith [hlo, hg0])
      (le_of_lt hxA) hxG1
    exact ⟨le_trans hn4 hbox.1, le_trans hbox.2 hx4⟩
  rcases le_or_gt x e2 with hxB | hxB
  · -- кусок B: монотонный спад
    have hanti := p5_antitoneOn_of_Q a b c c1 e2 hQB
    have hm : p5 a b c e2 ≤ p5 a b c x :=
      hanti ⟨le_of_lt hxG1, hxB⟩ ⟨le_trans hg2 (le_refl e2), le_refl e2⟩ hxB
    have hM : p5 a b c x ≤ p5 a b c c1 :=
      hanti ⟨le_refl c1, hg2⟩ ⟨le_of_lt hxG1, hxB⟩ (le_of_lt hxG1)
    exact ⟨le_trans hn2 hm, le_trans hM hx2⟩
  rcases le_or_gt x d1 with hxG2 | hxG2
  · -- зазор G2: мономиальный бокс
    have hbox := p5_monomial_box a b c e2 d1 x ha hb hc
      (by linarith [hlo, hg0, hg1, hg2]) (le_of_lt hxB) hxG2
    exact ⟨le_trans hn5 hbox.1, le_trans hbox.2 hx5⟩
  · -- кусок C: монотонный рост
    have hmono := p5_monotoneOn_of_Q a b c d1 hi hQC
    have hm : p5 a b c d1 ≤ p5 a b c x :=
      hmono ⟨le_refl d1, hg4⟩ ⟨le_of_lt hxG2, hxhi⟩ (le_of_lt hxG2)
    have hM : p5 a b c x ≤ p5 a b c hi :=
      hmono ⟨le_of_lt hxG2, hxhi⟩ ⟨hg4, le_refl hi⟩ hxhi
    exact ⟨le_trans hn3 hm, le_trans hM hx3⟩

/-- Общий шаговой сертификат (нижний конец домена внутри «down»-региона):
кусочная структура A (up) → зазор G1 → B (down до hi). -/
theorem polar_express_step_bound_down_end (a b c lo hi e1 c1 BL BH : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 0) (hc : 0 ≤ c) (hlo : 0 ≤ lo)
    (hg0 : lo ≤ e1) (hg1 : e1 ≤ c1) (hg2 : c1 ≤ hi)
    (hA1 : 3 * b + 10 * c * (e1 * e1) ≤ 0) (hA2 : 0 ≤ polarQ a b c (e1 * e1))
    (hB1 : polarQ a b c (c1 * c1) ≤ 0) (hB2 : polarQ a b c (hi * hi) ≤ 0)
    (hn1 : BL ≤ p5 a b c lo) (hn2 : BL ≤ p5 a b c hi)
    (hn4 : BL ≤ a * e1 + b * c1 ^ 3 + c * e1 ^ 5)
    (hx1 : p5 a b c e1 ≤ BH) (hx2 : p5 a b c c1 ≤ BH)
    (hx4 : a * c1 + b * e1 ^ 3 + c * c1 ^ 5 ≤ BH)
    {x : ℝ} (hxlo : lo ≤ x) (hxhi : x ≤ hi) : BL ≤ p5 a b c x ∧ p5 a b c x ≤ BH := by
  have hQA : ∀ z ∈ Set.Ioo lo e1, 0 ≤ polarQ a b c (z * z) := by
    intro z ⟨hz1, hz2⟩
    have hz0 : 0 ≤ z := by linarith
    apply polarQ_nonneg_left a b c (z * z) (e1 * e1) hc (by nlinarith) _ hA1 hA2
    nlinarith
  have hQB : ∀ z ∈ Set.Ioo c1 hi, polarQ a b c (z * z) ≤ 0 := by
    intro z ⟨hz1, hz2⟩
    have hc10 : 0 ≤ c1 := by linarith [hg0, hg1, hlo]
    exact polarQ_nonpos_mid a b c (z * z) (c1 * c1) (hi * hi)
      (by nlinarith) (by nlinarith) hB1 hB2 hc
  rcases le_or_gt x e1 with hxA | hxA
  · have hmono := p5_monotoneOn_of_Q a b c lo e1 hQA
    have hm : p5 a b c lo ≤ p5 a b c x :=
      hmono ⟨le_refl lo, hg0⟩ ⟨hxlo, hxA⟩ hxlo
    have hM : p5 a b c x ≤ p5 a b c e1 :=
      hmono ⟨hxlo, hxA⟩ ⟨hg0, le_refl e1⟩ hxA
    exact ⟨le_trans hn1 hm, le_trans hM hx1⟩
  rcases le_or_gt x c1 with hxG1 | hxG1
  · have hbox := p5_monomial_box a b c e1 c1 x ha hb hc (by linarith [hlo, hg0])
      (le_of_lt hxA) hxG1
    exact ⟨le_trans hn4 hbox.1, le_trans hbox.2 hx4⟩
  · have hanti := p5_antitoneOn_of_Q a b c c1 hi hQB
    have hm : p5 a b c hi ≤ p5 a b c x :=
      hanti ⟨le_of_lt hxG1, hxhi⟩ ⟨le_trans hg2 (le_refl hi), le_refl hi⟩ hxhi
    have hM : p5 a b c x ≤ p5 a b c c1 :=
      hanti ⟨le_refl c1, hg2⟩ ⟨le_of_lt hxG1, hxhi⟩
        (le_of_lt hxG1)
    exact ⟨le_trans hn2 hm, le_trans hM hx2⟩

end Steps


section Instantiations

/-! ## Шаг 1: `(10151/2500, −17483/2500, 9623/2500)`, спектр `[1/1000, 1]` → `[1/256, 1313/1024]` -/

/-- Сертификат шага 1: минимакс-полином (рационализованный) переводит
спектральный бокс `[1/1000, 1]` в точный рациональный бокс
`[1/256, 1313/1024]`. -/
theorem polar_express_step1_bound {x : ℝ} (hx1 : (1:ℝ)/1000 ≤ x) (hx2 : x ≤ 1) :
    (1:ℝ)/256 ≤ p5 (10151/2500) (-17483/2500) (9623/2500) x ∧
    p5 (10151/2500) (-17483/2500) (9623/2500) x ≤ 1313/1024 := by
  refine polar_express_step_bound_up (10151/2500) (-17483/2500) (9623/2500)
    (1/1000) 1 (513/1024) (257/512) (937/1024) (469/512) (1/256) (1313/1024)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    hx1 hx2

/-! ## Шаг 2: `(5429/2000, −25159/10000, 1963/2500)`, `[1/256, 1313/1024]` → `[5/512, 601/512]` -/

/-- Сертификат шага 2: `[1/256, 1313/1024]` → точный бокс `[5/512, 601/512]`. -/
theorem polar_express_step2_bound {x : ℝ} (hx1 : (1:ℝ)/256 ≤ x) (hx2 : x ≤ 1313/1024) :
    (5:ℝ)/512 ≤ p5 (5429/2000) (-25159/10000) (1963/2500) x ∧
    p5 (5429/2000) (-25159/10000) (1963/2500) x ≤ 601/512 := by
  refine polar_express_step_bound_up (5429/2000) (-25159/10000) (1963/2500)
    (1/256) (1313/1024) (177/256) (709/1024) (615/512) (1231/1024) (5/512) (601/512)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    hx1 hx2

/-! ## Шаг 3: `(9473/5000, −1119/1000, 2201/10000)`, `[5/512, 601/512]` → `[9/512, 1049/1024]` -/

/-- Сертификат шага 3 (нижний конец домена внутри «down»-региона):
`[5/512, 601/512]` → ФИНАЛЬНЫЙ точный бокс `[9/512, 1049/1024]`. -/
theorem polar_express_step3_bound {x : ℝ} (hx1 : (5:ℝ)/512 ≤ x) (hx2 : x ≤ 601/512) :
    (9:ℝ)/512 ≤ p5 (9473/5000) (-1119/1000) (2201/10000) x ∧
    p5 (9473/5000) (-1119/1000) (2201/10000) x ≤ 1049/1024 := by
  refine polar_express_step_bound_down_end (9473/5000) (-1119/1000) (2201/10000)
    (5/512) (601/512) (885/1024) (443/512) (9/512) (1049/1024)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    (by first | (simp only [polarQ, p5]; norm_num1) | norm_num1)
    hx1 hx2

/-- **Polar-Express interval-сертификат (P3)**: композиция трёх
рационализованных minimax Newton-Schulz полиномов переводит
спектральный бокс `[1/1000, 1]` в ТОЧНЫЙ рациональный бокс
`[9/512, 1049/1024] ≈ [0.0176, 1.0244]`. Спектрального взрыва нет:
верх спектра остаётся в пределах 2.5% от 1 (матричная часть —
см. minimax-заметку в шапке модуля). -/
theorem polar_express_cycle_cert {x : ℝ} (hx1 : (1:ℝ)/1000 ≤ x) (hx2 : x ≤ 1) :
    (9:ℝ)/512 ≤ p5 (9473/5000) (-1119/1000) (2201/10000)
        (p5 (5429/2000) (-25159/10000) (1963/2500)
          (p5 (10151/2500) (-17483/2500) (9623/2500) x)) ∧
    p5 (9473/5000) (-1119/1000) (2201/10000)
        (p5 (5429/2000) (-25159/10000) (1963/2500)
          (p5 (10151/2500) (-17483/2500) (9623/2500) x)) ≤ 1049/1024 := by
  have h1 := polar_express_step1_bound hx1 hx2
  have h2 := polar_express_step2_bound h1.1 h1.2
  exact polar_express_step3_bound h2.1 h2.2

/-- Негатив: «плохие» коэффициенты (3, −5, 1) того же знакового
профиля вылетают из положительного спектрального коридора —
p(9/10) = −35451/100000 < 0. Сертификат не vacuous: не любой
полином с a ≥ 0, b ≤ 0, c ≥ 0 удерживает спектр. -/
theorem polar_express_bad_coeff_counterex :
    ¬ (∀ x ∈ Set.Icc ((1:ℝ)/1000) (1:ℝ),
        (0:ℝ) ≤ p5 3 (-5) 1 x) := by
  intro h
  have := h (9/10) ⟨by norm_num, by norm_num⟩
  simp only [p5] at this
  norm_num at this

end Instantiations

end Hagi.Optimization
