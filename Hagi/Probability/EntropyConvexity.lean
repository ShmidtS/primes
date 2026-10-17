/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

namespace Hagi.Probability


open Finset Real

open Finset in
/-- **Log-sum неравенство (R451)**:
A·ln(A/B) ≤ Σ a·ln(a/b) для
положительных a, b
(A = Σa, B = Σb).
Вывод: нормализация
a/A, b/B в распределения +
R447 (KL ≥ 0); без Коши-Энгеля.
Классический кирпич
Энтропийной неравенств
цепи и основа
Пинскера/Гиббса-Дюгема. -/
theorem log_sum_ineq {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (a b : V → ℝ)
    (ha : ∀ v, 0 < a v) (hb : ∀ v, 0 < b v) :
    (∑ v : V, a v) * Real.log ((∑ v : V, a v) / (∑ v : V, b v))
      ≤ ∑ v : V, a v * Real.log (a v / b v) := by
  set A : ℝ := ∑ v : V, a v with hA
  set B : ℝ := ∑ v : V, b v with hB
  have hApos : 0 < A :=
    Finset.sum_pos (fun v _ => ha v)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hBpos : 0 < B :=
    Finset.sum_pos (fun v _ => hb v)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set ρ : V → ℝ := fun v => a v / A with hρ
  set γ : V → ℝ := fun v => b v / B with hγ
  have hρpos : ∀ v, 0 < ρ v :=
    fun v => by rw [hρ]; exact div_pos (ha v) hApos
  have hγpos : ∀ v, 0 < γ v :=
    fun v => by rw [hγ]; exact div_pos (hb v) hBpos
  have hρ1 : ∑ v : V, ρ v = 1 := by
    rw [hρ]; simp only; rw [← Finset.sum_div]; exact div_self hApos.ne'
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]; simp only; rw [← Finset.sum_div]; exact div_self hBpos.ne'
  have hKL := finite_kl_nonneg ρ γ hρpos hρ1 hγpos hγ1
  have hexp : ∑ v : V, ρ v * Real.log (ρ v / γ v)
      = (1/A) * (∑ v : V, a v * Real.log (a v / b v))
        + Real.log (B/A) := by
    have hsplit : ∀ v : V, ρ v * Real.log (ρ v / γ v)
        = (1/A) * (a v * Real.log (a v / b v))
          + (a v / A) * Real.log (B/A) := by
      intro v
      have hr : ρ v / γ v = (a v / b v) * (B / A) := by
        rw [hρ, hγ]; field_simp
      have hab : 0 < a v / b v := div_pos (ha v) (hb v)
      have hBA : 0 < B / A := div_pos hBpos hApos
      rw [hr, Real.log_mul hab.ne' hBA.ne', hρ]
      simp only
      field_simp
    have hs1 : ∑ v : V, (1/A) * (a v * Real.log (a v / b v))
        = (1/A) * (∑ v : V, a v * Real.log (a v / b v)) :=
      (Finset.mul_sum Finset.univ
        (fun v => a v * Real.log (a v / b v)) (1/A)).symm
    have hs2 : ∑ v : V, (a v / A) * Real.log (B / A)
        = Real.log (B / A) := by
      rw [← Finset.sum_mul, ← Finset.sum_div,
        div_self hApos.ne', one_mul]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v),
      Finset.sum_add_distrib, hs1, hs2]
  rw [hexp] at hKL
  have hlogneg : Real.log (A / B) = -(Real.log (B / A)) := by
    rw [Real.log_div hApos.ne' hBpos.ne',
      Real.log_div hBpos.ne' hApos.ne']
    ring
  rw [hlogneg]
  have hKLA := mul_nonneg hKL hApos.le
  field_simp at hKLA
  linarith

open Finset in
/-- **Log-sum неравенство на
подмножестве (R452)**:
для s ⊆ V и положительных на s:
(Σ_{v∈s} a)·ln(Σa/Σb) ≤ Σ_{v∈s} a·ln(a/b).
Доказательство:
применение R451 к
подтипу {v // v ∈ s}
(Finset.sum_coe_sort).
Кирпич для
неравенства
обработки данных (KL не
растёт при сжатии по
слоям). -/
theorem log_sum_ineq_on {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty)
    (a b : V → ℝ)
    (ha : ∀ v ∈ s, 0 < a v) (hb : ∀ v ∈ s, 0 < b v) :
    (∑ v ∈ s, a v) * Real.log ((∑ v ∈ s, a v) / (∑ v ∈ s, b v))
      ≤ ∑ v ∈ s, a v * Real.log (a v / b v) := by
  -- subtype carrier
  have hne : Nonempty {v // v ∈ s} := hs.to_subtype
  have hsub := @log_sum_ineq {v // v ∈ s} _ _ hne
    (fun v => a v.val) (fun v => b v.val)
    (fun v => ha v.1 v.2) (fun v => hb v.1 v.2)
  -- convert coe-sort sums to Finset sums
  rw [Finset.sum_coe_sort, Finset.sum_coe_sort] at hsub
  have hlast : ∑ v : {v // v ∈ s}, a v.val * Real.log (a v.val / b v.val)
      = ∑ v ∈ s, a v * Real.log (a v / b v) :=
    Finset.sum_coe_sort s (fun x => a x * Real.log (a x / b x))
  rw [hlast] at hsub
  exact hsub

open Finset in
/-- **Неравенство
обработки данных (R453)**:
KL(Tρḟ‖Tγ) ≤ KL(ρḟ‖γ) для
любого отображения T:
информация только
теряется при
обработке.
Механика:
fiber-разложение
(Finset.sum_fiberwise) + log-sum
почленно по слоям
(R452); пустые слои — нулевой
вклад (log 0 = 0). -/
theorem kl_data_processing {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [Nonempty V]
    (T : V → W)
    (ρ γ : V → ℝ)
    (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1)
    (hγ : ∀ v, 0 < γ v) (hγ1 : ∑ v : V, γ v = 1) :
    (∑ w : W, (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
        * Real.log ((∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
          / (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, γ v)))
    ≤ ∑ v : V, ρ v * Real.log (ρ v / γ v) := by
  -- fiber decomposition: RHS = sum over W of fiber sums
  have hdecomp : (∑ v : V, ρ v * Real.log (ρ v / γ v))
      = ∑ w : W, ∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ,
          ρ v * Real.log (ρ v / γ v) :=
    (Finset.sum_fiberwise Finset.univ T
      (fun v => ρ v * Real.log (ρ v / γ v))).symm
  -- per-fiber log-sum (case split on fiber emptiness)
  have hper : ∀ w : W,
      (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
        * Real.log ((∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, ρ v)
          / (∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ, γ v))
      ≤ ∑ v ∈ Finset.filter (fun v => T v = w) Finset.univ,
          ρ v * Real.log (ρ v / γ v) := by
    intro w
    by_cases hfib : (Finset.filter (fun v => T v = w) Finset.univ).Nonempty
    · exact log_sum_ineq_on _ hfib ρ γ
        (fun v hv => hρ v) (fun v hv => hγ v)
    · -- empty fiber: both sides 0
      have he : Finset.filter (fun v => T v = w) Finset.univ = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hfib
      rw [he]
      simp [Real.log_zero, zero_div]
  rw [hdecomp]
  exact Finset.sum_le_sum (fun w _ => hper w)

open Real in
/-- **Двухточечная
вогнутость ln (R454)**:
λ·ln x + (1−λ)·ln y ≤
ln(λx+(1−λ)y).
Без calculus:
взвешенное AM-GM
(Реал.geom_mean_le_arith_mean2_weighted)
+ монотонность ln.
Кирпич выпуклости KL-
дивергенции. -/
theorem log_concave_two {lam x y : ℝ} (hlam : 0 < lam) (hlam2 : lam < 1)
    (hx : 0 < x) (hy : 0 < y) :
    lam * Real.log x + (1 - lam) * Real.log y
      ≤ Real.log (lam * x + (1 - lam) * y) := by
  have h1 : x ^ lam * y ^ (1 - lam) ≤ lam * x + (1 - lam) * y :=
    Real.geom_mean_le_arith_mean2_weighted hlam.le
      (by linarith : (0:ℝ) ≤ 1 - lam) hx.le hy.le
      (by ring)
  have h2 : Real.log (x ^ lam * y ^ (1 - lam))
      = lam * Real.log x + (1 - lam) * Real.log y := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hx lam).ne'
      (Real.rpow_pos_of_pos hy (1 - lam)).ne',
      Real.log_rpow hx, Real.log_rpow hy]
  rw [← h2]
  exact Real.log_le_log (mul_pos
    (Real.rpow_pos_of_pos hx lam)
    (Real.rpow_pos_of_pos hy (1 - lam))) h1

open Finset Real in
/-- **Выпуклость x·ln x (R455)**:
(λa+(1−λ)b)·ln(λa+(1−λ)b) ≤
λa·ln a + (1−λ)b·ln b.
Доказательство: log-sum (R451)
на Bool-носителе с
α = (λa, (1−λ)b),
β = (λ, 1−λ) (Σβ = 1).
Энтропийная
функция выпукла —
кирпич выпуклости KL-
дивергенции. -/
theorem xlogx_convex {a b lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlam : 0 < lam) (hlam2 : lam < 1) :
    (lam * a + (1 - lam) * b) * Real.log (lam * a + (1 - lam) * b)
      ≤ lam * a * Real.log a + (1 - lam) * b * Real.log b := by
  set α : Bool → ℝ := fun t => if t then lam * a else (1 - lam) * b with hα
  set β : Bool → ℝ := fun t => if t then lam else 1 - lam with hβ
  have hαpos : ∀ t : Bool, 0 < α t := by
    intro t; cases t <;> rw [hα] <;> simp <;> positivity
  have hβpos : ∀ t : Bool, 0 < β t := by
    intro t; cases t <;> rw [hβ] <;> simp <;> linarith
  have hsum := log_sum_ineq α β hαpos hβpos
  have hβ1 : ∑ t : Bool, β t = 1 := by
    rw [hβ]; simp [Fin.sum_univ_two]
  have hα1 : ∑ t : Bool, α t = lam * a + (1 - lam) * b := by
    rw [hα]; simp [Fin.sum_univ_two]
  rw [hβ1, div_one, hα1] at hsum
  have hexp : ∑ t : Bool, α t * Real.log (α t / β t)
      = lam * a * Real.log a + (1 - lam) * b * Real.log b := by
    have hdiv1 : lam * a / lam = a := by
      field_simp
    have hdiv2 : (1 - lam) * b / (1 - lam) = b := by
      field_simp
    rw [hα, hβ]
    simp [hdiv1, hdiv2]
  rw [hexp] at hsum
  exact hsum

open Real in
/-- **Скалярная выпуклость
x·ln(x/y) по x (R456)**:
(λa+(1−λ)b)·ln((λa+(1−λ)b)/y) ≤
λa·ln(a/y) + (1−λ)b·ln(b/y).
Вывод: R455 (z·ln z выпукла)
+ линейность
z·ln y. Кирпич
выпуклости KL по
первому аргументу. -/
theorem xlog_div_convex {a b y lam : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 < y) (hlam : 0 < lam) (hlam2 : lam < 1) :
    (lam * a + (1 - lam) * b)
      * Real.log ((lam * a + (1 - lam) * b) / y)
      ≤ lam * a * Real.log (a / y) + (1 - lam) * b * Real.log (b / y) := by
  have hz : 0 < lam * a + (1 - lam) * b :=
    add_pos (mul_pos hlam ha) (mul_pos (by linarith : (0:ℝ) < 1 - lam) hb)
  have h1 := xlogx_convex ha hb hlam hlam2
  -- expand logs: ln(x/y) = ln x - ln y
  rw [Real.log_div hz.ne' hy.ne', Real.log_div ha.ne' hy.ne',
    Real.log_div hb.ne' hy.ne']
  -- z * (ln z - ln y) = z*ln z - z*ln y; split linear term
  have hsplit : (lam * a + (1 - lam) * b) * Real.log y
      = lam * a * Real.log y + (1 - lam) * b * Real.log y := by
    ring
  rw [mul_sub, hsplit]
  linarith

open Finset Real in
/-- **Выпуклость KL по
первому аргументу (R457)**:
KL(λρ₁+(1−λ)ρ₂ ḟ‖ γ) ≤
λ·KL(ρ₁ḟ‖γ)+(1−λ)·KL(ρ₂ḟ‖γ).
Вывод: почленное R456 +
разделение сумм.
Дуга выпуклости
завершена:
R454→R455→R456→R457. -/
theorem kl_convex_first {V : Type*} [Fintype V] [Nonempty V]
    (ρ₁ ρ₂ γ : V → ℝ) (lam : ℝ)
    (hρ₁ : ∀ v, 0 < ρ₁ v) (hρ₂ : ∀ v, 0 < ρ₂ v)
    (hγ : ∀ v, 0 < γ v)
    (hlam : 0 < lam) (hlam2 : lam < 1) :
    (∑ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
        * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v))
    ≤ lam * (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ v))
      + (1 - lam) * (∑ v : V, ρ₂ v * Real.log (ρ₂ v / γ v)) := by
  have hper : ∀ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
      * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v)
      ≤ lam * (ρ₁ v * Real.log (ρ₁ v / γ v))
        + (1 - lam) * (ρ₂ v * Real.log (ρ₂ v / γ v)) :=
    fun v => by
      have h := xlog_div_convex (hρ₁ v) (hρ₂ v) (hγ v) hlam hlam2
      linarith
  calc (∑ v : V, (lam * ρ₁ v + (1 - lam) * ρ₂ v)
        * Real.log ((lam * ρ₁ v + (1 - lam) * ρ₂ v) / γ v))
      ≤ ∑ v : V, (lam * (ρ₁ v * Real.log (ρ₁ v / γ v))
          + (1 - lam) * (ρ₂ v * Real.log (ρ₂ v / γ v))) :=
        Finset.sum_le_sum (fun v _ => hper v)
    _ = lam * (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ v))
        + (1 - lam) * (∑ v : V, ρ₂ v * Real.log (ρ₂ v / γ v)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

open Finset Real in
/-- **Аддитивность KL на
произведении (R458)**:
KL(ρ₁×ρ₂ ḟ‖ γ₁×γ₂) =
KL(ρ₁ḟ‖γ₁) + KL(ρ₂ḟ‖γ₂)
(цепное правило для
независимых).
Механика: log-
разложение + Fubini
(Fintype.sum_prod_type +
sum_congr/свёртка
строк через
Σρ = 1). -/
theorem kl_product_additive {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W]
    (ρ₁ γ₁ : V → ℝ) (ρ₂ γ₂ : W → ℝ)
    (hρ₁ : ∀ v, 0 < ρ₁ v) (hρ₂ : ∀ w, 0 < ρ₂ w)
    (hγ₁ : ∀ v, 0 < γ₁ v) (hγ₂ : ∀ w, 0 < γ₂ w)
    (hρ₁s : ∑ v : V, ρ₁ v = 1) (hρ₂s : ∑ w : W, ρ₂ w = 1) :
    (∑ p : V × W, (ρ₁ p.1 * ρ₂ p.2)
        * Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2)))
    = (∑ v : V, ρ₁ v * Real.log (ρ₁ v / γ₁ v))
      + (∑ w : W, ρ₂ w * Real.log (ρ₂ w / γ₂ w)) := by
  have hsplit : ∀ p : V × W,
      Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2))
      = (Real.log (ρ₁ p.1) + Real.log (ρ₂ p.2)
          - Real.log (γ₁ p.1) - Real.log (γ₂ p.2)) := by
    intro p
    rw [Real.log_div (mul_pos (hρ₁ p.1) (hρ₂ p.2)).ne'
      (mul_pos (hγ₁ p.1) (hγ₂ p.2)).ne']
    rw [Real.log_mul (hρ₁ p.1).ne' (hρ₂ p.2).ne',
      Real.log_mul (hγ₁ p.1).ne' (hγ₂ p.2).ne']
    ring
  -- expand the summand algebraically
  have hterm : ∀ p : V × W, (ρ₁ p.1 * ρ₂ p.2)
      * Real.log ((ρ₁ p.1 * ρ₂ p.2) / (γ₁ p.1 * γ₂ p.2))
      = ρ₁ p.1 * ρ₂ p.2 * Real.log (ρ₁ p.1)
        + ρ₁ p.1 * ρ₂ p.2 * Real.log (ρ₂ p.2)
        - ρ₁ p.1 * ρ₂ p.2 * Real.log (γ₁ p.1)
        - ρ₁ p.1 * ρ₂ p.2 * Real.log (γ₂ p.2) := by
    intro p
    rw [hsplit p]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  -- Fubini bricks
  have hfibV : ∀ f : V → ℝ, (∑ p : V × W, ρ₁ p.1 * ρ₂ p.2 * f p.1)
      = (∑ v : V, ρ₁ v * f v) := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ₁ (v, w).1 * ρ₂ (v, w).2 * f (v, w).1 = (ρ₁ v * f v) * ρ₂ w
      simp only; ring)]
    rw [← Finset.mul_sum, hρ₂s, mul_one]
  have hfibW : ∀ g : W → ℝ, (∑ p : V × W, ρ₁ p.1 * ρ₂ p.2 * g p.2)
      = (∑ w : W, ρ₂ w * g w) := by
    intro g
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, ρ₁ (v, w).1 * ρ₂ (v, w).2 * g (v, w).2
          = (∑ w : W, ρ₂ w * g w) * ρ₁ v := by
      intro v
      rw [Finset.sum_congr rfl (fun w _ => by
        show ρ₁ (v, w).1 * ρ₂ (v, w).2 * g (v, w).2
          = (ρ₂ w * g w) * ρ₁ v
        simp only; ring)]
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    rw [← Finset.mul_sum, hρ₁s, mul_one]
  rw [hfibV (fun v => Real.log (ρ₁ v)), hfibV (fun v => Real.log (γ₁ v)),
    hfibW (fun w => Real.log (ρ₂ w)), hfibW (fun w => Real.log (γ₂ w))]
  -- split log-div sums
  have hsplit2 : ∀ (f g : V → ℝ), (∀ v, 0 < f v) → (∀ v, 0 < g v) →
      (∑ v : V, f v * Real.log (f v / g v))
      = (∑ v : V, f v * Real.log (f v))
        - (∑ v : V, f v * Real.log (g v)) := by
    intro f g hf hg
    have hpt : ∀ v : V, f v * Real.log (f v / g v)
        = f v * Real.log (f v) - f v * Real.log (g v) := by
      intro v
      rw [Real.log_div (hf v).ne' (hg v).ne', mul_sub]
    rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_sub_distrib]
  have hsplit2W : ∀ (f g : W → ℝ), (∀ w, 0 < f w) → (∀ w, 0 < g w) →
      (∑ w : W, f w * Real.log (f w / g w))
      = (∑ w : W, f w * Real.log (f w))
        - (∑ w : W, f w * Real.log (g w)) := by
    intro f g hf hg
    have hpt : ∀ w : W, f w * Real.log (f w / g w)
        = f w * Real.log (f w) - f w * Real.log (g w) := by
      intro w
      rw [Real.log_div (hf w).ne' (hg w).ne', mul_sub]
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_sub_distrib]
  rw [hsplit2 ρ₁ γ₁ hρ₁ hγ₁, hsplit2W ρ₂ γ₂ hρ₂ hγ₂]
  linarith

open Finset Real in
/-- **Субаддитивность
энтропии (R459)**:
S(совместное) ≤
S(маргинальное по V)
+ S(маргинальное по W).
Вывод через взаимную
информацию: KL(ρ ḟ‖ μ₁×μ₂)
= S₁+S₂−S ≥ 0 (R447);
механика в стиле R458
(Fubini-свёртки).
Классика теории
информации. -/
theorem entropy_subadditive {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    -(∑ p : V × W, ρ p * Real.log (ρ p))
      ≤ -(∑ v : V, (∑ w : W, ρ (v, w)) * Real.log (∑ w : W, ρ (v, w)))
        - (∑ w : W, (∑ v : V, ρ (v, w)) * Real.log (∑ v : V, ρ (v, w))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  set μ₂ : W → ℝ := fun w => ∑ v : V, ρ (v, w) with hμ₂
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  have hμ₂pos : ∀ w, 0 < μ₂ w := by
    intro w
    have := Finset.sum_pos (fun v _ => hρ (v, w))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [hμ₂]; exact this
  -- product of marginals is a distribution
  set γ : V × W → ℝ := fun p => μ₁ p.1 * μ₂ p.2 with hγ
  have hγpos : ∀ p, 0 < γ p := fun p => by
    rw [hγ]; exact mul_pos (hμ₁pos p.1) (hμ₂pos p.2)
  have hμ₁s : ∑ v : V, μ₁ v = 1 := by
    rw [hμ₁, ← Fintype.sum_prod_type]; exact hρ1
  have hμ₂s : ∑ w : W, μ₂ w = 1 := by
    rw [hμ₂, Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hρ1
  have hγ1 : ∑ p : V × W, γ p = 1 := by
    show ∑ p : V × W, μ₁ p.1 * μ₂ p.2 = 1
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, μ₁ (v, w).1 * μ₂ (v, w).2 = μ₁ v := by
      intro v
      simp only []
      rw [← Finset.mul_sum, hμ₂s, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    exact hμ₁s
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  -- expand KL = A - B - C
  have hexp : ∑ p : V × W, ρ p * Real.log (ρ p / γ p)
      = (∑ p : V × W, ρ p * Real.log (ρ p))
        - (∑ p : V × W, ρ p * Real.log (μ₁ p.1))
        - (∑ p : V × W, ρ p * Real.log (μ₂ p.2)) := by
    have hpt : ∀ p : V × W, ρ p * Real.log (ρ p / γ p)
        = ρ p * Real.log (ρ p) - ρ p * Real.log (μ₁ p.1)
          - ρ p * Real.log (μ₂ p.2) := by
      intro p
      rw [hγ]
      rw [Real.log_div (hρ p).ne' (mul_pos (hμ₁pos p.1) (hμ₂pos p.2)).ne']
      rw [Real.log_mul (hμ₁pos p.1).ne' (hμ₂pos p.2).ne']
      ring
    rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  -- Fubini collapse of cross terms
  have hfibV : ∀ f : V → ℝ, (∑ p : V × W, ρ p * f p.1)
      = (∑ v : V, μ₁ v * f v) := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ (v, w) * f (v, w).1 = ρ (v, w) * f v
      simp only)]
    rw [Finset.sum_mul]
  have hfibW : ∀ g : W → ℝ, (∑ p : V × W, ρ p * g p.2)
      = (∑ w : W, μ₂ w * g w) := by
    intro g
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [Finset.sum_congr rfl (fun v _ => by
      show ρ (v, w) * g (v, w).2 = ρ (v, w) * g w
      simp only)]
    rw [← Finset.sum_mul, hμ₂]
  rw [hexp, hfibV (fun v => Real.log (μ₁ v)), hfibW (fun w => Real.log (μ₂ w))] at hKL
  rw [hμ₁] at hKL
  rw [hμ₂] at hKL
  linarith

open Finset Real in
/-- **Цепное правило
энтропии Шеннона (R460)**:
S(V,W) = S(V) + Σᵥ μ₁(v)·S(условная)
— совместная энтропия =
маргинальная + средняя
условная по условному
ядру ρ(v,w)/μ₁(v).
Механика: per-term log-
разделение + Fubini-
свёртки строк/ядер в
стиле R458/R459.
Вместе с R459 — полная
энтропийная арифметика
совместных распределений. -/
theorem entropy_chain {V W : Type*} [Fintype V] [Fintype W]
    [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (∑ p : V × W, ρ p * Real.log (ρ p))
      = (∑ v : V, (∑ w : W, ρ (v, w))
            * Real.log (∑ w : W, ρ (v, w)))
        + (∑ v : V, (∑ w : W, ρ (v, w))
            * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
                * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w))))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  -- per-term split: rho ln rho = rho ln mu1 + rho ln(rho/mu1)
  have hpt : ∀ p : V × W, ρ p * Real.log (ρ p)
      = ρ p * Real.log (μ₁ p.1)
        + μ₁ p.1 * ((ρ p / μ₁ p.1) * Real.log (ρ p / μ₁ p.1)) := by
    intro p
    rw [Real.log_div (hρ p).ne' (hμ₁pos p.1).ne']
    field_simp [(hμ₁pos p.1).ne']
    ring
  rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib]
  -- first sum: Fubini collapse
  have hA : (∑ p : V × W, ρ p * Real.log (μ₁ p.1))
      = (∑ v : V, μ₁ v * Real.log (μ₁ v)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show ρ (v, w) * Real.log (μ₁ (v, w).1) = ρ (v, w) * Real.log (μ₁ v)
      simp only)]
    rw [Finset.sum_mul]
  -- second sum: row-collapse with cond kernel
  have hB : (∑ p : V × W, μ₁ p.1
      * ((ρ p / μ₁ p.1) * Real.log (ρ p / μ₁ p.1)))
      = (∑ v : V, μ₁ v
          * (∑ w : W, (ρ (v, w) / μ₁ v)
              * Real.log (ρ (v, w) / μ₁ v))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.sum_congr rfl (fun w _ => by
      show μ₁ (v, w).1 * ((ρ (v, w) / μ₁ (v, w).1)
          * Real.log (ρ (v, w) / μ₁ (v, w).1))
        = μ₁ v * ((ρ (v, w) / μ₁ v) * Real.log (ρ (v, w) / μ₁ v))
      simp only)]
    rw [← Finset.mul_sum]
  rw [hA, hB]

open Finset Real in
/-- **Лог-сумма
распределения
неположительна (R461a)**:
Σ ρ·ln ρ ≤ 0 при ρ ≤ 1
почленно
(single_le_sum + log-монотонность). -/
theorem dist_log_nonpos {V : Type*} [Fintype V] [Nonempty V]
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v : V, ρ v = 1) :
    (∑ v : V, ρ v * Real.log (ρ v)) ≤ 0 := by
  have hle : ∀ v : V, ρ v ≤ 1 := by
    intro v
    have h1 := Finset.single_le_sum (f := ρ) (fun w _ => (hρ w).le)
      (Finset.mem_univ v)
    rw [hρ1] at h1
    exact h1
  have hpt : ∀ v : V, ρ v * Real.log (ρ v) ≤ 0 := by
    intro v
    have hl : Real.log (ρ v) ≤ Real.log 1 :=
      Real.log_le_log (hρ v) (hle v)
    rw [Real.log_one] at hl
    nlinarith [hρ v, hl]
  exact Finset.sum_nonpos (fun v _ => hpt v)

/-- **Условие не
увеличивает
энтропию (R461)**:
S(V,W) ≥ S(V) — условная
энтропия неотрицательна.
Вывод: цепное правило R460 +
неположительность
лог-сумм условных
строк. -/
theorem joint_entropy_ge_marginal {V W : Type*} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (∑ p : V × W, ρ p * Real.log (ρ p))
    ≤ (∑ v : V, (∑ w : W, ρ (v, w))
        * Real.log (∑ w : W, ρ (v, w))) := by
  rw [entropy_chain ρ hρ hρ1]
  -- row conditionals are distributions; each row log-sum <= 0
  have hrow : ∀ v : V,
      (∑ w : W, ρ (v, w))
        * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
            * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w)))) ≤ 0 := by
    intro v
    have hμ : (0:ℝ) < ∑ w : W, ρ (v, w) :=
      Finset.sum_pos (fun w _ => hρ (v, w))
        ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    have hsum1 : ∑ w : W, ρ (v, w) / (∑ w : W, ρ (v, w)) = 1 := by
      rw [← Finset.sum_div, div_self hμ.ne']
    have hpos : ∀ w : W,
        0 < ρ (v, w) / (∑ w : W, ρ (v, w)) :=
      fun w => div_pos (hρ (v, w)) hμ
    have hnonpos := dist_log_nonpos
      (fun w => ρ (v, w) / (∑ w : W, ρ (v, w))) hpos hsum1
    nlinarith [hμ]
  have hrows : (∑ v : V,
      (∑ w : W, ρ (v, w))
        * (∑ w : W, (ρ (v, w) / (∑ w : W, ρ (v, w)))
            * Real.log (ρ (v, w) / (∑ w : W, ρ (v, w))))) ≤ 0 :=
    Finset.sum_nonpos (fun v _ => hrow v)
  linarith

open Finset Real in
/-- **Тождество свободной
энергии на равновесии (R462)**:
−T·ln Z = ⟨E⟩_γ + T·Σγ ln γ —
F = ⟨E⟩ − T·S в лог-форме
(эквивалент R446 совместно с
PAC-Bayes-выводом).
Механика: per-v
T·γ ln γ = −γE − γ(T ln Z) +
свёртки сумм через
Σγ = 1. -/
theorem gibbs_free_energy_identity {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T) :
    -T * Real.log (∑ v : V, Real.exp (-(E v)/T))
      = (∑ v : V, (Real.exp (-(E v)/T)
            / ∑ v : V, Real.exp (-(E v)/T)) * E v)
        + T * (∑ v : V, (Real.exp (-(E v)/T)
            / ∑ v : V, Real.exp (-(E v)/T))
            * Real.log (Real.exp (-(E v)/T)
              / ∑ v : V, Real.exp (-(E v)/T))) := by
  set Z : ℝ := ∑ v : V, Real.exp (-(E v)/T) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set γ : V → ℝ := fun v => Real.exp (-(E v)/T) / Z with hγ
  have hγpos : ∀ v, 0 < γ v := fun v => by
    rw [hγ]; exact div_pos (exp_pos _) hZpos
  have hγ1 : ∑ v : V, γ v = 1 := by
    rw [hγ]; simp only; rw [← Finset.sum_div]; exact div_self hZpos.ne'
  -- per-term: T * gamma * ln gamma = - gamma * E - gamma * (T ln Z)
  have hpt : ∀ v : V, T * (γ v * Real.log (γ v))
      = -(γ v * E v) - γ v * (T * Real.log Z) := by
    intro v
    rw [hγ, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
    field_simp [(hγpos v).ne', hZpos.ne']
  -- sum the identity
  have hsum : T * (∑ v : V, γ v * Real.log (γ v))
      = -(∑ v : V, γ v * E v)
        - (∑ v : V, γ v) * (T * Real.log Z) := by
    have h1 : T * (∑ v : V, γ v * Real.log (γ v))
        = ∑ v : V, T * (γ v * Real.log (γ v)) := by
      rw [Finset.mul_sum]
    have h2 : (∑ v : V, T * (γ v * Real.log (γ v)))
        = ∑ v : V, (-(γ v * E v) - γ v * (T * Real.log Z)) :=
      Finset.sum_congr rfl (fun v _ => hpt v)
    have h3 : (∑ v : V, (-(γ v * E v) - γ v * (T * Real.log Z)))
        = -(∑ v : V, γ v * E v)
          - (∑ v : V, γ v) * (T * Real.log Z) := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_mul]
    rw [h1, h2, h3, hγ1, one_mul]
  -- conclude
  have hgoalE : (∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T)) * E v)
      = (∑ v : V, γ v * E v) :=
    Finset.sum_congr rfl (fun v _ => rfl)
  have hgoalL : (∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)))
      = (∑ v : V, γ v * Real.log (γ v)) :=
    Finset.sum_congr rfl (fun v _ => rfl)
  have hZZ : Real.log Z
      = Real.log (∑ v : V, Real.exp (-(E v)/T)) := rfl
  rw [hgoalE, hgoalL, ← hZZ]
  rw [hγ1, one_mul] at hsum
  linarith


end Hagi.Probability

export Hagi.Probability (dist_log_nonpos entropy_chain entropy_subadditive gibbs_free_energy_identity joint_entropy_ge_marginal kl_convex_first kl_data_processing kl_product_additive log_concave_two log_sum_ineq log_sum_ineq_on xlog_div_convex xlogx_convex)
