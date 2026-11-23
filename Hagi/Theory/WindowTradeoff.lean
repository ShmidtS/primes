/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.CoverageReading

set_option relaxedAutoImplicit false

/-!
# WindowTradeoff — certified trade-off выбора ширины окна (C623)

C618 замкнул total-оптимальность иерархического чтения: при
s = w total = ⌈n/w⌉ — информационный минимум ЛЮБОГО покрытия
(`hier_total_min`, `hier_total_floor`). Здесь закрывается
roadmap C620 top-3: certified trade-off выбора ширины окна w.
Total-стоимость моделируется как

  totalCost(w) = ⌈n/w⌉ · c(w),

где число чтений ⌈n/w⌉ убывает по w, а стоимость чтения одного
окна c(w) РАСТЁТ по w. Формализованы два режима + мост к
иерархии:

- режим (a) `windowCost_fixed_mono`: c(w) = c (фиксированная
  стоимость окна) ⇒ totalCost = c·⌈n/w⌉ монотонно невозрастает
  по w (`ceil_div_anti`) ⇒ оптимально максимальное допустимое
  w = w_max — каждое укрупнение окна бесплатно сокращает число
  чтений;
- режим (b) `windowCost_linear_bounds` /
  `windowCost_linear_near_const`: c(w) = c·w (линейное окно) ⇒
  totalCost = c·(w·⌈n/w⌉) и n ≤ w·⌈n/w⌉ ≤ n + w − 1 —
  total-cost «почти константа»: НЕ зависит от выбора w с
  точностью до c·w (зазор < c·w, нижняя граница c·n едина для
  всех w). УДИВИТЕЛЬНЫЙ вывод: при линейной стоимости чтения
  окна выбор w свободен по total-cost — его делают только
  соображения точности/глубины контекста, не экономия;
- `windowCost_hier`: мост — totalCost равен c·(hierStarts
  n B w w).length, т.е. стоимости реального иерархического
  чтения C618 (total = ⌈n/w⌉ при w ∣ B).

Режим (c) — суперлинейное окно c(w) = a + c·w^α, α > 1 —
formal-часть C628 (квадратичный случай α = 2, покрывающий
bench-default `cost_regime_w`): непрерывная релаксация
  (n/w)·(a + c·w²) = n·(a/w + c·w)
минимизируется AM-GM: a/w + c·w ≥ 2√(a·c) с равенством при
w = √(a/c) (`mixedCost_relax_min`, `mixedCost_relax_min_eq`),
и дискретный totalCost = ⌈n/w⌉·(a+c·w²) наследует нижнюю
границу 2n√(a·c) (`mixedCost_lower`): внутренний оптимум
смешанной стоимости w* = (a/(c·(α−1)))^(1/α) при α=2 равен
√(a/c) — теперь certified. Общий α>1 — вне этого файла
(real calculus deriv+convexOn; honest note в STATUS).
-/

namespace Hagi.Theory.WindowTradeoff

open Hagi.Theory.CoverageReading

/-- Анти-монотонность потолка деления: при 0 < w ≤ w' потолок
⌈n/w'⌉ ≤ ⌈n/w⌉ — более широкое окно требует не БОЛЬШЕ чтений
(k = ⌈n/w⌉ даёт n ≤ k·w ≤ k·w', значит ⌈n/w'⌉ < k+1). Ядро
режима (a) `windowCost_fixed_mono`. -/
theorem ceil_div_anti (n w w' : ℕ) (hw : 0 < w) (hw' : 0 < w') (hle : w ≤ w') :
    (n + w' - 1) / w' ≤ (n + w - 1) / w := by
  have hkm : w * ((n + w - 1) / w) + (n + w - 1) % w = n + w - 1 :=
    Nat.div_add_mod (n + w - 1) w
  have hmod : (n + w - 1) % w < w := Nat.mod_lt _ hw
  have hnle : n ≤ w * ((n + w - 1) / w) := by omega
  have hqw : w * ((n + w - 1) / w) ≤ ((n + w - 1) / w) * w' := by
    have h := Nat.mul_le_mul_right ((n + w - 1) / w) hle
    simpa [Nat.mul_comm] using h
  have hring : ((n + w - 1) / w + 1) * w' = ((n + w - 1) / w) * w' + 1 * w' := by
    ring
  have hlt : n + w' - 1 < ((n + w - 1) / w + 1) * w' := by omega
  have hdiv : (n + w' - 1) / w' < (n + w - 1) / w + 1 :=
    (Nat.div_lt_iff_lt_mul hw').mpr hlt
  omega

/-- **Режим (a) — фиксированная стоимость окна**: c(w) = c ⇒
totalCost(w) = c·⌈n/w⌉ монотонно НЕвозрастает по w: при
0 < w ≤ w_max стоимость максимального окна не превосходит
стоимость любого допустимого (`ceil_div_anti` +
`Nat.mul_le_mul_left`). Certified правило: бери w = w_max —
укрупнение окна бесплатно сокращает число чтений. -/
theorem windowCost_fixed_mono (n c w wmax : ℕ) (hw : 0 < w) (hwmax : 0 < wmax)
    (hle : w ≤ wmax) :
    c * ((n + wmax - 1) / wmax) ≤ c * ((n + w - 1) / w) :=
  Nat.mul_le_mul_left c (ceil_div_anti n w wmax hw hwmax hle)

/-- **Режим (b) — линейное окно, границы**: c(w) = c·w ⇒
totalCost(w) = c·(w·⌈n/w⌉), и n ≤ w·⌈n/w⌉ ≤ n + w − 1
(`Nat.mul_div_le` сверху, `Nat.div_add_mod` + `Nat.mod_lt`
снизу): total-cost зажат в [c·n, c·(n+w)). -/
theorem windowCost_linear_bounds (n w : ℕ) (hw : 0 < w) :
    n ≤ w * ((n + w - 1) / w) ∧ w * ((n + w - 1) / w) ≤ n + w - 1 := by
  have hmul : w * ((n + w - 1) / w) ≤ n + w - 1 := Nat.mul_div_le _ _
  have hkm : w * ((n + w - 1) / w) + (n + w - 1) % w = n + w - 1 :=
    Nat.div_add_mod (n + w - 1) w
  have hmod : (n + w - 1) % w < w := Nat.mod_lt _ hw
  omega

/-- **Режим (b) — w-инвариантность total-cost** (удивительный
результат): при линейной стоимости чтения окна c(w) = c·w
total-cost почти НЕ зависит от выбора ширины: для любых
0 < w1, w1' ширина w1 превышает w1' не более чем на w1 − 1
окно-эквивалентов (обе границы `windowCost_linear_bounds` +
omega). В терминах стоимости: totalCost(w1) ≤ totalCost(w1') +
c·(w1 − 1) и симметрично — выбор w свободен по total-cost, его
делают только точность/глубина контекста. -/
theorem windowCost_linear_near_const (n w1 w2 : ℕ) (hw1 : 0 < w1) (hw2 : 0 < w2) :
    w1 * ((n + w1 - 1) / w1) ≤ w2 * ((n + w2 - 1) / w2) + (w1 - 1) := by
  obtain ⟨hle1, hle2⟩ := windowCost_linear_bounds n w1 hw1
  obtain ⟨hle1', hle2'⟩ := windowCost_linear_bounds n w2 hw2
  omega

/-- **Мост к иерархическому чтению C618**: totalCost(w) в модели
равен c·(hierStarts n B w w).length — стоимости реального
полного чтения (total = ⌈n/w⌉ при w ∣ B, делегат `hier_total_min`
C618: иерархия ДОСТИГАЕТ информационного минимума чтений, на
котором стоит вся модель стоимости этого файла). -/
theorem windowCost_hier (n B w c : ℕ) (hw : 0 < w) (hB : 0 < B) (hdiv : w ∣ B) :
    c * ((n + w - 1) / w) = c * (hierStarts n B w w).length := by
  rw [hier_total_min n B w hw hB hdiv]

/-! ### Режим (c): суперлинейное окно c(w) = a + c·w² (C628)

Непрерывная релаксация totalCost — амортизированная стоимость
n·(a/w + c·w) (расщепление «дешёвые частые чтения vs дорогие
широкие окна») — минимизируется AM-GM; дискретный totalCost
наследует нижнюю границу через ⌈n/w⌉ ≥ n/w. -/

/-- **Режим (c) — квадратичное окно, нижняя граница AM-GM**:
релаксация per-read-стоимости a/w + c·w ≥ 2·√(a·c) при
a, c, w > 0 (AM-GM: (√u − √v)² ≥ 0 для u = a/w, v = c·w,
√u·√v = √(u·v) = √(a·c)). Ядро смешанного режима: минимум
непрерывной релаксации (n/w)·(a + c·w²) = n·(a/w + c·w)
не ниже 2n·√(a·c). -/
theorem mixedCost_relax_min {a c w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hw : 0 < w) : 2 * Real.sqrt (a * c) ≤ a / w + c * w := by
  have hu : 0 ≤ a / w := by positivity
  have hv : 0 ≤ c * w := by positivity
  have key := sq_nonneg (Real.sqrt (a / w) - Real.sqrt (c * w))
  rw [sub_sq, Real.sq_sqrt hu, Real.sq_sqrt hv] at key
  have hmul : Real.sqrt (a / w) * Real.sqrt (c * w) = Real.sqrt (a * c) := by
    rw [← Real.sqrt_mul]
    congr 1
    field_simp
    positivity
  linarith [key, hmul]

/-- **Режим (c) — точка равенства релаксации**: при
w = √(a/c) неравенство `mixedCost_relax_min` обращается в
равенство: обе части a/w и c·w равны √(a·c) (квадраты обеих
равны a·c, injectivity по pow_left_inj₀). Итого внутренний
оптимум квадратичной смешанной стоимости w* = √(a/c) —
certified (bench-случай α = 2 формулы
w* = (a/(c·(α−1)))^(1/α)). -/
theorem mixedCost_relax_min_eq {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    a / Real.sqrt (a / c) + c * Real.sqrt (a / c)
      = 2 * Real.sqrt (a * c) := by
  have hw2 : (Real.sqrt (a / c)) ^ 2 = a / c :=
    Real.sq_sqrt (by positivity)
  have h1 : (a / Real.sqrt (a / c)) ^ 2 = a * c := by
    rw [div_pow, hw2, div_div_eq_mul_div]; field_simp
  have h2 : (c * Real.sqrt (a / c)) ^ 2 = a * c := by
    rw [mul_pow, hw2]; field_simp
  have e1 : a / Real.sqrt (a / c) = Real.sqrt (a * c) := by
    apply (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1
    rw [h1, Real.sq_sqrt (by positivity)]
  have e2 : c * Real.sqrt (a / c) = Real.sqrt (a * c) := by
    apply (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1
    rw [h2, Real.sq_sqrt (by positivity)]
  rw [e1, e2]; ring

/-- **Режим (c) — certified нижняя граница дискретного
totalCost**: totalCost(w) = ⌈n/w⌉·(a + c·w²) ≥ 2n·√(a·c) при
a, c > 0, w > 0. Мост: ⌈n/w⌉ = (n+w−1)/w ≥ n/w
(`windowCost_linear_bounds`, каст в ℝ), множитель a + c·w² > 0,
далее релаксация `mixedCost_relax_min` ×n. Дискретное
равенство в общем случае НЕ достигается (⌈n/w⌉ > n/w при
w ∤ n) — нижняя граница certified, точность определяется
целочисленным argmin bench. -/
theorem mixedCost_lower {n w : ℕ} {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hw : 0 < w) :
    2 * (n : ℝ) * Real.sqrt (a * c)
      ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) := by
  obtain ⟨hle, _⟩ := windowCost_linear_bounds n w hw
  have hcast : (n : ℝ) ≤ (w : ℝ) * ((n + w - 1) / w : ℕ) :=
    by exact_mod_cast hle
  have hw' : (0 : ℝ) < (w : ℕ) := by exact_mod_cast hw
  have hbridge : (n : ℝ) / (w : ℝ) ≤ ((n + w - 1) / w : ℕ) := by
    rw [div_le_iff₀ hw']; linarith
  have hpos : (0 : ℝ) < a + c * (w : ℝ) ^ 2 := by positivity
  have hstep1 : (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2)
      ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hbridge hpos.le
  have hstep2 : (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2)
      = (n : ℝ) * (a / (w : ℝ) + c * (w : ℝ)) := by
    field_simp
  calc 2 * (n : ℝ) * Real.sqrt (a * c)
      ≤ (n : ℝ) * (a / (w : ℝ) + c * (w : ℝ)) :=
        by nlinarith [mixedCost_relax_min (w := (w : ℝ)) ha hc hw']
    _ = (n : ℝ) / (w : ℝ) * (a + c * (w : ℝ) ^ 2) := hstep2.symm
    _ ≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2) := hstep1

end Hagi.Theory.WindowTradeoff
