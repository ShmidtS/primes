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
honest-набросок в STATUS.md: чистая c·w^α внутреннего оптимума
не имеет (totalCost ≈ c·n·w^(α−1) растёт по w); внутренний
оптимум смешанной стоимости w* = (a/(c·(α−1)))^(1/α) требует
вещественной арифметики — вне Nat-сферы этого файла (KISS).
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

end Hagi.Theory.WindowTradeoff
