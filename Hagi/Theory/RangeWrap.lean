/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.FactLedger

set_option relaxedAutoImplicit false

/-!
# RangeWrap — piecewise range-affine мост

Мост к HAGI_v2 piecewise range-affine
шаблону (`hagi/core.py`, функция `_mod_affine_expr`): синтез
CAESAR-подобных программ на codepoint-алфавитах по формуле
`y = ((x - lo + c) mod m) + lo` — base-offset affine. Внутри
сегмента входов [lo, hi) формула действует, вне — гейт вызывающего
отбраковывает. Python floor-mod для int совпадает с `Int.emod`
(неположительные аргументы дают неотрицательный остаток).

Ядро: `rangeWrap lo c x m = (x - lo + c) % m + lo`; две теоремы.

- `rangeWrap_inrange` — замкнутость: результат всегда в
  [lo, lo + m) при m > 0 (round-robin перенос, алфавит не
  покидается);
- `rangeWrap_fixed_point` — нулевой сдвиг (c mod m = 0) не
  двигает аргумент, уже лежащий в диапазоне.

Обе — мост к Mathlib-леммам `Int.emod_nonneg` /
`Int.emod_lt_of_pos` / `Int.add_emod` / `Int.emod_eq_of_lt`
(недублирование: леммы переиспользуются как есть). Идемпотентность композиции wrap
честно опущена: ненулевой сдвиг меняет аргумент.
-/

namespace Hagi.Theory.RangeWrap

/-- Range-wrap: вернуть x в диапазон [lo, lo + m) со сдвигом c —
формула base-offset affine из HAGI_v2 (там: `((x - lo + c) % m)
+ lo`, применяется к сегментам codepoint-алфавитов). -/
def rangeWrap (lo c x m : ℤ) : ℤ := (x - lo + c) % m + lo

/-- **Замкнутость в диапазон**: при m > 0 результат rangeWrap
всегда лежит в [lo, lo + m) — остаток неотрицателен и меньше m
(round-robin перенос: выход не покидает алфавит). -/
theorem rangeWrap_inrange (lo c x m : ℤ) (hm : 0 < m) :
    lo ≤ rangeWrap lo c x m ∧ rangeWrap lo c x m < lo + m := by
  have h0 : 0 ≤ (x - lo + c) % m := Int.emod_nonneg _ (ne_of_gt hm)
  have h1 : (x - lo + c) % m < m := Int.emod_lt_of_pos _ hm
  unfold rangeWrap
  omega

/-- **Фиксированная точка нулевого сдвига**: если x уже в
[lo, lo + m) и c mod m = 0, то rangeWrap возвращает x без
изменений. -/
theorem rangeWrap_fixed_point (lo c x m : ℤ) (hm : 0 < m)
    (hlo : lo ≤ x) (hhi : x < lo + m) (hc : c % m = 0) :
    rangeWrap lo c x m = x := by
  have hxl : 0 ≤ x - lo := by omega
  have hxr : x - lo < m := by omega
  have h1 : (x - lo) % m = x - lo := Int.emod_eq_of_lt hxl hxr
  unfold rangeWrap
  rw [Int.add_emod, h1, hc, Int.add_zero, h1]
  omega

end Hagi.Theory.RangeWrap
