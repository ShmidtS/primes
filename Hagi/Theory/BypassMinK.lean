/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# BypassMinK — пороги словаря обхода как защита от случайных совпадений

`optimal_lm.py`: BYPASS_T5_MIN = 3, BYPASS_T3_MIN = 6 — запись 5- и 3-байтового
словаря начинает отвечать после стольких одинаковых наблюдений следующего
байта. При случайном источнике (iid равномерные байты на алфавите размера
`V`) вероятность `k` подряд совпадений равна `V` в степени `-(k-1)` (первое наблюдение
свободно).

* `coincidence V k = V^{-(k-1)}`;
* `min3_coincidence` — порог 3: `1/65536 ≈ 1.5e-5`;
* `min6_coincidence` — порог 6: `1/2^40 ≈ 9.1e-13`;
* `coincidence_anti` — монотонность: больше совпадений — реже случайность.
-/

namespace Hagi.Theory.BypassMinK

/-- Порог словаря обхода (BYPASS_T5_MIN = 3, BYPASS_T3_MIN = 6): запись
отвечает после `k` одинаковых наблюдений следующего байта. При случайном
источнике (iid равномерные байты на алфавите размера `V`) вероятность `k`
подряд совпадений равна `V^{-(k-1)}` — первое наблюдение свободно. -/
def coincidence (V k : ℕ) : ℚ := ((V : ℚ) ^ (k - 1))⁻¹
/-- Порог 3: случайное совпадение имеет вероятность `2^{-16} ≈ 1.5e-5`. -/
theorem min3_coincidence : coincidence 256 3 = 1 / 65536 := by
  unfold coincidence; norm_num
/-- Порог 6: `256^{-5} = 2^{-40}` (меньше триллионной). -/
theorem min6_coincidence : coincidence 256 6 = 1 / 1099511627776 := by
  unfold coincidence; norm_num
/-- Монотонность по порогу: больше одинаковых наблюдений — реже случайность. -/
theorem coincidence_anti (V k₁ k₂ : ℕ) (hV : 0 < V) (hk : k₁ ≤ k₂) :
    coincidence V k₂ ≤ coincidence V k₁ := by
  have hV1 : (1:ℚ) ≤ V := by exact_mod_cast hV
  have hpow : ((V : ℚ) ^ (k₁ - 1)) ≤ (V : ℚ) ^ (k₂ - 1) :=
    pow_le_pow_right₀ hV1 (by omega)
  unfold coincidence
  rw [← one_div, ← one_div, div_le_div_iff₀ (pow_pos (by linarith) _) (pow_pos (by linarith) _)]
  simpa using hpow

end Hagi.Theory.BypassMinK
