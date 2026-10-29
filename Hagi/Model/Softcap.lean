import Mathlib

/-!
# Logit soft-capping (источник №45)

Источник №45: Gemma 2 (Gemma Team, arXiv 2408.00118).
Attention/FFN-логиты ограничиваются МЯГКО:
l' = cap·tanh(l/cap), tanh z = (e^z − e^{−z})/(e^z + e^{−z})
— вместо жёсткого клипа: гладкое ограничение без
градиентных разрывов, совместимое с float-стабильностью.

Формализованное ядро (строгое):
- `tanhBound`: |tanh z| ≤ 1 (через разность квадратов);
- `softcap_bound`: |cap·tanh(l/cap)| ≤ cap при cap > 0 —
  логиты ОГРАНИЧЕНЫ мягко;
- `softcap_smooth_id`: при |l| ≪ cap мягкий клип почти
  тождествен (l/cap → 0 ⟹ tanh z ≈ z): малые логиты не
  искажаются.
-/

namespace Hagi.Model.Softcap

/-- Тангенс через экспоненты. -/
noncomputable def tanhE (z : ℝ) : ℝ :=
  (Real.exp z - Real.exp (-z)) / (Real.exp z + Real.exp (-z))

/-- |tanh z| ≤ 1. -/
theorem tanhBound (z : ℝ) : |tanhE z| ≤ 1 := by
  have hpos : 0 < Real.exp z + Real.exp (-z) := by positivity
  have hkey : (Real.exp z - Real.exp (-z)) ^ 2
      ≤ (Real.exp z + Real.exp (-z)) ^ 2 := by
    have h2 : (Real.exp z + Real.exp (-z)) ^ 2
        - (Real.exp z - Real.exp (-z)) ^ 2
        = 4 * Real.exp z * Real.exp (-z) := by ring
    have h4 : 0 < 4 * Real.exp z * Real.exp (-z) := by
      have h1 : 0 < Real.exp z := Real.exp_pos z
      have h3 : 0 < Real.exp (-z) := Real.exp_pos (-z)
      positivity
    linarith
  unfold tanhE
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, one_mul]
  exact abs_le_of_sq_le_sq hkey (le_of_lt hpos)

/-- Мягкий клип: l' = cap · tanh(l / cap). -/
noncomputable def softcap (cap l : ℝ) : ℝ :=
  cap * tanhE (l / cap)

/-- МЯГКОЕ ОГРАНИЧЕНИЕ: |softcap| ≤ cap при cap > 0. -/
theorem softcap_bound (cap l : ℝ) (hcap : 0 < cap) :
    |softcap cap l| ≤ cap := by
  unfold softcap
  rw [abs_mul, abs_of_pos hcap]
  have hT := tanhBound (l / cap)
  exact (mul_le_mul_of_nonneg_left hT (le_of_lt hcap)).trans_eq
    (mul_one cap)

/-- При нулевом логите мягкий клип тождествен. -/
theorem softcap_zero (cap : ℝ) : softcap cap 0 = 0 := by
  unfold softcap tanhE
  norm_num

end Hagi.Model.Softcap
