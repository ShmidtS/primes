/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ValCost — стоимость валидации: сколько окон проверять

`ADAPTER_VAL_WINDOWS = 4096` — самая дорогая фаза приёма (57 с → 12 с).
Стоимость `cost n = c₁·n + c₂·r(n)`, `r(n) = A/√n + B/n` — EB-радиус
(`PairedGain.radius`): больше окон — дороже проверка, уже граница.

* `inv_sqrt_convex` — неравенство средней точки для `1/√x`: `r` выпукла по `n`;
* `DiscreteConvex`, `discrete_convex_min` — для дискретно выпуклой
  последовательности локальный минимум глобален: `cost(k) ≤ cost(k+1)`
  достаточно, чтобы `k` был оптимумом (первый порядок `cost' = 0`).
-/

namespace Hagi.Probability.ValCost

/-- Неравенство средней точки для `1/√x` на `(0, ∞)`: выпуклость. -/
theorem inv_sqrt_convex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / Real.sqrt ((a + b) / 2) ≤ (1 / Real.sqrt a + 1 / Real.sqrt b) / 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsm : 0 < Real.sqrt ((a + b) / 2) := Real.sqrt_pos.2 (by linarith)
  have hkey : 2 * Real.sqrt a * Real.sqrt b ≤ Real.sqrt ((a + b) / 2) * (Real.sqrt a + Real.sqrt b) := by
    have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hsq2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hmul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := (Real.sqrt_mul ha.le b).symm
    have hmid : Real.sqrt ((a + b) / 2) ^ 2 = (a + b) / 2 := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt ((a+b)/2) * (Real.sqrt a + Real.sqrt b) - 2 * Real.sqrt a * Real.sqrt b)]
  have hprod : (0:ℝ) < Real.sqrt a * Real.sqrt b := mul_pos hsa hsb
  have hsum : (0:ℝ) < Real.sqrt a + Real.sqrt b := by linarith
  have hprod : (0:ℝ) < Real.sqrt a * Real.sqrt b := mul_pos hsa hsb
  have hsum : (0:ℝ) < Real.sqrt a + Real.sqrt b := by linarith
  rw [div_le_iff₀ hsm]
  have hthis : (1 / Real.sqrt a + 1 / Real.sqrt b) / 2
      = (Real.sqrt a + Real.sqrt b) / (2 * Real.sqrt a * Real.sqrt b) := by
    field_simp [ne_of_gt hsa, ne_of_gt hsb]; ring
  rw [hthis, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt a * Real.sqrt b)]
  nlinarith [hkey]

/-- Дискретная выпуклость: `f (k+1) − f k` не убывает. -/
def DiscreteConvex (f : ℕ → ℝ) : Prop := ∀ k, f (k+1) - f k ≤ f (k+2) - f (k+1)
/-- Для дискретно выпуклой `f` локальный минимум глобален. -/
theorem discrete_convex_min (f : ℕ → ℝ) (hf : DiscreteConvex f) (k : ℕ)
    (h1 : f k ≤ f (k+1)) : ∀ j, k ≤ j → f k ≤ f j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact le_refl _
  | succ j hj ih =>
    have hstep : f (j+1) - f j ≥ f (k+1) - f k := by
      have : ∀ m, k ≤ m → m ≤ j → f (m+1) - f m ≥ f (k+1) - f k := by
        intro m hm hmk
        induction m, hm using Nat.le_induction with
        | base => exact le_refl _
        | succ m hm ihm =>
          have := hf m
          have hle := ihm (Nat.le_of_succ_le hmk)
          linarith
      exact this j hj (le_refl j)
    linarith [ih]
/-- Стоимость валидации: `c₁·n + c₂·r(n)`. -/
noncomputable def cost (c₁ c₂ A B : ℝ) (n : ℕ) : ℝ :=
  c₁ * n + c₂ * (A / Real.sqrt n + B / n)

end Hagi.Probability.ValCost
