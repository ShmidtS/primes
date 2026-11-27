/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Probability.MirrorHedgeMWU

/-!
# ResidualMasking — маскирование градиента на покрытых `ExactBypass` позициях

`ExactBypass` (ce_total_eq_residual, bypass_reaches_compression_limit): при
уверенном прогнозе `p = 1` вклад в CE равен 0, нейронный проход на покрытых
позициях пропускается. При обучении градиент на покрытых позициях маскируется
(`residual_masking`): градиент категориальной CE по логиту есть
`softmax(z)_c − 1[c = y]`; при вероятностях, равных one-hot, он равен нулю по
всем логитам, поэтому маскирование — тождество, а не приближение, и экономит
долю вычислений градиента, равную доле покрытых позиций.

* `gradCE p y c = p c − 1[c = y]`;
* `gradCE_zero_of_onehot` — при `p = one-hot` все `gradCE = 0`;
* `covered_grad_zero` — скалярная форма (`p = 1 ⇒ p − 1 = 0`);
* `masked_compute_split`, `masked_saving_frac` — экономия `(N − cov)/N`;
* `covered_window_propensity_zero`, `covered_fraction_zero_propensity` — мост к
  importance sampling (`selectedLoss_optimalPropensity`): окно с `ℓ = 0`
  получает нулевую propensity, вся масса сэмплирования — на непокрытых окнах;
* `combinedCost ρ v = (1 − ρ)·v` — доля вычисляемых градиентов на относительную
  дисперсию; `combinedCost_le_one`, `combinedCost_lt_one`,
  `combinedCost_lt_one_of_is` (`MSE* < MSE_u` ⇒ стоимость строго ниже базовой).
-/

namespace Hagi.Theory.ResidualMasking
open Hagi.Probability

/-- Градиент категориальной CE по логиту класса `c` при метке `y`:
`softmax(z)_c − 1[c = y]` (стандартная формула; `p` — вероятности softmax). -/
noncomputable def gradCE {n : ℕ} (p : Fin n → ℝ) (y c : Fin n) : ℝ :=
  p c - if c = y then 1 else 0
/-- Уверенный прогноз (вероятности равны one-hot): градиент по всем логитам
равен нулю — маскирование (обнуление) градиента на покрытой позиции точно. -/
theorem gradCE_zero_of_onehot {n : ℕ} (p : Fin n → ℝ) (y : Fin n)
    (hp : p = fun c => if c = y then 1 else 0) : ∀ c, gradCE p y c = 0 := by
  intro c
  unfold gradCE
  simp [hp, gradCE]
/-- Скалярная форма: `p = 1` ⇒ `p − 1 = 0` (бинарный случай, `cePoint 1 = 0`). -/
theorem covered_grad_zero (p : ℝ) (hp : p = 1) : p - 1 = 0 := by rw [hp]; ring
/-- Экономия: маскированный проход вычисляет градиенты только на `N − cov`
непокрытых позициях; сумма долей = `N`. -/
theorem masked_compute_split (N cov : ℕ) (hcov : cov ≤ N) : (N - cov) + cov = N := by omega
/-- Доля сэкономленных вычислений градиента равна доле покрытых позиций. -/
theorem masked_saving_frac (N cov : ℕ) (hN : 0 < N) (hcov : cov ≤ N) :
    (N - cov) / (N : ℝ) = 1 - cov / (N : ℝ) := by
  have : (cov : ℝ) ≤ N := by exact_mod_cast hcov
  have : (0:ℝ) < N := by exact_mod_cast hN
  push_cast
  field_simp

/-- Окно, полностью покрытое bypass (`ℓ b = 0`), получает нулевую оптимальную
пропенсити и никогда не сэмплируется — нули не входят в `MSE*`. -/
theorem covered_window_propensity_zero {V : Type*} [Fintype V] (ℓ : V → ℝ)
    (hL : 0 < ∑ i, |ℓ i|) (b : V) (hb : ℓ b = 0) :
    (selectedLoss_optimalPropensity ℓ hL b).toReal = 0 := by
  rw [selectedLoss_optimalPropensity_apply, hb, abs_zero, zero_div]
/-- Экономия сэмплирования: суммарная propensity всех покрытых окон равна 0. -/
theorem covered_fraction_zero_propensity {V : Type*} [Fintype V] (ℓ : V → ℝ)
    (hL : 0 < ∑ i, |ℓ i|) (Z : Finset V) (hZ : ∀ b ∈ Z, ℓ b = 0) :
    ∑ b ∈ Z, (selectedLoss_optimalPropensity ℓ hL b).toReal = 0 :=
  Finset.sum_eq_zero fun b hb => covered_window_propensity_zero ℓ hL b (hZ b hb)

/-- Комбинированная стоимость шага: доля вычисляемых градиентов `(1 − ρ)`
на относительную дисперсию оценки `v = MSE*/MSE_uniform` (за шаг нужно
`1/v`-кратно меньше выборок для той же точности). -/
noncomputable def combinedCost (ρ v : ℝ) : ℝ := (1 - ρ) * v
/-- При `0 ≤ ρ < 1`, `v ≤ 1` — стоимость не выше базовой; при `ρ > 0` или
`v < 1` — строго ниже. -/
theorem combinedCost_le_one (ρ v : ℝ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1) (hv : 0 ≤ v) (hv2 : v ≤ 1) :
    combinedCost ρ v ≤ 1 := by
  unfold combinedCost
  nlinarith [mul_nonneg (sub_nonneg.2 hρ2) hv]
theorem combinedCost_lt_one (ρ v : ℝ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1) (hv : 0 ≤ v) (hv2 : v ≤ 1)
    (h : 0 < ρ ∨ v < 1) : combinedCost ρ v < 1 := by
  unfold combinedCost
  rcases eq_or_lt_of_le hρ2 with h1 | h1
  · subst h1; simp
  · rcases h with h | h
    · nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h)]
    · have := mul_lt_mul_of_pos_left h (sub_pos.mpr h1)
      nlinarith
/-- Importance sampling: `v = MSE*/MSE_u < 1` при неоднородных градиентах
(`selectedMeanGradientMSE_optimalPropensity_lt_uniform_iff`); вместе с маскировкой
`ρ > 0` — комбинированная стоимость шага строго ниже базовой. -/
theorem combinedCost_lt_one_of_is (ρ Ms Mu : ℝ) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1)
    (hMu : 0 < Mu) (hMs : 0 ≤ Ms) (hlt : Ms < Mu) :
    combinedCost ρ (Ms / Mu) < 1 := by
  apply combinedCost_lt_one ρ (Ms / Mu) hρ hρ2 (div_nonneg hMs hMu.le) (div_le_one hMu |>.2 hlt.le)
  exact Or.inr ((div_lt_one hMu).2 hlt)

end Hagi.Theory.ResidualMasking
