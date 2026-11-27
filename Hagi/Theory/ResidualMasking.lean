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
  `combinedCost_lt_one_of_is` (`MSE* < MSE_u` ⇒ стоимость строго ниже базовой);
* `masked_importance_unbiased` — оценка `ℓ_b/q_b` с оптимальной propensity
  несмещена на всех окнах, включая покрытые (`selectedLoss_sum_real_support`);
* `masking_residual_le`, `masking_residual_boost8` — честная граница для кода
  (bypass_mask, boost = 8): обход — конечная прибавка к логиту, остаточный
  градиент `σ(−(z+boost)) ≤ e^{−boost} ≈ 3.4e−4` при `z ≥ 0`;
* `covered_propensity_le` — при importance sampling propensity покрытого окна
  ≤ ε/Σ|ℓ| (ε = e^{−boost}): маскирование при нём избыточно.
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

open scoped Classical in
/-- Несмещённость importance-оценки с маскировкой: propensity `q` оптимальна
(`selectedLoss_optimalPropensity`), поэтому на покрытых окнах нуль, а
`selectedLoss_sum_real_support` даёт `Σ q_a·(ℓ_b/q_b·1[a=b]) = ℓ_b` для
всех `b` — покрытые (ℓ_b = 0) вносят ровно 0. -/
theorem masked_importance_unbiased {V : Type*} [Fintype V] (ℓ : V → ℝ)
    (hL : 0 < ∑ i, |ℓ i|) (b : V) :
    ∑ a, (selectedLoss_optimalPropensity ℓ hL a).toReal *
        (if a = b then ℓ a / (selectedLoss_optimalPropensity ℓ hL a).toReal else 0) = ℓ b := by
  classical
  have hsupp : (selectedLoss_optimalPropensity ℓ hL b).toReal ≠ 0 ∨ ℓ b = 0 := by
    by_cases h : ℓ b = 0
    · exact Or.inr h
    · left
      intro h0
      rw [selectedLoss_optimalPropensity_apply] at h0
      have habsp : (0:ℝ) < |ℓ b| := abs_pos.2 h
      have hS : (0:ℝ) < ∑ i, |ℓ i| := hL
      have : (0:ℝ) < |ℓ b| / ∑ i, |ℓ i| := div_pos habsp hS
      linarith
  have h := Hagi.Probability.selectedLoss_sum_real_support
    (fun a => (selectedLoss_optimalPropensity ℓ hL a).toReal) ℓ b hsupp
  exact h

/-- Код (bypass_mask, optimal_lm.py): обход — прибавка `boost` к логиту
правильного байта, `boost = 8` по умолчанию. При конечном `boost` вероятность
`p = 1/(1 + e^{-(z+boost)}) < 1`, остаточный градиент `1 − p = σ(−(z+boost))`:
маскирование — приближение с ошибкой `σ(−(z+boost)) ≤ e^{-boost}` при `z ≥ 0`
(модель не противоречит обходу). -/
theorem masking_residual_le (z boost : ℝ) (hz : 0 ≤ z) (hb : 0 ≤ boost) :
    |1 - 1 / (1 + Real.exp (-(z + boost)))| ≤ Real.exp (-boost) := by
  have h1 : 0 < 1 + Real.exp (-(z + boost)) := by positivity
  rw [abs_of_nonneg (by rw [sub_nonneg]; apply (div_le_one h1).2; linarith [Real.exp_pos (-(z+boost))])]
  rw [show 1 - 1 / (1 + Real.exp (-(z + boost))) = Real.exp (-(z + boost)) / (1 + Real.exp (-(z + boost))) by
    field_simp; ring]
  rw [div_le_iff₀ h1]
  have he : Real.exp (-(z + boost)) ≤ Real.exp (-boost) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith [Real.exp_pos (-(z + boost))]
/-- При `boost = 8`: остаточный градиент ≤ e^{-8} ≈ 3.35e-4. -/
theorem masking_residual_boost8 (z : ℝ) (hz : 0 ≤ z) :
    |1 - 1 / (1 + Real.exp (-(z + 8)))| ≤ Real.exp (-8) :=
  masking_residual_le z 8 hz (by norm_num)

/-- При конечном boost покрытое окно имеет `|ℓ| ≤ ε` (ε = e^{−boost}), и его
оптимальная propensity ≤ ε/Σ|ℓ|: importance sampling сам почти не берёт
покрытые окна — маскирование при нём избыточно (экономит лишь ε-долю). -/
theorem covered_propensity_le {V : Type*} [Fintype V] (ℓ : V → ℝ)
    (hL : 0 < ∑ i, |ℓ i|) (b : V) (ε : ℝ) (hε : 0 ≤ ε) (hb : |ℓ b| ≤ ε) :
    (selectedLoss_optimalPropensity ℓ hL b).toReal ≤ ε / ∑ i, |ℓ i| := by
  rw [selectedLoss_optimalPropensity_apply]
  exact div_le_div_of_nonneg_right hb (le_of_lt hL)

/-- Ограничение дисперсии importance-оценки при капе `q_b ≥ q_min`: для
Бернулли `m_b ~ q_b` второй момент оценки `ℓ_b·m_b/q_b` равен `ℓ_b²/q_b`,
дисперсия `ℓ_b²·(1/q_b − 1) ≤ ℓ_b²·(1/q_min − 1)`. Кап `q ≥ 0.25`
(`q ∝ |ℓ_b|`, нормировка `E[q] = 1`, cap 4) удерживает вес `1/q ≤ 4`. -/
theorem importance_cap_second_moment (ℓ q : ℝ) (hq : 0 < q) :
    q * (ℓ / q) ^ 2 + (1 - q) * 0 ^ 2 = ℓ ^ 2 / q := by
  field_simp [ne_of_gt hq]; ring
theorem importance_cap_variance_bound (ℓ q qmin : ℝ) (hq : qmin ≤ q) (hq0 : 0 < qmin)
    :
    ℓ ^ 2 * (1 / q - 1) ≤ ℓ ^ 2 * (1 / qmin - 1) := by
  have h1 : 1 / q ≤ 1 / qmin := by
    apply one_div_le_one_div_of_le (by linarith) hq
  have h2 : ℓ ^ 2 * (1 / q - 1) ≤ ℓ ^ 2 * (1 / qmin - 1) := by nlinarith [h1]
  exact h2

end Hagi.Theory.ResidualMasking
