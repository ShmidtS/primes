/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# CodedSizeQAT — почему член «coded size» в функции потерь корректен

cmix-neif-2.0 §4.3: quantization-aware training с членом за кодированный объём
весов на cool-down learning rate — обучаемая версия оси «байты» из
`IdealModel.ideal_is_bytes_minimization`.

* `prefixCode_ge_entropy` — префиксный код по строке (Kraft `Σ e^{-ℓ_j} ≤ 1`)
  имеет среднюю длину не меньше энтропии распределения уровней `H(p)`
  (Jensen: log вогнут); `H(p)` — нижняя граница реального объёма, и её
  минимизация в loss — минимизация честной нижней оценки байт.
* `differentialEntropy_normal` — дифференциальная энтропия `N(0, σ²)` равна
  `log σ + ½·log(2πe)`; `differentialEntropy_normal_mono` — растёт по `σ`:
  член «−H» штрафует разброс весов — то же направление, что баланс норм
  (`GaugeBalance.stock_balance_min`), но выведенное из объёма.
-/

namespace Hagi.Information.CodedSizeQAT

open Finset
variable {n : ℕ}
noncomputable def H (p : Fin n → ℝ) : ℝ := -∑ j, p j * Real.log (p j)
theorem prefixCode_ge_entropy (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
    (ℓ : Fin n → ℝ) (hkraft : (∑ j, Real.exp (-ℓ j)) ≤ 1) :
    H p ≤ ∑ j, p j * ℓ j := by
  classical
  have hc : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hJ := hc.le_map_sum (t := univ) (w := p) (p := fun j => Real.exp (-ℓ j) / p j)
    (fun j _ => (hp j).le) (by exact hpsum) (fun j _ => div_pos (Real.exp_pos _) (hp j))
  simp only [smul_eq_mul] at hJ
  have hsum : (∑ j, p j * (Real.exp (-ℓ j) / p j)) = ∑ j, Real.exp (-ℓ j) := by
    apply Finset.sum_congr rfl; intro j _; field_simp [ne_of_gt (hp j)]
  rw [hsum] at hJ
  have hZ : Real.log (∑ j, Real.exp (-ℓ j)) ≤ 0 :=
    Real.log_nonpos (Finset.sum_nonneg (fun j _ => by positivity)) (le_trans hkraft (by norm_num))
  have hle : (∑ j, p j * Real.log (Real.exp (-ℓ j) / p j)) ≤ 0 := le_trans hJ hZ
  have hlog : ∀ j, Real.log (Real.exp (-ℓ j) / p j) = -ℓ j - Real.log (p j) := by
    intro j; rw [Real.log_div (by positivity) (ne_of_gt (hp j)), Real.log_exp]
  have hsplit : (∑ j, p j * (-ℓ j - Real.log (p j))) = -(∑ j, p j * ℓ j) - ∑ j, p j * Real.log (p j) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl (fun j _ => by rw [hlog j]), hsplit] at hle
  unfold H; linarith

/-- Дифференциальная энтропия `N(0, σ²)`: `log σ + ½·log(2πe)`. -/
noncomputable def diffEntropyNormal (σ : ℝ) : ℝ := Real.log σ + (1 / 2) * Real.log (2 * Real.pi * Real.exp 1)

/-- Энтропия растёт по `σ`: член «−H» в QAT-лоссе штрафует разброс весов. -/
theorem diffEntropyNormal_mono (σ₁ σ₂ : ℝ) (h₁ : 0 < σ₁) (h₂ : σ₁ ≤ σ₂) :
    diffEntropyNormal σ₁ ≤ diffEntropyNormal σ₂ := by
  unfold diffEntropyNormal; have := Real.log_le_log h₁ h₂; linarith

end Hagi.Information.CodedSizeQAT
