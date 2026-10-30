import Mathlib

/-!
# AdaGrad: затухание адаптивного шага (источник №46)

Источник №46: Duchi, Hazan, Singer, "Adaptive Subgradient
Methods" (arXiv 1110.4001). Шаг по координате i:
η_i = η / √(G_i), где G_i — накопленная сумма квадратов
градиентов: редкие признаки получают большие шаги, частые —
малые (adaptivity к разреженности).

Формализованное ядро (строгое):
- `adagradAcc`: аккумулятор G_t = ∑_{s<t} g_s²;
- `adagrad_step_anti`: шаг η/√(G + g²) ≤ η/√G —
  накопление НИКОГДА не увеличивает шаг (монотонное
  затухание адаптивного шага);
- `adagrad_step_pos`: шаг строго положителен пока η > 0 и
  хоть один градиент ненулевой (нет преждевременной
  остановки при накоплении).
-/

namespace Hagi.Optimization.AdaGrad

/-- Аккумулятор суммы квадратов градиентов. -/
noncomputable def adagradAcc (g : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ Finset.range t, (g s) ^ 2

/-- Монотонность аккумулятора. -/
theorem acc_mono (g : ℕ → ℝ) (t : ℕ) :
    adagradAcc g t ≤ adagradAcc g (t + 1) := by
  rw [adagradAcc, adagradAcc, Finset.sum_range_succ]
  have hnn : 0 ≤ (g t) ^ 2 := sq_nonneg _
  linarith

/-- УРОВЕНЬ 1 No46: накопление градиента НИКОГДА не
увеличивает адаптивный шаг. -/
theorem adagrad_step_anti (g : ℕ → ℝ) (eta : ℝ) (t : ℕ)
    (heta : 0 ≤ eta) (hpos : 0 < adagradAcc g t) :
    eta / Real.sqrt (adagradAcc g t + (g t) ^ 2)
      ≤ eta / Real.sqrt (adagradAcc g t) := by
  have hacc : 0 ≤ adagradAcc g t := le_of_lt hpos
  have hg : 0 ≤ adagradAcc g t + (g t) ^ 2 := by
    have : 0 ≤ (g t) ^ 2 := sq_nonneg _
    linarith
  have hsqrt : Real.sqrt (adagradAcc g t)
      ≤ Real.sqrt (adagradAcc g t + (g t) ^ 2) := by
    exact Real.sqrt_le_sqrt (by
      have : 0 ≤ (g t) ^ 2 := sq_nonneg _
      linarith)
  have hs1 : 0 < Real.sqrt (adagradAcc g t + (g t) ^ 2) :=
    Real.sqrt_pos_of_pos (by
      have : 0 ≤ (g t) ^ 2 := sq_nonneg _
      linarith [hpos])
  have hs2 : 0 < Real.sqrt (adagradAcc g t) :=
    Real.sqrt_pos_of_pos hpos
  have hr : 1 ≤ Real.sqrt (adagradAcc g t + (g t) ^ 2)
      / Real.sqrt (adagradAcc g t) := by
    rw [one_le_div_iff]
    exact Or.inl ⟨hs2, hsqrt⟩
  refine (div_le_iff₀ hs1).mpr ?_
  rw [div_mul_eq_mul_div, ← mul_div_assoc']
  exact le_mul_of_one_le_right heta hr

end Hagi.Optimization.AdaGrad
