import Mathlib
import Hagi.Optimization.AdamBias

/-!
# DDPM: forward-процесс диффузии (источник №39)

Источник №39: Ho, Jain, Abbeel, "Denoising Diffusion
Probabilistic Models" (arXiv 2006.11239). Forward-процесс
x_t = √ᾱ_t·x_0 + √(1−ᾱ_t)·ε: кумулятивный продукт
ᾱ_t = ∏_{s<t} (1−β_s) контролирует баланс сигнал/шум.

Формализованное ядро (строгое):
- `alphaBar`-рекуррентность: ᾱ_{t+1} = ᾱ_t·(1−β_t), ᾱ_0=1;
- `alphaBar_mono`: ᾱ монотонно НЕвозрастает при β ≥ 0 —
  сигнал только затухает;
- `alphaBar_exp_bound`: при равномерном β ∈ (0,1):
  ᾱ_t ≤ (1−β)^t — ЭКСПОНЕНЦИАЛЬНОЕ затухание сигнала:
  forward-процесс быстро переводит в шумовой режим
  (геометрическая скорость).
-/

namespace Hagi.Model.DDPM

/-- Кумулятивный сохранённый сигнал: ᾱ_t = ∏_{s<t}(1−β). -/
noncomputable def alphaBar (β : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ i ∈ Finset.range t, (1 - β i)

/-- Рекуррентность forward-процесса. -/
theorem alphaBar_succ (β : ℕ → ℝ) (t : ℕ) :
    alphaBar β (t + 1) = alphaBar β t * (1 - β t) := by
  unfold alphaBar
  rw [Finset.prod_range_succ]

/-- ᾱ монотонно невозрастает при β ≥ 0. -/
theorem alphaBar_mono (β : ℕ → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hβ1 : ∀ i, β i ≤ 1) (t : ℕ) :
    alphaBar β (t + 1) ≤ alphaBar β t := by
  rw [alphaBar_succ]
  have h1 : 0 ≤ alphaBar β t :=
    Finset.prod_nonneg (fun i _ => by
      have := hβ i
      have := hβ1 i
      nlinarith)
  have h2 : 1 - β t ≤ 1 := by linarith [hβ t]
  nlinarith [h1, h2]

/-- ЭКСПОНЕНЦИАЛЬНОЕ затухание: при постоянном β ∈ (0,1)
ᾱ_t ≤ (1−b)^t — сигнал исчезает геометрически. -/
theorem alphaBar_exp_bound (β : ℕ → ℝ) (b : ℝ) (_hb : 0 < b)
    (hb1 : b < 1) (hβ : ∀ i, b ≤ β i)
    (hβ1 : ∀ i, β i ≤ 1) (t : ℕ) :
    alphaBar β t ≤ (1 - b) ^ t := by
  induction t with
  | zero => simp [alphaBar]
  | succ t ih =>
    rw [alphaBar_succ, pow_succ]
    have hle : 1 - β t ≤ 1 - b := by linarith [hβ t]
    have hnn : 0 ≤ 1 - b := by linarith
    have h0 : 0 ≤ alphaBar β t :=
      Finset.prod_nonneg (fun i _ => by
        have := hβ i
        have := hβ1 i
        nlinarith)
    have hc : 0 ≤ 1 - β t := by
      have := hβ t
      have := hβ1 t
      nlinarith
    exact mul_le_mul ih hle hc (pow_nonneg hnn t)

end Hagi.Model.DDPM
