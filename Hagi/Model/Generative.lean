/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

/-!
# Генеративное семейство (объединённое)

DDPM и FlowMatching. Имена деклараций сохранены.
-/

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

/-- УРОВЕНЬ 2 No39: ТОЧНОЕ ВОССТАНОВЛЕНИЕ. Если x_t построен
forward-процессом x_t = sqrt(ab)*x_0 + sqrt(1-ab)*eps, то
denoising-предиктор (x_t - sqrt(1-ab)*eps)/sqrt(ab)
ВОССТАНАВЛИВАЕТ x_0 ТОЧНО (при ab > 0) — идеальный
noise-predictor даёт тождественную реконструкцию. -/
theorem ddpm_recover (x0 eps ab : ℝ) (hab : 0 < ab)
    (_hab1 : ab < 1) (xt : ℝ)
    (hfwd : xt = Real.sqrt ab * x0 + Real.sqrt (1 - ab) * eps) :
    (xt - Real.sqrt (1 - ab) * eps) / Real.sqrt ab = x0 := by
  rw [hfwd]
  field_simp
  ring

end Hagi.Model.DDPM

/-!
# Flow Matching: линейный путь (источник №41)

Источник №41: Lipman et al., "Flow Matching for
Generative Modeling" (arXiv 2210.02747). Обучение генерации
через векторные поля: путь x_t = (1−t)·x₀ + t·x₁ —
прямолинейная интерполяция шум→данные с ПОСТОЯННОЙ
скоростью x₁−x₀ (против стохастических SDE-путей DDPM).

Формализованное ядро (строгое):
- `flow_path`: x_t = (1−t)·x₀ + t·x₁;
- `flow_start/flow_end`: endpoints — t=0 даёт x₀, t=1
  даёт x₁ (точная доставка);
- `flow_convex`: при t ∈ [0,1] точка пути лежит МЕЖДУ x₀ и
  x₁ (по каждой координате) — путь не выходит за отрезок;
- `flow_mid`: средняя точка — середина отрезка.
-/

namespace Hagi.Model.FlowMatching

/-- Линейный путь потока. -/
noncomputable def flowPath (x0 x1 t : ℝ) : ℝ :=
  (1 - t) * x0 + t * x1

theorem flow_start (x0 x1 : ℝ) : flowPath x0 x1 0 = x0 := by
  norm_num [flowPath]

theorem flow_end (x0 x1 : ℝ) : flowPath x0 x1 1 = x1 := by
  norm_num [flowPath]

/-- При t ∈ [0,1] путь между endpoints. -/
theorem flow_convex (x0 x1 t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hle : x0 ≤ x1) :
    x0 ≤ flowPath x0 x1 t ∧ flowPath x0 x1 t ≤ x1 := by
  have hdiff : 0 ≤ x1 - x0 := by linarith
  have h1 : flowPath x0 x1 t = x0 + t * (x1 - x0) := by
    unfold flowPath
    ring
  rw [h1]
  have hnn : t * (x1 - x0) ≤ x1 - x0 := by
    rw [mul_comm]
    exact mul_le_of_le_one_right hdiff ht1
  have hpos : 0 ≤ t * (x1 - x0) := mul_nonneg ht0 hdiff
  constructor <;> linarith

theorem flow_mid (x0 x1 : ℝ) :
    flowPath x0 x1 (1 / 2) = (x0 + x1) / 2 := by
  norm_num [flowPath]
  linarith

/-- УРОВЕНЬ 2 No41: ПОСТОЯННАЯ СКОРОСТЬ. Скорость пути
d/dt flowPath = x1 - x0 — НЕ ЗАВИСИТ от t: прямолинейный
поток имеет одну скорость всюду (основа
constant-velocity matching-цели). -/
theorem flow_const_velocity (x0 x1 t : ℝ) :
    HasDerivAt (flowPath x0 x1) (x1 - x0) t := by
  rw [show flowPath x0 x1 = fun s => x0 + (x1 - x0) * s from by
    funext s
    unfold flowPath
    ring]
  simpa using ((hasDerivAt_id t).const_mul (x1 - x0)).const_add x0

end Hagi.Model.FlowMatching
