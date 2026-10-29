import Mathlib
import Hagi.Model.GRPO
import Hagi.Model.RMSNorm

/-!
# LayerNorm: масштабная инвариантность (источник №21)

Источник №21: Ba, Kiros, Hinton, "Layer Normalization"
(arXiv 1607.06450); RMSNorm (Zhang & Sennrich 1904.10510):
нормировка активаций по слою — стандартный компонент
трансформеров.

Формализованное ядро (строгое): LayerNorm ИНВАРИАНТЕН к
масштабу входа: LN(c·x) = LN(x) при c > 0 — нормировка
выделяет НАПРАВЛЕНИЕ, отбрасывая длину (устойчивость
обучения глубоких сетей к масштабу активаций).
-/

namespace Hagi.Model.LayerNorm

open Real

variable {n : ℕ}

/-- Среднее по слою. -/
noncomputable def mean (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- Дисперсия по слою. -/
noncomputable def variance (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - mean x) ^ 2) / n

/-- LayerNorm-вектор (без аффинных параметров). -/
noncomputable def lnVec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i - mean x) / Real.sqrt (variance x)

/-- Масштаб входа выносится из среднего. -/
theorem mean_smul (x : Fin n → ℝ) (c : ℝ) :
    mean (c • x) = c * mean x := by
  unfold mean
  have h1 : ∑ i, (c • x) i = ∑ i, c * x i :=
    Finset.sum_congr rfl fun i _ => rfl
  have h2 : ∑ i, c * x i = c * ∑ i, x i := (Finset.mul_sum _ _ _).symm
  rw [h1, h2, mul_div_assoc]

/-- Дисперсия однородна второй степени. -/
theorem variance_smul (x : Fin n → ℝ) (c : ℝ) :
    variance (c • x) = c ^ 2 * variance x := by
  have hper : ∀ i : Fin n, (c • x) i - c * mean x
      = c * (x i - mean x) := by
    intro i
    rw [show (c • x) i = c * x i from rfl]
    ring
  have hring : ∀ i : Fin n, (c * (x i - mean x)) ^ 2
      = c ^ 2 * (x i - mean x) ^ 2 := fun i => by ring
  have hsumA : ∑ i, ((c • x) i - c * mean x) ^ 2
      = ∑ i, (c * (x i - mean x)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hper i]
  have hsumB : ∑ i, (c * (x i - mean x)) ^ 2
      = c ^ 2 * ∑ i, (x i - mean x) ^ 2 := by
    calc ∑ i, (c * (x i - mean x)) ^ 2
        = ∑ i, c ^ 2 * (x i - mean x) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hring i
      _ = c ^ 2 * ∑ i, (x i - mean x) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
  unfold variance
  rw [mean_smul, hsumA, hsumB, mul_div_assoc]

/-- ГЛАВНАЯ ТЕОРЕМА: LayerNorm инвариантен к масштабу входа
(c > 0): нормировка выделяет направление, отбрасывая длину. -/
theorem ln_scale_invariant (x : Fin n → ℝ) (c : ℝ) (hc : 0 < c) :
    lnVec (c • x) = lnVec x := by
  funext i
  unfold lnVec
  rw [variance_smul]
  have hs : Real.sqrt (c ^ 2 * variance x) = c * Real.sqrt (variance x) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ c ^ 2),
      Real.sqrt_sq (by positivity : (0:ℝ) ≤ c)]
  rw [hs, mean_smul, show (c • x) i = c * x i from rfl]
  rw [← mul_sub, mul_div_mul_left _ _ hc.ne']

/-- МОСТ №21-№25: разложение дисперсии
variance(x) = ms(x) - (mean x)^2 — LayerNorm-дисперсия есть
RMSNorm-средний квадрат минус квадрат среднего (E[x^2] - E[x]^2).
Реюз groupAdv_sq_decomp (GRPO №33) с c = 0. -/
theorem variance_decomp (x : Fin n → ℝ) (hn : 0 < n) :
    variance x = Hagi.Model.RMSNorm.ms x - (mean x) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hd := Hagi.Model.GRPO.groupAdv_sq_decomp x hn 0
  simp only [sub_zero] at hd
  have hB : ∑ i, (x i - (∑ j, x j) / n) ^ 2
      = ∑ i, (x i) ^ 2 - n * ((∑ j, x j) / n) ^ 2 := by
    linarith [hd]
  unfold variance mean Hagi.Model.RMSNorm.ms
  rw [hB]
  field_simp

/-- УРОВЕНЬ 3 No21: LayerNorm-выход ЦЕНТРИРОВАН:
sum (lnVec x i) = 0 (реюз groupAdv_sum_zero; RMSNorm (No25)
этим НЕ обладает — точный контраст двух нормировок). -/
theorem ln_sum_zero (x : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, lnVec x i = 0 := by
  have hz : ∑ i, (x i - (∑ j, x j) / n) = 0 :=
    Hagi.Model.GRPO.groupAdv_sum_zero x hn
  unfold lnVec
  rw [← Finset.sum_div]
  rw [show (∑ i, (x i - mean x)) = ∑ i, (x i - (∑ j, x j) / n)
    from by simp only [mean]]
  rw [hz, zero_div]

end Hagi.Model.LayerNorm

