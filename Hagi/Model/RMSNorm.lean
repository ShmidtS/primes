import Mathlib

/-!
# RMSNorm: масштабная инвариантность и сохранение RMS (источник №25)

Источник №25: Zhang & Sennrich, "Root Mean Square Layer
Normalization" (arXiv 1912.11247). RMSNorm — упрощение
LayerNorm: без вычитания среднего, только масштабная
нормировка x / RMS(x) — стандарт современных LLM
(LLaMA, Mistral). В отличие от LN (№21), RMS не центрирует,
но так же инвариантен к масштабу и даёт единичный RMS
выхода; вычислительно дешевле (нет mean-subtraction).

Формализованное ядро (строгое):
- rn_scale_invariant: RMSNorm(c·x) = RMSNorm(x), c > 0 —
  как LN, выделяет направление, отбрасывая длину;
- rn_unit_rms: выход имеет единичный RMS
  (∑ (rn x i)^2 = n) при x ≠ 0.
-/

namespace Hagi.Model.RMSNorm

open Real

variable {n : ℕ}

/-- Средний квадрат по слою. -/
noncomputable def ms (x : Fin n → ℝ) : ℝ := (∑ i, (x i) ^ 2) / n

/-- RMSNorm-вектор: деление на root-mean-square. -/
noncomputable def rnVec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / sqrt (ms x)

/-- Средний квадрат однороден степени 2. -/
theorem ms_smul (x : Fin n → ℝ) (c : ℝ) :
    ms (c • x) = c ^ 2 * ms x := by
  unfold ms
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  field_simp
  rw [Finset.mul_sum]

/-- Масштабная инвариантность RMSNorm (ядро №25): направление
сохраняется, длина отбрасывается. -/
theorem rn_scale_invariant (x : Fin n → ℝ) (c : ℝ) (hc : 0 < c) :
    rnVec (c • x) = rnVec x := by
  have hms : 0 ≤ ms x := by
    unfold ms
    apply div_nonneg
    · apply Finset.sum_nonneg; intro i _; positivity
    · positivity
  have hsqrt : sqrt (c ^ 2 * ms x) = c * sqrt (ms x) := by
    have hl : 0 ≤ Real.sqrt (c ^ 2 * ms x) := Real.sqrt_nonneg _
    have hr : 0 ≤ c * Real.sqrt (ms x) := by positivity
    have hsl : (Real.sqrt (c ^ 2 * ms x)) ^ 2 = c ^ 2 * ms x :=
      Real.sq_sqrt (by positivity)
    have hsr : (c * Real.sqrt (ms x)) ^ 2 = c ^ 2 * ms x := by
      rw [mul_pow, Real.sq_sqrt hms]
    nlinarith [hsl, hsr, hl, hr]
  funext i
  simp only [rnVec, Pi.smul_apply, smul_eq_mul, ms_smul,
    hsqrt, mul_div_mul_left _ _ hc.ne']

/-- Единичный RMS выхода: ∑ (rn x i)^2 = n при x ≠ 0. -/
theorem rn_unit_rms (x : Fin n → ℝ) (hx : ms x ≠ 0) :
    ∑ i, (rnVec x i) ^ 2 = n := by
  have hms : 0 < ms x := lt_of_le_of_ne (div_nonneg
    (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))
    (by positivity)) (Ne.symm hx)
  have hs : sqrt (ms x) ^ 2 = ms x := Real.sq_sqrt hms.le
  simp only [rnVec, div_pow, ← Finset.sum_div, hs]
  have hmsdef : ms x = (∑ i, (x i) ^ 2) / n := rfl
  rw [hmsdef, div_div_eq_mul_div]
  have hS : (∑ i, (x i) ^ 2) ≠ 0 := by
    intro hc
    apply hx
    rw [hmsdef, hc]
    simp
  exact mul_div_cancel_left₀ (n:ℝ) hS

end Hagi.Model.RMSNorm
