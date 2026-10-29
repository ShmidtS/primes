import Hagi.Unified.FannesComplete

/-!
# Дистилляция знаний: температурный информационный диал (№19)

Источник №19: Hinton, Vinyals, Dean, "Distilling the
Knowledge in a Neural Network" (arXiv 1503.02531):
перенос знаний teacher → student через SOFT-метки при
температуре T («тёмное знание» — информация о сходстве
классов, отсутствующая в one-hot).

Формализованное ядро (строгое, двухклассовая модель):
softProb x = 1/(1+e^{−x}) — вероятность класса 1 при
нормированном зазоре x = d/T (логит-зазор / температура).

- `soft_dial_max`: x → ∞ (T → 0⁺) ⟹ метка → 1 — one-hot,
  полный бит о классе;
- `soft_dial_zero`: x → 0 (T → ∞) ⟹ метка → 1/2 —
  равномерная, ноль информации о классе;
- `soft_entropy_bound`: информационный бюджет H ≤ ln 2 —
  следствие канонического `shannon_le_log_card`.

Температура непрерывно управляет количеством переносимой
информации — формальное ядро temperature scaling в KD.
-/

namespace Hagi.Unified.Distillation

open Real Filter

/-- Soft-вероятность класса 1 при нормированном зазоре x. -/
noncomputable def softProb (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- Диал в максимум: x → ∞ (T → 0⁺) — one-hot-метка,
полный бит о классе. -/
theorem soft_dial_max : Tendsto softProb atTop (nhds 1) := by
  -- 0 ≤ 1 − p(x) ≤ e^{−x} → 0
  have hlo : ∀ᶠ x in atTop, 1 - softProb x ≤ Real.exp (-x) := by
    filter_upwards with x
    have hden : 0 < 1 + Real.exp (-x) := by positivity
    have hdef : softProb x = 1 / (1 + Real.exp (-x)) := rfl
    have he : 0 < Real.exp (-x) := Real.exp_pos _
    have hsplit : 1 - 1 / (1 + Real.exp (-x))
        = Real.exp (-x) / (1 + Real.exp (-x)) := by
      field_simp
      ring
    rw [hdef, hsplit, div_le_iff₀ hden]
    nlinarith [he]
  have hnn : ∀ᶠ x in atTop, 0 ≤ 1 - softProb x := by
    filter_upwards with x
    have hden : 0 < 1 + Real.exp (-x) := by positivity
    have he : 0 < Real.exp (-x) := Real.exp_pos _
    have hdef : softProb x = 1 / (1 + Real.exp (-x)) := rfl
    rw [hdef, sub_nonneg, div_le_iff₀ hden]
    linarith
  have hz : Tendsto (fun x => Real.exp (-x)) atTop (nhds 0) := by
    have he : Tendsto (fun x : ℝ => Real.exp x) atBot (nhds 0) :=
      tendsto_exp_atBot
    exact he.comp tendsto_neg_atTop_atBot
  have h1 : Tendsto (fun x => 1 - softProb x) atTop (nhds 0) :=
    squeeze_zero' hnn hlo hz
  have h2 := h1.const_sub 1
  simpa using h2

/-- Диал в ноль информации: x → 0 (T → ∞) — метка → 1/2,
равномерное распределение, ноль бит о классе. -/
theorem soft_dial_zero : Tendsto softProb (nhds 0) (nhds (1/2)) := by
  have hcont : Continuous softProb := by
    refine Continuous.div continuous_const (continuous_const.add ?_) ?_
    · exact continuous_exp.comp continuous_neg
    · intro x
      positivity
  convert hcont.tendsto 0 using 2
  norm_num [softProb]

/-- Двоичная энтропия метки. -/
noncomputable def binEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- ИНФОРМАЦИОННЫЙ БЮДЖЕТ дистилляции: H(p) ≤ ln 2 —
следствие канонического `shannon_le_log_card` на двух
классах; максимум достигается на равномерной метке
(диал в ноль информации). -/
theorem soft_entropy_bound (p : ℝ) (hp : 0 < p) (hp2 : p < 1) :
    binEntropy p ≤ Real.log 2 := by
  -- распределение на Bool: [1−p, p]
  set q : Bool → ℝ := fun b => if b then p else 1 - p with hq
  have hqnn : ∀ i, 0 ≤ q i := by
    intro i
    cases i <;> simp [hq] <;> linarith
  have hqsum : ∑ i, q i = 1 := by
    rw [Fintype.sum_bool]
    simp [hq]
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  have hcanon := Hagi.Unified.shannon_le_log_card q hqnn hqsum
  rw [hcard] at hcanon
  -- связать negMulLog-сумму с binEntropy
  have hsplit : ∑ i, Real.negMulLog (q i)
      = binEntropy p := by
    rw [Fintype.sum_bool]
    have hE1 : Real.negMulLog p = -p * Real.log p := by
      unfold Real.negMulLog
      ring
    have hE2 : Real.negMulLog (1 - p) = -(1 - p) * Real.log (1 - p) := by
      unfold Real.negMulLog
      ring
    simp only [hq, ite_true, Bool.false_eq_true, ite_false]
    rw [hE2, hE1]
    unfold binEntropy
    ring
  rw [hsplit] at hcanon
  exact hcanon


/-! ### Attention-масштабирование (источник №23) -/

/-- ПОЧЕМУ 1/√d В ATTENTION (Vaswani et al., arXiv
1706.03762), температурная интерпретация: масштаб логитов
на 1/√размерности держит softmax в МЯГКОЙ ЗОНЕ — для
любого фиксированного зазора s вероятность
softProb (s/√n) → 1/2 при n → ∞ (максимум градиента,
никакого затухания). Композиция `soft_dial_zero` с
√n → ∞. -/
theorem attention_scale_softens (s : ℝ) :
    Filter.Tendsto (fun n : ℕ => softProb (s / Real.sqrt ((n:ℝ))))
      Filter.atTop (nhds (1/2)) := by
  have h1 : Filter.Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun x : ℝ => s / x)
      Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.const_mul s
    convert h using 1
    · ext x
      field_simp
    · simp
  exact soft_dial_zero.comp (h2.comp h1)

/-- КОНТРАСТ: БЕЗ масштабирования при ширине n зазор
растёт как s·n — вероятность САТУРИРУЕТСЯ к 1 (диал в
максимум, градиент затухает): формальное ядро
необходимости 1/√d-скейлинга в attention. -/
theorem attention_no_scale_saturates (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun n : ℕ => softProb (s * (n:ℝ)))
      Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun n : ℕ => s * (n:ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  exact soft_dial_max.comp h1

end Hagi.Unified.Distillation
