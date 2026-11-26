/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# AdamSNR — Adam как функция SNR и связь с g-SNR-скейлингом (SGD-SaI)

Второй момент Adam — половина памяти оптимизатора на таблицах
(`v_v` в optimal_lm.py). SGD-SaI (Xu et al. 2024, arXiv 2412.11768) заменяет
его lr-скейлингом по SNR градиента на инициализации. Для стационарного
градиента `g ~ (μ, σ²)`: `m̂ → μ`, `v̂ → μ² + σ²`.

* `adamFactor μ σ = μ/√(μ²+σ²)` — стационарный множитель Adam;
* `adamFactor_abs_le_one` — насыщение: `|adamFactor| ≤ 1` при любом SNR;
* `adamFactor_snr_le` — малый SNR (`|μ| ≤ εσ`) даёт `|adamFactor| ≤ ε`;
* `adamFactor_eq_snr_scale` — `adamFactor = (μ/σ)/√(1+(μ/σ)²)`: SaI-фактор
  `μ/σ` с множителем `1/√(1+SNR²) ≤ 1`.

Следствие: при малом SNR Adam ≈ SaI в первом порядке; при большом Adam
насыщается (шаг ≤ lr), SaI растёт линейно — SaI без второго момента
безопасен только в режиме малого SNR.

* `adam_le_clipped` — клиппированный SaI-фактор `min(s,1)` доминирует Adam;
* `clipped_le_sqrt2_adam` / `_high` — при `s ≤ 1` и при `s ≥ 1` он в пределах `√2`
  от Adam (везде, т.е. клиппированный фактор ≈ Adam с точностью √2).
Клиппированный g-SNR-шаг — замена Adam без второго момента (proposal 15).

* `snrEstimate` — оценка SNR по списку касаний строки (частота касаний в неё
  не входит); `adam_not_invariant` — второй момент Adam, напротив, зависит
  от простоя `d` между касаниями: g-SNR-скейлинг решает и проблему редких
  строк (proposal 14), без хранения `v`.
-/

namespace Hagi.Step.AdamSNR

/-- Стационарный Adam-шаг для градиента с mean μ и std σ (m̂ → μ, v̂ → μ²+σ²):
`μ / √(μ² + σ²) = sign μ · SNR/√(1+SNR²)`, `SNR = |μ|/σ`. -/
noncomputable def adamFactor (μ σ : ℝ) : ℝ := μ / Real.sqrt (μ ^ 2 + σ ^ 2)
/-- SaI-фактор: `lr·SNR·g`, для `g ≈ μ` — шаг `μ·|μ|/σ` (линейный по SNR). -/
noncomputable def saiFactor (μ σ : ℝ) : ℝ := μ * |μ| / σ
/-- Adam-фактор ограничен 1 по модулю (насыщение) при `σ > 0`. -/
theorem adamFactor_abs_le_one (μ σ : ℝ) (hσ : 0 < σ) : |adamFactor μ σ| ≤ 1 := by
  unfold adamFactor
  rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by nlinarith [sq_nonneg μ, sq_nonneg σ]))]
  have h : |μ| ≤ Real.sqrt (μ ^ 2 + σ ^ 2) := by
    apply (Real.le_sqrt (abs_nonneg _) (by nlinarith [sq_nonneg μ, sq_nonneg σ])).2
    nlinarith [sq_abs μ]
  have hden : 0 < Real.sqrt (μ ^ 2 + σ ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg μ, sq_nonneg σ])
  exact (div_le_one hden).2 h
/-- Малый SNR: Adam-фактор `≈ μ/σ` (SaI в первом порядке). Точная граница:
`|μ|/√(μ²+σ²) ≥ |μ|/√(σ²(1+ε²)) = (|μ|/σ)/√(1+ε²)` при `|μ| ≤ εσ`. -/
theorem adamFactor_snr_le (μ σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε)
    (hμ : |μ| ≤ ε * σ) : |adamFactor μ σ| ≤ ε := by
  unfold adamFactor
  rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by nlinarith [sq_nonneg μ, sq_nonneg σ]))]
  have hs : σ ≤ Real.sqrt (μ ^ 2 + σ ^ 2) := by
    apply (Real.le_sqrt hσ.le (by nlinarith [sq_nonneg μ, sq_nonneg σ])).2
    nlinarith [sq_nonneg μ]
  calc |μ| / Real.sqrt (μ ^ 2 + σ ^ 2) ≤ |μ| / σ := div_le_div₀ (abs_nonneg μ) (le_refl _) hσ hs
    _ ≤ ε * σ / σ := (div_le_div_of_nonneg_right hμ hσ.le)
    _ = ε := by field_simp
/-- Первый порядок: `adamFactor μ σ = (μ/σ)·(1/√(1+SNR²))` — множитель `≤ 1`. -/
theorem adamFactor_eq_snr_scale (μ σ : ℝ) (hσ : 0 < σ) :
    adamFactor μ σ = (μ / σ) / Real.sqrt (1 + (μ / σ) ^ 2) := by
  unfold adamFactor
  have hsq : μ ^ 2 + σ ^ 2 = σ ^ 2 * (1 + (μ / σ) ^ 2) := by
    field_simp [ne_of_gt hσ]; ring
  have h : Real.sqrt (μ ^ 2 + σ ^ 2) = σ * Real.sqrt (1 + (μ / σ) ^ 2) := by
    rw [hsq, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  rw [h, div_div]

/-- Clipped g-SNR factor `min(s,1)` dominates the Adam factor for `s ≥ 0`:
the clipped-SaI step is never smaller than Adam's. -/
theorem adam_le_clipped (s : ℝ) (hs : 0 ≤ s) :
    s / Real.sqrt (1 + s ^ 2) ≤ min s 1 := by
  have hsq : 0 < Real.sqrt (1 + s ^ 2) := by positivity
  have hone : 1 ≤ Real.sqrt (1 + s ^ 2) := (Real.one_le_sqrt (x := 1 + s ^ 2)).2 (by nlinarith [sq_nonneg s])
  have hA : s / Real.sqrt (1 + s ^ 2) ≤ s := by
    rw [div_le_iff₀ hsq]
    nlinarith [mul_nonneg hs (by linarith : 0 ≤ Real.sqrt (1 + s ^ 2))]
  have hB : s / Real.sqrt (1 + s ^ 2) ≤ 1 := (div_le_one hsq).2 (by
    apply (Real.le_sqrt (by positivity) (by positivity)).2; nlinarith)
  exact le_min_iff.2 ⟨hA, hB⟩
/-- Low SNR (`s ≤ 1`): Adam ≥ clipped/√2 — within `√2`. -/
theorem clipped_le_sqrt2_adam (s : ℝ) (hs : 0 ≤ s) (h : s ≤ 1) :
    min s 1 ≤ Real.sqrt 2 * (s / Real.sqrt (1 + s ^ 2)) := by
  have hsq : 0 < Real.sqrt (1 + s ^ 2) := by positivity
  rw [min_eq_left h, ← mul_div_assoc, le_div_iff₀ hsq]
  have h2 : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := by
    apply Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  nlinarith [mul_le_mul_of_nonneg_left h2 hs, mul_nonneg (Real.sqrt_nonneg 2) hs]

/-- High SNR (`s ≥ 1`): the clipped factor `1` is also within `√2` of Adam. -/
theorem clipped_le_sqrt2_adam_high (s : ℝ) (h : 1 ≤ s) :
    min s 1 ≤ Real.sqrt 2 * (s / Real.sqrt (1 + s ^ 2)) := by
  have hsq : 0 < Real.sqrt (1 + s ^ 2) := by positivity
  rw [min_eq_right h, ← mul_div_assoc, le_div_iff₀ hsq]
  have h2 : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 * s := by
    nlinarith [Real.sqrt_nonneg (1 + s ^ 2), Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity),
      Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (by linarith : 0 ≤ s)]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 + s ^ 2), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (1 + s ^ 2))]

open Finset List in
/-- g-SNR-оценка по касаниям: `μ̂ = (1/cnt)∑ g_i`, `σ̂² = (1/cnt)∑ g_i² − μ̂²`
на списке градиентов касаний `gs`. Не зависит от расписания касаний. -/
noncomputable def snrEstimate (gs : List ℝ) : ℝ :=
  let cnt := (gs.length : ℝ)
  let μ := (gs.sum) / cnt
  let σ := Real.sqrt ((gs.map (fun x => x ^ 2)).sum / cnt - μ ^ 2)
  μ / (σ + 1e-8)
/-- Оценка SNR определена только по списку касаний `gs` — число пропущенных
шагов `d` между касаниями в неё не входит (инвариантность по построению).
В отличие от Adam `v`: плотный декей меняет знаменатель. -/
theorem adam_not_invariant (v0 b2 : ℝ) (hv : 0 < v0) (hb0 : 0 < b2) (hb1 : b2 < 1)
    {d : ℕ} (hd : 0 < d) : b2 ^ d * v0 ≠ v0 := by
  intro h
  have hpow : b2 ^ d < 1 := pow_lt_one₀ hb0.le hb1 (Nat.ne_of_gt hd)
  have hlt : b2 ^ d * v0 < 1 * v0 := mul_lt_mul_of_pos_right hpow hv
  rw [one_mul] at hlt
  linarith

end Hagi.Step.AdamSNR
