/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.NoiseTemperature
import Hagi.Probability.KLSBridge
import Mathlib.Tactic

set_option linter.style.header false

/-!
# ThermoBridge: one 1/B law — two interfaces

The thermodynamic axis of HAGI now has two formalizations of
the SAME noise-cooling law:

* `batch_variance_eq` (NoiseTemperature): the exact identity
  Var(batchMean) = Var(g)/B on the product-probability
  interface (`prodE`/`uniP`) — no hypotheses beyond the
  uniform product system.
* `klsBatchNoise` (KLSBridge): the dimension-free BOUND
  σ² ≤ C·L²·‖a‖²/B on the finite-vector interface
  (`Probability.expQ`) — under the Poincaré interface.

This module welds the interfaces:

* prodDens_uniP: the uniform product density is the
  constant (1/card V)^B.
* `prodE_as_expQ`: `prodE (uniP b)` IS `Probability.expQ` with the
  constant density — the two expectation operators coincide
  on the uniform product system.
* `batchVar_expQ`: `batch_variance_eq` transported verbatim
  into the `expQ` carrier — the SAME law both formalizations
  compute; `uncorrMeanVar` (the klsBatchNoise core) and
  `batch_variance_eq` are one theorem in two vocabularies,
  and the annealing budget σ²·c/(B₀(c−1)) is the same
  quantity both chains bound.
-/

namespace Hagi.Probability

open Finset

variable {V : Type} [Fintype V] [Nonempty V]

/-- **Interface weld**: on the uniform product system the
`prodE` expectation IS `Probability.expQ` with the constant density —
the two vocabularies compute the same number. -/
theorem prodE_as_expQ (b : ℕ) (f : (Fin b → V) → ℝ) :
    prodE (V := V) (uniP b) f
      = Probability.expQ (fun _ => ((Fintype.card V : ℝ) ^ b) ⁻¹) f := by
  unfold prodE Probability.expQ
  rw [Finset.sum_congr rfl (fun ω _ => by rw [uniP_dens])]

/-- **The 1/B law in the expQ carrier**: `batch_variance_eq`
transported verbatim — the SAME theorem the NoiseTemperature
chain computes, now stated in the KLS vocabulary: the
batch-mean temperature is exactly Var(g)/B on the welded
interface. Together with `klsBatchNoise` (the dimension-free
bound) and `uncorrMeanVar` (the general averaging law), the
three formalizations are one law: anneal_by_batch's budget
σ²·c/(B₀(c−1)) is the same quantity all three bound. -/
theorem batchVar_expQ (g : V → ℝ) {b : ℕ} [Nonempty (Fin b)] :
    Probability.expQ (fun _ : Fin b → V => ((Fintype.card V : ℝ) ^ b) ⁻¹)
        (fun ω => (batchMean g ω - popMean g) ^ 2)
      = popVar g / b := by
  exact (prodE_as_expQ b (fun ω => (batchMean g ω - popMean g) ^ 2)).symm.trans
    (batch_variance_eq (V := V) (b := b) g)

end Hagi.Probability

/-!
# WSqD — the full warm-stable-decay noise budget (;
plan §5.4, source 2607.10959 + 1711.00489)

The WSqD scheduler runs THREE phases: warmup, a long
STABLE phase at constant batch B₀, and a DECAY phase with
geometrically growing batch (the "cooldown"). The
literature's full theorem (quality of WSqD ≥ WSD at equal
budget) is empirical-plus-optimizer-theoretic and not
formalizable end-to-end here; what IS formalizable — and
what the recipe actually exploits — is the NOISE BUDGET
accounting of the composition:

* `stable_phase_noise`: a stable phase of n_w steps at
  constant batch B₀ costs EXACTLY σ²·n_w/B₀ — linear in
  the phase length;
* `cooldown_tail_constant`: the ENTIRE decay phase — of ANY
  length — costs at most σ²·c/(B₀(c−1)), the geometric
  bound of `anneal_by_batch`: an unboundedly long
  cooldown is nearly free in noise;
* `wsqd_noise_budget`: the composed budget is the linear
  stable term plus the constant cooldown tail —

    Σ σ²/B_t ≤ σ²·n_w/B₀ + σ²·c/(B₀(c−1))

  — the formal core of the WSqD prescription: the stable
  phase does the work (linear cost per step), the cooldown
  polishes at a fixed total price. Scheduling economics,
  not folklore.
-/

open scoped BigOperators

namespace Hagi.Probability

/-- The stable phase contributes its per-step noise
linearly: n_w steps at constant batch B₀ cost exactly
σ²·n_w/B₀. -/
theorem stable_phase_noise {sigma : ℝ} (B0 : ℝ)
    (n_w : ℕ) (hB0 : B0 ≠ 0) :
    ∑ t ∈ Finset.range n_w, sigma ^ 2 / B0
      = sigma ^ 2 * n_w / B0 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **The cooldown tail is CONSTANT**: the entire decay
phase — of ANY length — contributes at most the geometric
bound σ²·c/(B₀(c−1)) (`anneal_by_batch`,). An
unboundedly long cooldown is nearly free in noise. -/
theorem cooldown_tail_constant {sigma : ℝ}
    (B : ℕ → ℝ) (n_d : ℕ) (hsigma : 0 ≤ sigma)
    (hc1 : 1 < c) (hB0 : 0 < B 0)
    (hgrow : ∀ t < n_d, B (t + 1) = c * B t) :
    ∑ t ∈ Finset.range n_d, sigma ^ 2 / B t
      ≤ sigma ^ 2 * c / (B 0 * (c - 1)) :=
  anneal_by_batch B n_d hsigma hc1 hB0 hgrow

/-- **The composed WSqD noise budget**: stable phase of
n_w steps at B₀ followed by a decay phase of n_d steps
with growth c obeys the additive budget

  Σ σ²/B_t ≤ σ²·n_w/B₀ + σ²·c/(B₀(c−1))

— the linear stable term plus the CONSTANT cooldown tail:
the stable phase does the work (each step costs σ²/B₀),
the cooldown polishes at a fixed total price however long
it runs. -/
theorem wsqd_noise_budget {sigma : ℝ} (B0 : ℝ)
    (Bd : ℕ → ℝ) (n_w n_d : ℕ) (hsigma : 0 ≤ sigma)
    (hB0 : 0 < B0) (hBd0 : Bd 0 = B0) (hc1 : 1 < c)
    (hgrow : ∀ t < n_d, Bd (t + 1) = c * Bd t) :
    (∑ t ∈ Finset.range n_w, sigma ^ 2 / B0)
        + ∑ t ∈ Finset.range n_d, sigma ^ 2 / Bd t
      ≤ sigma ^ 2 * n_w / B0 + sigma ^ 2 * c / (B0 * (c - 1)) := by
  have h1 := stable_phase_noise (sigma := sigma) B0 n_w hB0.ne'
  have h2 := cooldown_tail_constant Bd n_d hsigma hc1
    (by rw [hBd0]; exact hB0) hgrow
  rw [hBd0] at h2
  rw [h1]
  exact add_le_add (le_refl _) h2

end Hagi.Probability

/-!
# BatchSNR (источник №76: McCandlish et al., "An Empirical
# Model of Large-Batch Training", arXiv 1812.06162)

Gradient noise scale: сигнал/шум батч-градиента растёт
ЛИНЕЙНО по размеру батча (следствие temperature law
Var(ĝ) = Var(g)/B из NoiseTemperature); критический
батч B* = σ²/μ² — порог, выше которого сигнал
превышает шум.
-/

namespace Hagi.Probability.BatchSNR

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Детерминированный SNR батч-градиента размера B:
μ²·B/σ² (σ² = popVar, μ = popMean). -/
noncomputable def snr (g : V → ℝ) (B : ℕ) : ℝ :=
  (popMean g)^2 * B / popVar g

/-- РЕАЛИЗОВАННЫЙ SNR: по temperature law (batch_variance_eq)
E[(ĝ−μ)²] = σ²/B, поэтому snr g B = μ²/E[(ĝ−μ)²] —
определение совпадает с фактическим отношением
сигнал/шум батч-градиента. -/
theorem snr_realized (g : V → ℝ) {b : ℕ} [Nonempty (Fin b)] :
    snr g b = (popMean g)^2
      / prodE (uniP b) (fun ω => (batchMean g ω - popMean g) ^ 2) := by
  have hv := batch_variance_eq (V := V) (b := b) g
  unfold snr
  rw [hv]
  field_simp

/-- ЛИНЕЙНОСТЬ ПО БАТЧУ: SNR(B) = B · SNR(1) — удвоение
батча удваивает отношение сигнал/шум (закон убывания
шума 1/B). -/
theorem snr_linear (g : V → ℝ) (B : ℕ) :
    snr g B = B * snr g 1 := by
  unfold snr
  field_simp
  ring

/-- КРИТИЧЕСКИЙ БАТЧ: B* = σ²/μ² (при μ ≠ 0, σ² > 0) —
минимальный вещественный размер батча с SNR = 1. -/
noncomputable def criticalBatch (g : V → ℝ) : ℝ :=
  popVar g / (popMean g)^2

/-- ПОРОГОВЫЙ ЗАКОН: SNR(B) ≥ 1 ⟺ B ≥ B* — выше
критического батча сигнал доминирует над шумом. -/
theorem snr_ge_one_iff (g : V → ℝ)
    (hμ : popMean g ≠ 0) (hσ : 0 < popVar g) (B : ℕ) :
    snr g B ≥ 1 ↔ criticalBatch g ≤ B := by
  have hμ2 : 0 < (popMean g)^2 := sq_pos_iff.mpr hμ
  unfold snr criticalBatch
  rw [ge_iff_le, le_div_iff₀ hσ, div_le_iff₀ hμ2]
  constructor <;> intro h <;> linarith

/-- Модель критического батча (источник №76, §4):
прогресс шага ∝ min(1, B/B*) — ниже B* прогресс
линейный по B, выше — насыщается (шум подавлен). -/
noncomputable def batchGain (Bstar : ℝ) (B : ℝ) : ℝ :=
  min 1 (B / Bstar)

/-- Стоимость шага: фиксированная β + линейная α·B
(параллелизм идеален до α). -/
noncomputable def stepCost (alpha beta B : ℝ) : ℝ :=
  alpha * B + beta

/-- Прогресс на единицу стоимости. -/
noncomputable def gainPerCost (Bstar alpha beta B : ℝ) : ℝ :=
  batchGain Bstar B / stepCost alpha beta B

/-- ЗАКОН УБЫВАНИЯ ЭФФЕКТИВНОСТИ: при B₂ > B₁ ≥ B*
прогресс на единицу стоимости СТРОГО убывает — за
критическим батчем каждый доп. образец покупает всё
меньше прогресса за вычисления (оптимум в B*). -/
theorem gain_decreasing_past_critical
    (Bstar alpha beta B1 B2 : ℝ)
    (hstar : 0 < Bstar) (hbeta : 0 < beta) (halpha : 0 < alpha)
    (h1 : Bstar ≤ B1) (h2 : B1 < B2) :
    gainPerCost Bstar alpha beta B2
      < gainPerCost Bstar alpha beta B1 := by
  have hmin1 : batchGain Bstar B1 = 1 :=
    min_eq_left ((le_div_iff₀ hstar).mpr (by linarith))
  have hmin2 : batchGain Bstar B2 = 1 :=
    min_eq_left ((le_div_iff₀ hstar).mpr (by linarith))
  unfold gainPerCost stepCost
  rw [hmin1, hmin2]
  have hB1pos : (0:ℝ) < B1 := lt_of_lt_of_le hstar h1
  have hc : (0:ℝ) < alpha * B1 + beta := by
    have hnn : 0 ≤ alpha * B1 :=
      mul_nonneg (le_of_lt halpha) (le_of_lt hB1pos)
    linarith
  have hc2 : (0:ℝ) < alpha * B2 + beta := by
    have hB2pos : (0:ℝ) < B2 := lt_of_lt_of_le hstar
      (le_trans h1 (le_of_lt h2))
    have hnn2 : 0 ≤ alpha * B2 :=
      mul_nonneg (le_of_lt halpha) (le_of_lt hB2pos)
    linarith
  rw [one_div_lt_one_div hc2 hc]
  have hBpos : (0:ℝ) < B2 - B1 := sub_pos.mpr h2
  have hmul : 0 < alpha * (B2 - B1) :=
    mul_pos halpha hBpos
  nlinarith [hmul]

end Hagi.Probability.BatchSNR

set_option linter.style.header false

/-!
# ThermoAxes — эквивалентность осей охлаждения: LR-decay ⟺
batch-increase

Формализация ядра «Don't Decay the Learning Rate, Increase
the Batch Size» (arXiv:1711.00489, Smith et al.; план §2,
терм-ось): убывание LR и рост batch — ОДНА математика на
двух осях. Шумовой бюджет шага пропорционален σ²η² (LR-ось)
или σ²/B (batch-ось); при перекрёстном соответствии

  η₀ = 1/√B₀,  r = 1/√c  (⟺ r²·c = 1)

последовательности шумовых вкладов СОВПАДАЮТ ПОЧЛЕННО, а
значит равны и полные бюджеты охлаждения.

Доказано:
* `noise_axes_coincide`: при r²·c = 1 и η₀²·B₀ = 1/B₀
  вклады η₀²·r^{2t} и 1/(B₀·c^t) равны для каждого t —
  оси — одна и та же последовательность;
* `noise_budget_axes_equal`: конечные суммы шумовых бюджетов
  равны (обе оси покупают одно и то же охлаждение);
* интерпретация: выбор оси — экономика (batch растёт —
  дороже шаг, дешевле конвергенция траектории), не
  математика.

Дополнение к anneal_by_batch: batch-ось покупает то же
охлаждение БЕЗ сжатия шага.
-/

open Finset Real

namespace Hagi.Probability

/-- Почленное совпадение осей: при r²·c = 1 и η₀²·B₀ = 1/B₀
шумовой вклад LR-оси η₀²·r^{2t} равен вкладу batch-оси
1/(B₀·c^t) для каждого шага t. -/
theorem noise_axes_coincide (eta0 r B0 c : ℝ) (t : ℕ)
    (hr2c : r ^ 2 * c = 1) (heta : eta0 ^ 2 * B0 = 1)
    (hB0 : B0 ≠ 0) :
    eta0 ^ 2 * r ^ (2 * t) = 1 / (B0 * c ^ t) := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr2c
    exact absurd hr2c (by simp)
  have hrpow : r ^ (2 * t) = 1 / c ^ t := by
    have h1 : (r ^ 2) ^ t * c ^ t = 1 := by
      calc (r ^ 2) ^ t * c ^ t = (r ^ 2 * c) ^ t := by rw [mul_pow]
        _ = 1 ^ t := by rw [hr2c]
        _ = 1 := one_pow _
    rw [pow_mul]
    exact (eq_div_iff (pow_ne_zero t hc)).mpr h1
  have heta2 : eta0 ^ 2 = 1 / B0 := by
    rw [eq_div_iff hB0] at *
    linarith
  rw [hrpow, heta2]
  field_simp

/-- Равенство полных шумовых бюджетов: сумма вкладов LR-оси
(η₀²r^{2t}) равна сумме вкладов batch-оси (1/(B₀c^t)) на
любом горизонте — оси охлаждения математически
эквивалентны. -/
theorem noise_budget_axes_equal (eta0 r B0 c : ℝ) (n : ℕ)
    (hr2c : r ^ 2 * c = 1) (heta : eta0 ^ 2 * B0 = 1)
    (hB0 : B0 ≠ 0) :
    ∑ t ∈ Finset.range n, eta0 ^ 2 * r ^ (2 * t)
      = ∑ t ∈ Finset.range n, 1 / (B0 * c ^ t) := by
  exact Finset.sum_congr rfl fun t _ =>
    noise_axes_coincide eta0 r B0 c t hr2c heta hB0

end Hagi.Probability
