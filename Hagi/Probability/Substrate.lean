/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Probability.Freedman
import Hagi.Probability.CertifiedEstimator
import Hagi.Probability.PMFBridge

set_option linter.style.header false

/-!
# Substrate — единая PMF-подложка вероятностных словарей (A19.3)

Аудит A19 (N-структура, вероятность/информация): библиотека говорит
на трёх параллельных словарях вероятности. Этот модуль — точка сборки:
манифест каноничности + мосты-тождества. НИ ОДНО доказательство
Freedman-семейства не переписано (KISS-транш).

## Манифест SSOT

* `Hagi.Probability.pmfMean` (FreedmanTwoSided) — канонический
  словарь ожиданий на Mathlib-типе `PMF`; наибольшая потребительская
  база; мосты в меры уже есть (`Hagi.Probability.toPMF`,
  `Hagi.Unified.pmfMean_eq_integral`).
* `prodDens`/`prodE`/`prodPq` (CertifiedEstimator, Freedman-семейство) —
  density-словарь независимого произведения; сохраняется как есть,
  мостится в PMF-подложку теоремой `prodE_eq_pmfMean` ниже.
* `densD`/`expD`/`probD` (FreedmanAdaptive) — зависимое
  обобщение; сохраняется как есть; вкладывается в density-словарь
  теоремами `densD_const`/`expD_const` (постоянные условные веса).

## Каноничность инфо-дублей (A19.3, дубль-таблица)

* `tvHalf_eq_tvDef`: канонический — `Hagi.Information.tvHalf_eq_tvDef`;
  копия `Hagi.Unified.InfoCanonical.tvHalf_eq_tvDef` — deprecated-alias.
* `shannon_le_log_card`: канонический — `Hagi.Unified.shannon_le_log_card`
  (более общий: не требует `Nonempty`); `Hagi.Information.GAD`
  -версия — внутреннее менее общее следствие, оставлена на месте.
* `hoeffding_tail` (Hagi.Ensemble против Hagi.Probability),
  `contraction_limit` (канонический `Hagi.Foundations`, Dynamics-копия
  делегирует), `gibbs_variational` (Hagi.Data и Hagi.Probability),
  `gibbs_free_energy_identity` (Hagi.Probability и Hagi.Energy) —
  РАЗНЫЕ statements в разных namespace, identity-слияние невозможно
  без искажения утверждений; каноничность закреплена этим манифестом.

## Открытый пункт (вне транша)

Полный мост «независимое произведение PMF» (measure-произведение через
bind-цепочку) не построен: текущим потребителям достаточно
`prodE_eq_pmfMean` через суммарную плотность.
-/

open Finset

namespace Hagi.Probability.Substrate

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Мост density → PMF -/

/-- Ожидание под мостом `toPMF` — это взвешенная сумма вещественных
весов (PMF-подложка поглощает density-словарь на одноточечном
пространстве). -/
theorem pmfMean_toPMF (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) (f : V → ℝ) :
    pmfMean (toPMF q hnn hs) f = ∑ a, q a * f a := by
  simp only [pmfMean, Hagi.Probability.toPMF_apply]
  exact Finset.sum_congr rfl fun a _ => by
    rw [ENNReal.toReal_ofReal (hnn a)]

/-- Полная масса плотности независимого произведения равна 1. -/
theorem prodDens_sum {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p) :
    ∑ ω, prodDens p ω = 1 := by
  have h := prodE_one p hp
  simpa [prodE] using h

/-- Развертка `prodE` в сумму (definitional). -/
theorem prodE_eq_sum {n : ℕ} (p : Fin n → V → ℝ)
    (f : (Fin n → V) → ℝ) : prodE p f = ∑ ω, prodDens p ω * f ω := rfl

/-- Ключевой мост A19.3: `prodE`-словарь — частный случай PMF-подложки
`pmfMean`: то же число, что ожидание PMF с плотностью произведения. -/
theorem prodE_eq_pmfMean {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (f : (Fin n → V) → ℝ) :
    prodE p f = pmfMean (toPMF (prodDens p) (prodDens_nonneg hp)
      (prodDens_sum p hp)) f := by
  rw [prodE_eq_sum, pmfMean_toPMF]

/-! ## Мост зависимое → независимое -/

/-- Зависимая плотность с постоянными условными весами — это
независимая плотность произведения (словарь вкладывается
в словарь Freedman-семейства). -/
theorem densD_const (q : ℕ → V → ℝ) : ∀ {n : ℕ} (ω : Fin n → V),
    densD (fun t _ => q t) ω = ∏ i : Fin n, q ↑i (ω i) := by
  intro n
  induction n with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      rw [densD]
      change (densD (fun t _ => q t) fun i => ω i.castSucc)
          * q n (ω (Fin.last n)) = _
      rw [ih (fun i => ω i.castSucc), Fin.prod_univ_castSucc]
      refine congrArg (fun x => x * q (Fin.last n : ℕ) (ω (Fin.last n))) ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Fin.val_castSucc]

/-- Следствие для ожиданий: `expD` на постоянных условных весах —
сумма вида `prodE`. -/
theorem expD_const (q : ℕ → V → ℝ) {n : ℕ} (f : (Fin n → V) → ℝ) :
    expD (fun t _ => q t) f
      = ∑ ω, (∏ i : Fin n, q ↑i (ω i)) * f ω := by
  rw [expD]
  exact Finset.sum_congr rfl fun ω _ => by rw [densD_const]

end Hagi.Probability.Substrate
