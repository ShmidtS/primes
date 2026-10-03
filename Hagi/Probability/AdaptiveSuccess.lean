/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
set_option linter.style.header false

/-!
# P0-4: AdaptiveSuccess — условные success-полы вместо i.i.d.

Аудит R121 (§7): R95 концентрирует ЧИСЛО успехов при
НЕЗАВИСИМЫХ одинаково распределённых S_t. В реальном
self-improvement loop успехи не i.i.d.:

S_{t+1} ~ P(· | F_t)

— успешность следующего эксперта зависит от того, что система
уже узнала. Нужна форма с УСЛОВНЫМИ полами.

**Формализация**: на конечном произведении циклов (R114)
зависимость от истории моделируется тем, что итог цикла t
является функцией ТОЛЬКО свежей случайности ω_t (каждый цикл
использует свой независимый источник: новые данные/инициализация/
minibatch). Тогда условное распределение S_t при любой истории —
маргинальное по ω_t, и per-cycle success-пол

  E[S_t | F_t] = E[S_t] ≥ p₀

воплощается как маргинальное неравенство
`coordMean p X t ≥ p₀` (координатное среднее — измеряемая
величина, сертифицируемая R114). Ключевая разница с R95:
распределения РАЗНЫЕ по циклам (не i.i.d.), только полы общие.

**Теоремы:**

* `adaptive_success_count_floor` — при per-cycle полах
  `∀ t, p₀ ≤ coordMean p X t`: число успехов ≥ n·p₀ − t с
  вероятностью ≥ 1 − exp(−2t²/n) (Hoeffding-хвост для
  независимых НЕодинаковых [0,1]-переменных; доказательство —
  `hoeffding_mean_tail_low` R114 + сдвиг на Σp₀).
* `adaptive_success_concentrated` — явная форма с
  t = √(n·log(1/δ)/2): P[ΣS ≥ n·p₀ − √(n log(1/δ)/2)] ≥ 1−δ.

**Честная граница**: настоящая мартингальная зависимость
(S_t — функция всей истории, не только ω_t) требует
Азумы/Фридмана с фильтрацией — открыто; здесь сведено к
fresh-randomness-per-cycle, стандартному трюку рандомизированных
алгоритмов. При детерминированной адаптации (без свежей
случайности) полы должны проверяться напрямую (runtime).
-/

open Finset Real

namespace Hagi

variable {V : Type} [Fintype V] [Nonempty V]

/-- **Адаптивный success-floor**: per-cycle условное среднее
(координатное маргинальное) ≥ p₀ — измеряемый и
сертифицируемый (R114) пол. -/
def SuccessFloor {n : ℕ} (p : Fin n → V → ℝ) (X : Fin n → V → ℝ)
    (p0 : ℝ) : Prop :=
  ∀ t, p0 ≤ coordMean p X t

/-- **Число успехов при условных полах**: если каждый цикл
использует свежую случайность ω_t (итог — функция только ω_t)
и маргинальный пол успеха ≥ p₀, то суммарный успех ≥ n·p₀ − t
с вероятностью ≥ 1 − exp(−2t²/n). Отличие от R95: циклы
РАЗНОРАСПРЕДЕЛЕНЫ (адаптивная система), одинаковы только
полы. -/
theorem adaptive_success_count_floor {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (p0 : ℝ) (hfloor : SuccessFloor p X p0)
    (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    1 - Real.exp (- 2 * t ^ 2 / (n : ℝ))
      ≤ prodPq p (fun ω => n * p0 - t ≤ ∑ i, X i (ω i)) := by
  classical
  -- Σ S ≥ Σ E[S] + centeredSum ≥ n·p₀ + centeredSum
  have hsumfloor : ∀ ω : Fin n → V,
      n * p0 + centeredSum p X ω ≤ ∑ i, X i (ω i) := by
    intro ω
    have hexp : (∑ i, coordMean p X i) + centeredSum p X ω
        = ∑ i, X i (ω i) := by
      unfold centeredSum
      ring
    have hfloorsum : n * p0 ≤ ∑ i, coordMean p X i := by
      have hpt : ∀ i : Fin n, p0 ≤ coordMean p X i := hfloor
      have hsumeq : n * p0 = ∑ i : Fin n, p0 := by
        rw [Finset.sum_const]
        simp [Finset.card_univ, Fintype.card_fin]
      rw [hsumeq]
      exact Finset.sum_le_sum fun i _ => hpt i
    linarith
  -- нижний хвост (R114): P(centeredSum ≤ −t) ≤ e^{−2t²/n}
  have hlow := hoeffding_mean_tail_low p hp X hX hn (t / (n : ℝ))
    (by positivity)
  have hexp_eq : Real.exp (- 2 * (n : ℝ) * (t / (n : ℝ)) ^ 2)
      = Real.exp (- 2 * t ^ 2 / (n : ℝ)) := by
    congr 1
    field_simp
    try ring
  have harg : - (n : ℝ) * (t / (n : ℝ)) = - t := by
    field_simp
  rw [harg] at hlow
  rw [hexp_eq] at hlow
  -- дополнение хвоста вкладывается в целевое событие
  have hmono : prodPq p (fun ω => ¬(centeredSum p X ω ≤ - t))
      ≤ prodPq p (fun ω => n * p0 - t ≤ ∑ i, X i (ω i)) :=
    prodPq_mono p hp _ _ (fun ω hω =>
      by have hsum := hsumfloor ω
         by_contra hcon
         push_neg at hcon
         have : centeredSum p X ω ≤ - t := by linarith
         exact hω this)
  have hcompl := prodPq_compl p hp
    (fun ω => centeredSum p X ω ≤ - t)
  rw [hcompl] at hmono
  linarith

/-- **Концентрированная форма**: с t = √(n·log(1/δ)/2)
число успехов ≥ n·p₀ − √(n·log(1/δ)/2) с вероятностью ≥ 1−δ. -/
theorem adaptive_success_concentrated {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (p0 : ℝ) (hfloor : SuccessFloor p X p0)
    (hn : 0 < n) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    1 - delta
      ≤ prodPq p (fun ω => n * p0
        - Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)
        ≤ ∑ i, X i (ω i)) := by
  have hone : 1 < 1 / delta := by
    field_simp
    linarith
  have hlog : 0 < Real.log (1 / delta) := Real.log_pos hone
  have ht : 0 < Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hmain := adaptive_success_count_floor p hp X hX p0 hfloor hn _ ht
  -- exp(−2t²/n) = delta при t = sqrt(n log(1/δ)/2)
  have hexpe : Real.exp (- 2 * (Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)) ^ 2
      / (n : ℝ)) = delta := by
    have hsq : (Real.sqrt ((n : ℝ) * Real.log (1 / delta) / 2)) ^ 2
        = (n : ℝ) * Real.log (1 / delta) / 2 :=
      Real.sq_sqrt (by positivity)
    have hdive : - 2 * ((n : ℝ) * Real.log (1 / delta) / 2) / (n : ℝ)
        = - Real.log (1 / delta) := by
      field_simp
      try ring
    rw [hsq, hdive, Real.exp_neg, Real.exp_log (one_div_pos.mpr hdelta)]
    field_simp
  rw [hexpe] at hmain
  exact hmain

end Hagi
