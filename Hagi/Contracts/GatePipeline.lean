/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
import Hagi.Unified.StitchingEProcess
set_option linter.style.header false

/-!
# Gate pipeline (C264, addendum A10 priority P1)

Формализация гейта, КАК его использует Python-код (audit A10 §3):
пошаговый пайплайн «измерение → доверительная граница → бюджет →
решение», собранный в ОДНУ теорему с итогом
«P(любой ложный commit) ≤ δ».

**Состав (каждому шагу кода — свой артефакт):**

* диапазонное шкалирование `[−1,1] → [0,1]`:
  `hoeffding_pm1_two_sided` — переменная Y = (X+1)/2, событие в
  [−1,1]-единицах с допуском η совпадает с событием в [0,1]-единицах
  с допуском η/2, поэтому экспонента Hoeffding `2e^{−2nε²}`
  переходит в `2e^{−2n(η/2)²} = 2e^{−nη²/2}` — радиус удваивается;
* δ-расписание: `gate_delta_schedule_sum_le` — для конечного числа
  последовательных проверок (K ≤ шести) частичная сумма
  Σ 6/(π²k²) ≤ 1 (честная конечная-K форма: тождество Базеля
  Σ 1/k² = π²/2·3 в пиннованном Mathlib отсутствует — поиск
  выполнен; доказательство через S₆ = 5369/3600, монотонность по K
  и π > 3);
* union-композиция: `gate_pipeline_false_commit` — при
  индивидуальных бюджетах β k с Σ β k ≤ δ вероятность того, что НЕ
  произойдёт ни одного ложного commit, ≥ 1 − δ (union bound по
  конечному множеству проверок);
* аллокация по этажам: `gate_pipeline_budget` — бюджет проверки k
  равен δ·6/(π²(k+1)²)/(1+m): (1+m) этажных событий на проверку,
  суммарный расход ≤ δ·Σ 6/(π²(k+1)²) ≤ δ (множитель (1+m)
  сокращается — никакого скрытого фактора);
* anytime-мост: `gate_anytime_valid` — Ville-овская равномерная по
  времени граница (C232 `stitching_eprocess_anytime`): если каждое
  событие ложного commit вложено в {δ⁻¹ ≤ M_t} со сшитым мастером
  M_t, то μ.real{∃ t ≤ n, ложный commit} ≤ δ ОДНОВРЕМЕННО для всех
  n — замена фиксированного-n объединения; ПРОДАКШН-РЕКОМЕНДАЦИЯ:
  эмпирическая дисперсия Freedman (C248
  `freedman_exp_empirical_le_fixed`, `stitching_alarm_superset`):
  при кумулятивной предсказуемой дисперсии в бюджете c² эмпирический
  показатель не хуже фиксированного — адаптивный n вместо
  фиксированного (измеренные эффекты остаются в документации, не в
  посылках);
* негативный свидетель: `gate_fixed_radius_unusable` — при
  параметрах аудита (пятьсот двенадцать образцов, δ = 1/20, десятая
  проверка, восемь этажей) любой [−1,1]-радиус r с гарантией
  2e^{−256·r²} ≤ бюджету удовлетворяет r > 0.14 > 1/20 —
  фиксированный-n гейт не может сертифицировать допуск 1/20
  (качественное совпадение с найденной аудитом непригодностью
  радиуса на пятистах двенадцати образцах).

**Честные посылки**: свежесть потока измерений — это `IsProbSys p`
(координатные распределения = распределения измерений; independence
в mgf-форме уже внутри `prodE_exp_sum`); вложение anytime-события —
явная посылка `hF` в `gate_anytime_valid`. Модуль сертифицирует
СТАТИСТИЧЕСКУЮ часть; репрезентативность остаётся на стороне
измерения.
-/

open Finset Real MeasureTheory ProbabilityTheory

namespace Hagi.Contracts.GatePipeline

/-! ## Диапазонное шкалирование [−1,1] → [0,1] -/

variable {V : Type} [Fintype V] [Nonempty V]

omit [Nonempty V] in
private theorem gateRescaleHalf {n : ℕ} (p : Fin n → V → ℝ)
    (hp : Hagi.Probability.IsProbSys p) (X : Fin n → V → ℝ) (ω : Fin n → V) :
    Hagi.Probability.centeredSum p (fun i v => (X i v + 1) / 2) ω
      = Hagi.Probability.centeredSum p X ω / 2 := by
  unfold Hagi.Probability.centeredSum Hagi.Probability.coordMean
  have hA : ∀ i : Fin n, ∑ v, p i v * ((X i v + 1) / 2)
      = ((∑ v, p i v * X i v) + 1) / 2 := by
    intro i
    have h1 : ∑ v, p i v = 1 := (hp i).2
    have hstep : ∀ v : V, p i v * ((X i v + 1) / 2) = (p i v * X i v) / 2 + p i v / 2 :=
      fun v => by ring
    rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_div]
    rw [h1]; ring
  simp only [hA]
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i : Fin n, ((X i (ω i) + 1) / 2) - ((∑ v, p i v * X i v) + 1)/2
      = (X i (ω i) - ∑ v, p i v * X i v)/2 := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.sum_div, Finset.sum_sub_distrib]

/-- Двусторонняя Hoeffding-граница в [−1,1]-единицах: для значений в
[−1,1] с допуском η вероятность |ΣX − Σμ| ≥ nη не превосходит
2e^{−nη²/2}. Это `hoeffding_two_sided` для Y = (X+1)/2 ∈ [0,1] при
ε = η/2: экспонента 2n(η/2)² = nη²/2 — РАДИУС УДВАИВАЕТСЯ относительно
[0,1]-шкалы (шаг Python-гейта: rescale [−1,1] → [0,1]). -/
theorem hoeffding_pm1_two_sided {n : ℕ} (p : Fin n → V → ℝ)
    (hp : Hagi.Probability.IsProbSys p) (X : Fin n → V → ℝ)
    (hX : ∀ i v, -1 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eta : ℝ) (heta : 0 < eta) :
    Hagi.Probability.prodPq p (fun ω =>
      (n : ℝ) * eta ≤ Hagi.Probability.centeredSum p X ω
        ∨ Hagi.Probability.centeredSum p X ω ≤ - (n : ℝ) * eta)
      ≤ 2 * Real.exp (- (n : ℝ) * eta ^ 2 / 2) := by
  classical
  set Y : Fin n → V → ℝ := fun i v => (X i v + 1) / 2 with hYdef
  have hYb : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1 := by
    intro i v
    have hx := hX i v
    show (0:ℝ) ≤ (X i v + 1)/2 ∧ (X i v + 1)/2 ≤ 1
    constructor <;> linarith [hx.1, hx.2]
  have hrw := gateRescaleHalf p hp X
  have hcongr : Hagi.Probability.prodPq p (fun ω =>
      (n : ℝ) * eta ≤ Hagi.Probability.centeredSum p X ω
        ∨ Hagi.Probability.centeredSum p X ω ≤ - (n : ℝ) * eta)
      = Hagi.Probability.prodPq p (fun ω =>
      (n : ℝ) * (eta / 2) ≤ Hagi.Probability.centeredSum p Y ω
        ∨ Hagi.Probability.centeredSum p Y ω ≤ - (n : ℝ) * (eta / 2)) := by
    refine Hagi.Probability.prodPq_iff p _ _ (fun ω => ?_)
    have h2 := hrw ω
    constructor
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  rw [hcongr]
  have hbase := Hagi.Probability.hoeffding_two_sided p hp Y hYb hn (eta / 2)
    (by linarith)
  have hexp : (2:ℝ) * Real.exp (- 2 * (n : ℝ) * (eta / 2) ^ 2)
      = 2 * Real.exp (- (n : ℝ) * eta ^ 2 / 2) := by
    have hsq : (eta / 2) ^ 2 = eta ^ 2 / 4 := by ring
    rw [hsq]
    congr 2
    field_simp
    ring
  rw [hexp] at hbase
  exact hbase

/-! ## δ-расписание -/

/-- Конечная частичная сумма δ-расписания Python-гейта: для K ≤ шести
последовательных проверок Σ_{k<K} 6/(π²(k+1)²) ≤ 1. Тождество Базеля
в пиннованном Mathlib отсутствует (поиск выполнен); честная конечная
форма: S₆ = 5369/3600, монотонность по K, 6/π² ≤ 2/3 (π > 3),
(2/3)·(5369/3600) ≤ 1. -/
theorem gate_delta_schedule_sum_le (K : ℕ) (hK : K ≤ 6) :
    ∑ k ∈ range K, 6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2) ≤ 1 := by
  have hS6 : ∑ k ∈ range 6, 1 / ((k:ℝ) + 1) ^ 2 = 5369/3600 := by norm_num
  have hcplt : (0:ℝ) ≤ ∑ k ∈ range (6 - K), 1 / (((K + k : ℕ):ℝ) + 1) ^ 2 := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hmonoK : ∑ k ∈ range K, 1 / ((k:ℝ) + 1) ^ 2
      ≤ ∑ k ∈ range 6, 1 / ((k:ℝ) + 1) ^ 2 := by
    rw [show (6:ℕ) = K + (6 - K) from by omega, Finset.sum_range_add]
    linarith [hcplt]
  have hmono : ∑ k ∈ range K, 1 / ((k:ℝ) + 1) ^ 2 ≤ 5369/3600 :=
    le_trans hmonoK hS6.le
  have hconv : ∑ k ∈ range K, 6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2)
      = (6 / Real.pi ^ 2) * ∑ k ∈ range K, 1 / ((k:ℝ) + 1) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← div_div]; ring
  have hpile : 6 / Real.pi ^ 2 ≤ 2/3 := by
    have h9 : (9:ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    field_simp
    nlinarith
  rw [hconv]
  have h53 : (5369:ℝ)/3600 ≤ 3/2 := by norm_num
  calc (6 / Real.pi ^ 2) * ∑ k ∈ range K, 1 / ((k:ℝ) + 1) ^ 2
      ≤ (2/3) * (5369/3600) := mul_le_mul hpile hmono (by positivity) (by positivity)
    _ ≤ 1 := by nlinarith [h53]

/-! ## Композиция: P(любого ложного commit) ≤ δ -/

/-- ГЛАВНАЯ композиция гейт-пайплайна (фиксированный n): если каждая
проверка k имеет событие ложного commit `Bad k` с вероятностью ≤ β k
(форма Hoeffding: `hoeffding_pm1_two_sided` / CertifiedEstimator
`e^{−2nε²}`), и суммарный бюджет Σ β k ≤ δ, то вероятность того, что
НЕ случится ни одного ложного commit, ≥ 1 − δ. Посылка свежести
потока — `IsProbSys p` (независимость координат внутри
`prodE_exp_sum`). Доказательство повторяет схему
`premises_union_confidence` (CertifiedEstimator) с неравными
пер-проверочными бюджетами β k. -/
theorem gate_pipeline_false_commit {n : ℕ} (p : Fin n → V → ℝ)
    (hp : Hagi.Probability.IsProbSys p) {K : Type} [Fintype K]
    (Bad : K → (Fin n → V) → Prop) [∀ k, DecidablePred (Bad k)]
    (β : K → ℝ)
    [DecidablePred (fun ω => ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω)]
    (htail : ∀ k, Hagi.Probability.prodPq p (Bad k) ≤ β k)
    (hsum : ∑ k, β k ≤ δ) :
    1 - δ ≤ Hagi.Probability.prodPq p
      (fun ω => ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω) := by
  classical
  have hfail : Hagi.Probability.prodPq p
      (fun ω => ¬ ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω)
        ≤ ∑ k ∈ (Finset.univ : Finset K), β k := by
    have hsplit2 := Hagi.Probability.prodPq_iff p
      (fun ω => ¬ ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω)
      (fun ω => ∃ k ∈ (Finset.univ : Finset K), Bad k ω)
      (fun ω => by
        constructor
        · intro h
          by_contra hc
          refine h (fun k hk => ?_)
          by_contra hai
          exact hc ⟨k, hk, hai⟩
        · rintro ⟨k, hk1, hk2⟩ hall
          exact absurd hk2 (hall k hk1))
    rw [hsplit2]
    have hu := Hagi.Probability.prodPq_union_finset p hp
      (Finset.univ : Finset K) Bad
    have hle : ∑ k ∈ (Finset.univ : Finset K), Hagi.Probability.prodPq p (Bad k)
        ≤ ∑ k ∈ (Finset.univ : Finset K), β k :=
      Finset.sum_le_sum fun k _ => htail k
    exact le_trans hu hle
  have hsplit3 := Hagi.Probability.prodPq_compl p hp
    (fun ω => ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω)
  have hfinal : Hagi.Probability.prodPq p
      (fun ω => ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω)
      = 1 - Hagi.Probability.prodPq p
          (fun ω => ¬ ∀ k ∈ (Finset.univ : Finset K), ¬ Bad k ω) :=
    by linear_combination hsplit3
  rw [hfinal]
  linarith

/-- Аллокация бюджета Python-гейта: проверка k получает
α_k/(1+m), где α_k = δ·6/(π²(k+1)²); (1+m) этажных событий на
проверку, суммарный расход по всем проверкам и этажам ≤ δ
(множитель (1+m) сокращается точно; применимо при K ≤ шести
последовательных проверках; δ ≥ 0 — бюджет). -/
theorem gate_pipeline_budget (δ : ℝ) (hδ : 0 ≤ δ) (m : ℕ) (K : ℕ)
    (hK : K ≤ 6) :
    ∑ k ∈ range K, ((m : ℝ) + 1) * (δ * 6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2)
      / ((m : ℝ) + 1)) ≤ δ := by
  have hm1 : ((m:ℝ) + 1) ≠ 0 := by
    have hmn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
    linarith
  have hterm : ∀ k ∈ range K, ((m:ℝ) + 1) * (δ * 6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2)
        / ((m:ℝ) + 1)) = δ * (6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2)) := by
    intro k _
    field_simp
  rw [Finset.sum_congr rfl (fun k hk => hterm k hk), ← Finset.mul_sum]
  calc δ * ∑ k ∈ range K, 6 / (Real.pi ^ 2 * ((k:ℝ) + 1) ^ 2)
      ≤ δ * 1 :=
        mul_le_mul_of_nonneg_left (gate_delta_schedule_sum_le K hK) hδ
    _ = δ := by ring

/-- ANYTIME-МОСТ: Ville-овская равномерная по времени граница
заменяет фиксированное-n объединение пайплайна. Если каждое событие
ложного commit `F t` вложено в пересечение порога δ⁻¹ сшитым
мастером `stitchedMaster w E t` (C232), то для КАЖДОГО горизонта n
ОДНОВРЕМЕННО μ.real{∃ t ≤ n, ложный commit} ≤ δ. Это прямое следствие
`Hagi.Unified.stitching_eprocess_anytime` (новой вероятностной
неравенственности не утверждается); вклад моста — форма посылки
вложения (то, что гейт обязан построить в рантайме) и ∀-n
одновременность вместо union по горизонтам. ПРОДАКШЕН: адаптивный n
с эмпирической дисперсией Freedman (C248
`freedman_exp_empirical_le_fixed`,
`Hagi.Unified.stitching_alarm_superset`) — эмпирический показатель не
хуже фиксированного при дисперсии в бюджете c². -/
theorem gate_anytime_valid {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    {k : Type} [Fintype k] [DecidableEq k] [Nonempty k]
    (w : k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i ≤ 1) (E : k → ℕ → Ω → ℝ)
    (hE : ∀ i, Supermartingale (E i) 𝒢 μ) (hEnn : ∀ i, 0 ≤ E i)
    (hE0 : ∀ i, μ[E i 0] ≤ 1) {delta : ℝ} (hdelta : 0 < delta)
    (n : ℕ) (F : ℕ → Ω → Prop)
    (hF : ∀ t ∈ Finset.range (n + 1),
      ∀ ω, F t ω → delta⁻¹ ≤ Hagi.Unified.stitchedMaster w E t ω) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), F t ω} ≤ delta := by
  have hmain := Hagi.Unified.stitching_eprocess_anytime w hw hwsum E hE hEnn hE0
    hdelta n
  refine le_trans ?_ hmain
  refine measureReal_mono ?_ (by finiteness)
  rintro ω ⟨t, ht, hFt⟩
  show ∃ t ∈ Finset.range (n + 1), delta⁻¹ ≤ Hagi.Unified.stitchedMaster w E t ω
  exact ⟨t, ht, hF t ht ω hFt⟩

/-! ## Негативный свидетель: фиксированный n непригоден -/

/-- НЕГАТИВНЫЙ СВИДЕТЕЛЬ непригодности фиксированного-n гейта при
параметрах аудита: n = пятьсот двенадцать образцов, δ = 1/20,
десятая последовательная проверка (k с (k+1)² = сотне), m = восемь
этажей. Бюджет события β = δ·6/(π²·10²)/9 ≤ 1/27000 (через 6/π² ≤
2/3 и π > 3); гарантия пер-события в [−1,1]-единицах есть
2e^{−256·r²}. ЛЮБОЙ радиус r ≥ 0 с такой гарантией удовлетворяет
r > 0.14 > 1/20 = tol: фиксированный-n гейт НЕ МОЖЕТ сертифицировать
допуск 1/20 (качественное совпадение с радиусом, найденным аудитом
непригодным на пятистах двенадцати образцах; решение — anytime-мост
`gate_anytime_valid` с адаптивным n). -/
theorem gate_fixed_radius_unusable (r : ℝ) (hr0 : 0 ≤ r)
    (hr : 2 * Real.exp (-256 * r ^ 2) ≤ 1/27000) : 0.14 < r := by
  by_contra hc
  have hle : r ≤ 0.14 := le_of_not_gt hc
  have hexp6 : Real.exp (6:ℝ) < 729 := by
    have h1 : Real.exp (6:ℝ) = (Real.exp 1) ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h6 : (Real.exp 1) ^ 6 < (3:ℝ) ^ 6 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
    rw [h1]
    have h729 : (3:ℝ)^6 = 729 := by norm_num
    rw [h729] at h6
    exact h6
  have hlow : Real.exp (-(6:ℝ)) ≤ Real.exp (-256 * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h014 : (0.14:ℝ) ^ 2 = 0.0196 := by norm_num
    nlinarith [hle, hr0, mul_nonneg (sub_nonneg.mpr hle) hr0, h014,
      sq_nonneg (0.14 - r)]
  have h729inv : (1:ℝ)/729 < Real.exp (-(6:ℝ)) := by
    have h1 := (one_div_lt_one_div (by norm_num : (0:ℝ) < 729)
      (Real.exp_pos 6)).mpr hexp6
    rw [Real.exp_neg (6:ℝ), inv_eq_one_div (Real.exp (6:ℝ))]
    linarith
  have hlower : (2:ℝ)/729 ≤ 2 * Real.exp (-256 * r ^ 2) := by
    calc (2:ℝ)/729 = 2 * ((1:ℝ)/729) := by ring
      _ ≤ 2 * Real.exp (-(6:ℝ)) :=
          mul_le_mul_of_nonneg_left h729inv.le (by norm_num)
      _ ≤ 2 * Real.exp (-256 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hlow (by norm_num)
  have hcontra : (2:ℝ)/729 ≤ 1/27000 := le_trans hlower hr
  norm_num at hcontra

end Hagi.Contracts.GatePipeline
