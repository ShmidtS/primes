/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Energy.PoEBound
set_option linter.style.header false

/-!
# Мост II рецензии: CertifiedEstimator — h_emp_* → confidence-certified

Аудит round-113/рецензия: 286 посылок `h_emp_*` — измеренные
эмпирические константы, входящие в теоремы как гипотезы. Этот
модуль строит первый механизм их сертификации: классический
Hoeffding bound на КОНЕЧНОМ произведении пространств, целиком в
стиле репозитория (Fintype-суммы, события — Finset-фильтры,
без MeasureTheory).

**Что доказано:**

* `prodPf_univ` — нормальность (факторизация `Finset.prod_univ_sum`).
* `prodE_exp_sum` — независимость в mgf-форме: E[e^{Σ gᵢ(ωᵢ)}]
  факторизуется в произведение пер-координатных ожиданий.
* `markov_ge` — конечный Markov: c·P(A) ≤ E[f] при f ≥ c на A.
* `coord_mgf_bound` — пер-координатная chord-лемма (из
  `mgf_hoeffding_ab` PoEBound): для X ∈ [0,1] E[e^{λ(X−μ)}] ≤ e^{λ²/8}.
* `hoeffding_chernoff` — P(ΣXᵢ − Σμᵢ ≥ t) ≤ exp(−λt + nλ²/8).
* `hoeffding_tail` — оптимум λ = 4t/n: P(ΣXᵢ − Σμᵢ ≥ t) ≤ e^{−2t²/n}.
* `hoeffding_mean_tail`, `hoeffding_mean_tail_low`,
  `hoeffding_two_sided` — для среднего (t = nε):
  P(μ̂ − μ ≥ ε) ≤ e^{−2nε²}; двусторонняя ≤ 2e^{−2nε²}.
* `cert_upper`, `cert_lower` — односторонние доверительные границы.
* `certified_premise` — МОСТ: измеренный margin
  ΣÂ + 2nε ≤ ΣB̂ (парные выборки) сертифицирует истинность
  μ_A ≤ μ_B с вероятностью ≥ 1 − 2e^{−2nε²} — форма, в которую
  переводятся посылки `h_emp_` (γ, ρ, β, пороги) из GainRenewal /
  FrontierScaling / SafeQPRobust.

**Честная граница**: репрезентативность выборки (координатные
распределения = распределения измерений) остаётся на стороне
измерения; модуль сертифицирует СТАТИСТИЧЕСКУЮ часть моста
(концентрация + union bound).
-/

open Finset Real

namespace Hagi

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Конечное произведение пространств -/

/-- Плотность произведения независимых координатных распределений. -/
def prodDens {n : ℕ} (p : Fin n → V → ℝ) (ω : Fin n → V) : ℝ := ∏ i, p i (ω i)

/-- Математическое ожидание на произведении (конечная сумма). -/
def prodE {n : ℕ} (p : Fin n → V → ℝ) (f : (Fin n → V) → ℝ) : ℝ :=
  ∑ ω, prodDens p ω * f ω

/-- Вероятность события-предиката. -/
def prodPq {n : ℕ} (p : Fin n → V → ℝ) (q : (Fin n → V) → Prop)
    [DecidablePred q] : ℝ :=
  prodE p (fun ω => if q ω then (1:ℝ) else 0)

/-- Предикат «координатные веса — вероятностные векторы». -/
def IsProbSys {n : ℕ} (p : Fin n → V → ℝ) : Prop :=
  ∀ i, (∀ v, 0 ≤ p i v) ∧ ∑ v, p i v = 1

theorem prodDens_nonneg {n : ℕ} {p : Fin n → V → ℝ} (hp : IsProbSys p)
    (ω : Fin n → V) : 0 ≤ prodDens p ω :=
  Finset.prod_nonneg fun i _ => (hp i).1 (ω i)

/-- Факторизация суммы по пространству функций (независимость). -/
theorem sum_prod_factor {n : ℕ} (f : ∀ i : Fin n, V → ℝ) :
    ∑ ω : Fin n → V, ∏ i, f i (ω i) = ∏ i, ∑ v, f i v := by
  classical
  have h := Finset.prod_univ_sum (t := fun _ => (Finset.univ : Finset V)) f
  rw [Fintype.piFinset_univ] at h
  exact h.symm

/-- Нормальность: полная масса произведения равна 1. -/
theorem prodE_one {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p) :
    prodE p (fun _ => (1:ℝ)) = 1 := by
  unfold prodE prodDens
  simp only [mul_one]
  rw [sum_prod_factor]
  exact Finset.prod_eq_one fun i _ => (hp i).2

/-- Верхняя граница вероятности: P(q) ≤ 1. -/
theorem prodPq_le_one {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (q : (Fin n → V) → Prop) [DecidablePred q] : prodPq p q ≤ 1 := by
  have h1 : prodPq p q ≤ prodE p (fun _ => (1:ℝ)) := by
    unfold prodPq prodE
    refine Finset.sum_le_sum fun ω _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (prodDens_nonneg hp ω)
    by_cases h : q ω <;> simp [h]
  rw [prodE_one p hp] at h1
  exact h1

/-- Дополнение: P(¬q) = 1 − P(q). -/
theorem prodPq_compl {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (q : (Fin n → V) → Prop) [DecidablePred q] :
    prodPq p (fun ω => ¬ q ω) = 1 - prodPq p q := by
  classical
  have hsplit : prodPq p q + prodPq p (fun ω => ¬ q ω)
      = prodE p (fun _ => (1:ℝ)) := by
    unfold prodPq prodE
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← mul_add]
    congr 1
    by_cases h : q ω <;> simp [h]
  rw [prodE_one p hp] at hsplit
  linarith

/-- Монотонность вероятности. -/
theorem prodPq_mono {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (q r : (Fin n → V) → Prop) [DecidablePred q] [DecidablePred r]
    (hqr : ∀ ω, q ω → r ω) :
    prodPq p q ≤ prodPq p r := by
  classical
  unfold prodPq prodE
  refine Finset.sum_le_sum fun ω _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (prodDens_nonneg hp ω)
  rcases em (q ω) with h | h
  · rcases em (r ω) with h' | h'
    · simp [h, h']
    · exact absurd (hqr ω h) h'
  · rcases em (r ω) with h' | h'
    · simp [h, h']
    · simp [h, h']

/-- Union bound: P(q ∨ r) ≤ P(q) + P(r). -/
theorem prodPq_union_le {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (q r : (Fin n → V) → Prop) [DecidablePred q] [DecidablePred r] :
    prodPq p (fun ω => q ω ∨ r ω) ≤ prodPq p q + prodPq p r := by
  classical
  unfold prodPq prodE
  beta_reduce
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hdens : 0 ≤ prodDens p ω := prodDens_nonneg hp ω
  rcases em (q ω) with h | h <;> rcases em (r ω) with h' | h' <;>
    simp [h, h'] <;> nlinarith [hdens]

/-! ## Независимость в mgf-форме -/

/-- MGF суммы факторизуется (независимость координат). -/
theorem prodE_exp_sum {n : ℕ} (p : Fin n → V → ℝ)
    (g : Fin n → V → ℝ) :
    prodE p (fun ω => Real.exp (∑ i, g i (ω i)))
      = ∏ i, ∑ v, p i v * Real.exp (g i v) := by
  unfold prodE prodDens
  have h : ∀ ω : Fin n → V,
      (∏ i, p i (ω i)) * Real.exp (∑ i, g i (ω i))
        = ∏ i, (p i (ω i) * Real.exp (g i (ω i))) := by
    intro ω
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  simp only [h]
  exact sum_prod_factor (fun i v => p i v * Real.exp (g i v))

/-! ## Конечный Markov -/

/-- Конечный Markov/Chernoff-шаг: если f ≥ c на событии q и
f ≥ 0 всюду, то c·P(q) ≤ E[f]. -/
theorem markov_ge {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (f : (Fin n → V) → ℝ) (hf : ∀ ω, 0 ≤ f ω) (c : ℝ)
    (q : (Fin n → V) → Prop) [DecidablePred q]
    (hA : ∀ ω, q ω → c ≤ f ω) :
    c * prodPq p q ≤ prodE p f := by
  classical
  have hfinal : prodE p (fun ω => if q ω then c else 0) = c * prodPq p q := by
    unfold prodPq prodE
    beta_reduce
    have hpoint : (fun ω => prodDens p ω * (if q ω then c else 0))
        = fun ω => c * (prodDens p ω * (if q ω then (1:ℝ) else 0)) := by
      funext ω
      by_cases h : q ω <;> simp [h] <;> ring
    rw [hpoint, Finset.mul_sum]
  have hmid : prodE p (fun ω => if q ω then c else 0)
      ≤ prodE p (fun ω => if q ω then f ω else 0) := by
    unfold prodE
    refine Finset.sum_le_sum fun ω _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (prodDens_nonneg hp ω)
    rcases em (q ω) with h | h
    · simp only [if_pos h]
      exact hA ω h
    · simp [h]
  have hlast : prodE p (fun ω => if q ω then f ω else 0) ≤ prodE p f := by
    unfold prodE
    refine Finset.sum_le_sum fun ω _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (prodDens_nonneg hp ω)
    rcases em (q ω) with h | h
    · simp [h]
    · simp [h, hf ω]
  calc c * prodPq p q = prodE p (fun ω => if q ω then c else 0) := hfinal.symm
    _ ≤ prodE p (fun ω => if q ω then f ω else 0) := hmid
    _ ≤ prodE p f := hlast

/-! ## Мультипликативная монотонность (для ℝ; MulLeftMono-инстанс
недоступен в текущем Mathlib module-изоляции) -/

private theorem prod_le_prod_real {n : ℕ} (F G : Fin n → ℝ)
    (hF : ∀ i, 0 ≤ F i) (hFG : ∀ i, F i ≤ G i) :
    ∏ i, F i ≤ ∏ i, G i := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      have hGnn : ∀ i, 0 ≤ G i := fun i => le_trans (hF i) (hFG i)
      have hstep1 : (∏ i : Fin m, F (Fin.castSucc i)) * F (Fin.last m)
          ≤ (∏ i : Fin m, G (Fin.castSucc i)) * F (Fin.last m) :=
        mul_le_mul_of_nonneg_right
          (ih (fun i => F (Fin.castSucc i)) (fun i => G (Fin.castSucc i))
            (fun i => hF (Fin.castSucc i))
            (fun i => hFG (Fin.castSucc i)))
          (hF (Fin.last m))
      have hstep2 : (∏ i : Fin m, G (Fin.castSucc i)) * F (Fin.last m)
          ≤ (∏ i : Fin m, G (Fin.castSucc i)) * G (Fin.last m) :=
        mul_le_mul_of_nonneg_left (hFG (Fin.last m))
          (Finset.prod_nonneg fun i _ => hGnn (Fin.castSucc i))
      exact le_trans hstep1 hstep2

/-! ## Hoeffding -/

/-- Координатное среднее μᵢ = Σ_v pᵢ(v)·Xᵢ(v). -/
def coordMean {n : ℕ} (p : Fin n → V → ℝ) (X : Fin n → V → ℝ) (i : Fin n) : ℝ :=
  ∑ v, p i v * X i v

/-- Центрированная сумма ΣXᵢ(ωᵢ) − Σμᵢ. -/
def centeredSum {n : ℕ} (p : Fin n → V → ℝ) (X : Fin n → V → ℝ)
    (ω : Fin n → V) : ℝ := ∑ i, X i (ω i) - ∑ i, coordMean p X i

/-- Линейный член MGF центрирования равен нулю:
Σ_v p·λ(X−μ) = 0. -/
theorem coord_center_zero {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (lam : ℝ) (i : Fin n) :
    ∑ v, p i v * (lam * (X i v - coordMean p X i)) = 0 := by
  set μ := coordMean p X i with hmu
  have h1 : ∑ v, p i v * (lam * (X i v - μ))
      = lam * (∑ v, p i v * X i v - ∑ v, p i v * μ) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hsum1 : ∑ v, p i v * X i v = μ := rfl
  have hsum2 : ∑ v, p i v * μ = μ := by
    rw [← Finset.sum_mul, (hp i).2, one_mul]
  rw [h1, hsum1, hsum2, sub_self, mul_zero]

/-- Пер-координатная chord-лемма (следствие `mgf_hoeffding_ab`):
для X ∈ [0,1] со средним μ E[e^{λ(X−μ)}] ≤ e^{λ²/8}. -/
theorem coord_mgf_bound {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (i : Fin n) :
    ∑ v, p i v * Real.exp (lam * (X i v - coordMean p X i))
      ≤ Real.exp (lam ^ 2 / 8) := by
  set μ : ℝ := coordMean p X i with hmu
  have hq := (hp i).1
  have hq1 := (hp i).2
  have hchord := mgf_hoeffding_ab (p i) (fun v => lam * (X i v - μ))
    hq hq1 (lam * (0 - μ)) (lam * (1 - μ))
    (fun v => by
      apply mul_le_mul_of_nonneg_left _ hlam
      have hx := hX i v
      linarith [hx.1, hx.2])
    (fun v => by
      apply mul_le_mul_of_nonneg_left _ hlam
      have hx := hX i v
      linarith [hx.1, hx.2])
  have hlin := coord_center_zero p hp X lam i
  have hrange : lam * (1 - μ) - lam * (0 - μ) = lam := by ring
  rw [hrange, hlin] at hchord
  simp only [zero_add] at hchord
  have hpos : 0 < ∑ v, p i v * Real.exp (lam * (X i v - μ)) := by
    obtain ⟨v0, _, hv0ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
      rw [hq1]; exact one_ne_zero)
    have hv0pos : 0 < p i v0 :=
      lt_of_le_of_ne (hq v0) (fun hc => hv0ne hc.symm)
    exact Finset.sum_pos' (fun v _ =>
      mul_nonneg (hq v) (Real.exp_pos _).le)
      ⟨v0, Finset.mem_univ v0, mul_pos hv0pos (Real.exp_pos _)⟩
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr hchord
/-- MGF центрированной суммы: E[e^{λ·(ΣX−Σμ)}] ≤ e^{nλ²/8}. -/
theorem sum_mgf_bound {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    prodE p (fun ω => Real.exp (lam * centeredSum p X ω))
      ≤ Real.exp ((n : ℝ) * lam ^ 2 / 8) := by
  have hfactor := prodE_exp_sum p
    (fun i v => lam * (X i v - coordMean p X i))
  have hinside : (fun ω : Fin n → V => Real.exp (∑ i, lam *
        (X i (ω i) - coordMean p X i)))
      = fun ω => Real.exp (lam * centeredSum p X ω) := by
    funext ω
    unfold centeredSum
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
  rw [hinside] at hfactor
  rw [hfactor]
  calc ∏ i, ∑ v, p i v * Real.exp (lam * (X i v - coordMean p X i))
      ≤ ∏ i, Real.exp (lam ^ 2 / 8) :=
        prod_le_prod_real _ _
          (fun i => Finset.sum_nonneg fun v _ =>
            mul_nonneg ((hp i).1 _) (Real.exp_pos _).le)
          (fun i => coord_mgf_bound p hp X hX lam hlam i)
    _ = Real.exp ((n : ℝ) * lam ^ 2 / 8) := by
        rw [Finset.prod_const]
        simp only [Finset.card_univ, Fintype.card_fin]
        rw [mul_div_assoc, Real.exp_nat_mul]

/-- Верхний хвост (Chernoff): P(ΣX−Σμ ≥ t) ≤ exp(−λt + nλ²/8). -/
theorem hoeffding_chernoff {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (lam t : ℝ) (hlam : 0 < lam) :
    prodPq p (fun ω => t ≤ centeredSum p X ω)
      ≤ Real.exp (- lam * t + (n : ℝ) * lam ^ 2 / 8) := by
  classical
  have hfexp : ∀ ω : Fin n → V, 0 ≤ Real.exp (lam * centeredSum p X ω) :=
    fun ω => (Real.exp_pos _).le
  have hmarkov := markov_ge p hp
    (fun ω => Real.exp (lam * centeredSum p X ω)) hfexp
    (Real.exp (lam * t)) (fun ω => t ≤ centeredSum p X ω)
    (fun ω hω => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hω hlam.le))
  have hmgf := sum_mgf_bound p hp X hX lam hlam.le
  have hexp : 0 < Real.exp (lam * t) := Real.exp_pos _
  have hle : Real.exp (lam * t) * prodPq p (fun ω => t ≤ centeredSum p X ω)
      ≤ Real.exp ((n : ℝ) * lam ^ 2 / 8) := le_trans hmarkov hmgf
  have hdiv : prodPq p (fun ω => t ≤ centeredSum p X ω)
      ≤ Real.exp ((n : ℝ) * lam ^ 2 / 8) / Real.exp (lam * t) :=
    (le_div_iff₀' hexp).mpr hle
  rw [← Real.exp_sub] at hdiv
  have hring : - lam * t + (n : ℝ) * lam ^ 2 / 8
      = (n : ℝ) * lam ^ 2 / 8 - lam * t := by ring
  rw [hring]
  exact hdiv

/-- Оптимум λ = 4t/n: P(ΣX−Σμ ≥ t) ≤ exp(−2t²/n). -/
theorem hoeffding_tail {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    prodPq p (fun ω => t ≤ centeredSum p X ω)
      ≤ Real.exp (- 2 * t ^ 2 / (n : ℝ)) := by
  have h := hoeffding_chernoff p hp X hX (4 * t / (n : ℝ)) t
    (div_pos (mul_pos (by norm_num) ht) (Nat.cast_pos.mpr hn))
  have hexpon : - (4 * t / (n : ℝ)) * t + (n : ℝ) * (4 * t / (n : ℝ)) ^ 2 / 8
      = - 2 * t ^ 2 / (n : ℝ) := by
    field_simp
    try ring
  rw [hexpon] at h
  exact h

/-- Верхний хвост среднего (t = nε): P(μ̂ − μ ≥ ε) ≤ e^{−2nε²}. -/
theorem hoeffding_mean_tail {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    prodPq p (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω)
      ≤ Real.exp (- 2 * (n : ℝ) * eps ^ 2) := by
  have h := hoeffding_tail p hp X hX hn ((n : ℝ) * eps)
    (mul_pos (Nat.cast_pos.mpr hn) heps)
  have hexpon : - 2 * ((n : ℝ) * eps) ^ 2 / (n : ℝ)
      = - 2 * (n : ℝ) * eps ^ 2 := by
    have hn' : ((n : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    field_simp
    try ring
  rw [hexpon] at h
  exact h

/-- Нижний хвост: P(μ − μ̂ ≥ ε) ≤ e^{−2nε²} (замена X ↦ 1−X). -/
theorem hoeffding_mean_tail_low {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    prodPq p (fun ω => centeredSum p X ω ≤ - (n : ℝ) * eps)
      ≤ Real.exp (- 2 * (n : ℝ) * eps ^ 2) := by
  classical
  have hYb : ∀ i v, 0 ≤ (1 - X i v) ∧ (1 - X i v) ≤ 1 := by
    intro i v; have hx := hX i v
    constructor <;> linarith [hx.1, hx.2]
  have hflip : ∀ ω : Fin n → V,
      centeredSum p (fun i v => 1 - X i v) ω = - centeredSum p X ω := by
    intro ω
    unfold centeredSum
    have hA : ∑ i : Fin n, (1 - X i (ω i) : ℝ)
        = (n : ℝ) - ∑ i : Fin n, X i (ω i) := by
      rw [Finset.sum_sub_distrib]
      have hone : ∑ i : Fin n, (1:ℝ) = (n : ℝ) := by simp
      rw [hone]
    have hB : ∑ i : Fin n, coordMean p (fun i v => 1 - X i v) i
        = (n : ℝ) - ∑ i : Fin n, coordMean p X i := by
      have hpt : ∀ i : Fin n,
          coordMean p (fun i v => 1 - X i v) i
            = (∑ v, p i v) - coordMean p X i := by
        intro i
        unfold coordMean
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [mul_sub, mul_one]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib]
      have h4 : ∀ i : Fin n, ∑ v, p i v = 1 := fun i => (hp i).2
      simp only [h4] at *
      have hone : ∑ i : Fin n, (1:ℝ) = (n : ℝ) := by simp
      rw [hone]
    rw [hA, hB]

    ring
  have hmono : prodPq p (fun ω => centeredSum p X ω ≤ - (n : ℝ) * eps)
      ≤ prodPq p (fun ω => (n : ℝ) * eps
        ≤ centeredSum p (fun i v => 1 - X i v) ω) :=
    prodPq_mono p hp _ _ (fun ω hω => by rw [hflip]; linarith)
  exact le_trans hmono
    (hoeffding_mean_tail p hp (fun i v => 1 - X i v) hYb hn eps heps)

/-- Двусторонний хвост: P(|μ̂ − μ| ≥ ε) ≤ 2e^{−2nε²}. -/
theorem hoeffding_two_sided {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    prodPq p (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω
        ∨ centeredSum p X ω ≤ - (n : ℝ) * eps)
      ≤ 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) := by
  classical
  have h1 := hoeffding_mean_tail p hp X hX hn eps heps
  have h2 := hoeffding_mean_tail_low p hp X hX hn eps heps
  have hu := prodPq_union_le p hp
    (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω)
    (fun ω => centeredSum p X ω ≤ - (n : ℝ) * eps)
  exact le_trans hu (by linarith)

/-! ## Мост: сертификация h_emp-посылок -/

/-- Односторонняя верхняя граница: истинная сумма средних Σμ не
превышает измеренной ΣX более чем на nε с вероятностью
≥ 1 − e^{−2nε²} (верхний хвост + дополнение). -/
theorem cert_upper {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω => centeredSum p X ω ≤ (n : ℝ) * eps) := by
  classical
  have htail := hoeffding_mean_tail p hp X hX hn eps heps
  have hcompl := prodPq_compl p hp
    (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω)
  have hmono : prodPq p (fun ω => ¬((n : ℝ) * eps ≤ centeredSum p X ω))
      ≤ prodPq p (fun ω => centeredSum p X ω ≤ (n : ℝ) * eps) :=
    prodPq_mono p hp _ _ (fun ω h => by
      push_neg at h
      exact le_of_lt h)
  rw [hcompl] at hmono
  linarith

/-- Односторонняя нижняя граница: измеренная ΣX не ниже истинной
Σμ более чем на nε с вероятностью ≥ 1 − e^{−2nε²}. -/
theorem cert_lower {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω => - (n : ℝ) * eps ≤ centeredSum p X ω) := by
  classical
  have htail := hoeffding_mean_tail_low p hp X hX hn eps heps
  have hcompl := prodPq_compl p hp
    (fun ω => centeredSum p X ω ≤ - (n : ℝ) * eps)
  have hmono : prodPq p (fun ω => ¬(centeredSum p X ω ≤ - (n : ℝ) * eps))
      ≤ prodPq p (fun ω => - (n : ℝ) * eps ≤ centeredSum p X ω) :=
    prodPq_mono p hp _ _ (fun ω h => by
      push_neg at h
      exact le_of_lt h)
  rw [hcompl] at hmono
  linarith

/-- **МОСТ II**: измеренный margin сертифицирует посылку
`h_emp_`-типа «A ≤ B». X измеряет величину A, Y — величину B
(парные выборки). Если на исходе ω выполнен измеренный margin
ΣX(ω) + 2nε ≤ ΣY(ω), то истинные средние удовлетворяют
μ_A ≤ μ_B — с вероятностью ≥ 1 − 2e^{−2nε²}: измерительное
событие вложено в объединение двух хвостов, каждый ≤ e^{−2nε²}. -/
theorem certified_premise {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X Y : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hY : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω =>
        ∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → ∑ i, coordMean p X i ≤ ∑ i, coordMean p Y i) := by
  classical
  set μA := ∑ i, coordMean p X i with hAdef
  set μB := ∑ i, coordMean p Y i with hBdef
  set E1 : (Fin n → V) → Prop :=
    fun ω => (n : ℝ) * eps < μA - ∑ i, X i (ω i) with hE1def
  set E2 : (Fin n → V) → Prop :=
    fun ω => (n : ℝ) * eps < ∑ i, Y i (ω i) - μB with hE2def
  -- E1 ⊆ нижний хвост X, E2 ⊆ верхний хвост Y
  have hE1le : prodPq p E1
      ≤ prodPq p (fun ω => centeredSum p X ω ≤ - (n : ℝ) * eps) :=
    prodPq_mono p hp _ _ (fun ω hω => by
      have h1' : (n : ℝ) * eps < μA - ∑ i, X i (ω i) := hω
      simp only [centeredSum]
      linarith [h1'])
  have hE2le : prodPq p E2
      ≤ prodPq p (fun ω => (n : ℝ) * eps ≤ centeredSum p Y ω) :=
    prodPq_mono p hp _ _ (fun ω hω => by
      have h2' : (n : ℝ) * eps < ∑ i, Y i (ω i) - μB := hω
      simp only [centeredSum]
      linarith [h2'])
  have h1 := hoeffding_mean_tail_low p hp X hX hn eps heps
  have h2 := hoeffding_mean_tail p hp Y hY hn eps heps
  have hu := prodPq_union_le p hp E1 E2
  have hbad : prodPq p E1 + prodPq p E2
      ≤ 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) := by
    linarith [le_trans hE1le h1, le_trans hE2le h2]
  -- отрицание импликации ⊆ E1 ∪ E2
  set q : (Fin n → V) → Prop :=
    fun ω => ∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
      ∧ μB < μA with hqdef
  have hsub : prodPq p q ≤ prodPq p (fun ω => E1 ω ∨ E2 ω) :=
    prodPq_mono p hp _ _ (by
      rintro ω ⟨hM, hAB⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨hn1, hn2⟩ := hcon
      have h1' : μA - ∑ i, X i (ω i) ≤ (n : ℝ) * eps :=
        not_lt.mp hn1
      have h2' : ∑ i, Y i (ω i) - μB ≤ (n : ℝ) * eps :=
        not_lt.mp hn2
      have : μA ≤ μB := by linarith
      linarith)
  have hqle : prodPq p q ≤ 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) := by
    refine le_trans hsub ?_
    exact le_trans hu hbad
  -- P(импликация) ≥ 1 − P(q): дополнение + монотонность
  have hcompl := prodPq_compl p hp q
  have hmono : prodPq p (fun ω => ¬ q ω)
      ≤ prodPq p (fun ω =>
          ∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
            → ∑ i, coordMean p X i ≤ ∑ i, coordMean p Y i) :=
    prodPq_mono p hp _ _ (by
      intro ω h hM
      by_contra hcon
      exact h ⟨hM, not_le.mp hcon⟩)
  rw [hcompl] at hmono
  linarith
