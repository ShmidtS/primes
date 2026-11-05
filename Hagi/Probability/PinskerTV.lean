/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

namespace Hagi.Probability

open Hagi.Prelude


open Finset Real

open Finset Real in
/-- **TV ≤ положительная
часть KL (R469)**:
(1/2)·Σ|p−q| ≤
Σ_{v: q<p} p·ln(p/q).
Механика: расщепление
Σ|p−q| = 2·Σ_A(p−q)
(дополнение меняет
знак) + per-v ln u ≥ 1−1/u
с u = q/p на A.
ВАЖНО: линейное
KL ≥ TV НЕВЕРНО
(контрпример p=(0.9,0.1),
q=(0.5,0.5): KL=0.368 <
TV=0.4; Пинскер требует √).
Кирпич
к Пинскеру. -/
theorem tv_le_pos_part_kl {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * (∑ v : V, |p v - q v|)
      ≤ ∑ v ∈ Finset.filter (fun v => q v < p v) Finset.univ,
        p v * Real.log (p v / q v) := by
  set A : Finset V := Finset.filter (fun v => q v < p v) Finset.univ with hA
  -- per-v on A: p - q <= p ln(p/q)
  have hpt : ∀ v ∈ A, p v - q v ≤ p v * Real.log (p v / q v) := by
    intro v hv
    have hlt : q v < p v := (Finset.mem_filter.mp hv).2
    have h1 : Real.log (q v / p v) ≤ q v / p v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq v) (hp v))
    have h2 : Real.log (p v / q v) = -(Real.log (q v / p v)) := by
      rw [Real.log_div (hp v).ne' (hq v).ne',
        Real.log_div (hq v).ne' (hp v).ne']
      ring
    rw [h2]
    have h3 : p v * (q v / p v) = q v := by
      field_simp [(hp v).ne']
    nlinarith [h1, h3, hp v]
  -- split: sum |p - q| = 2 * sum_A (p - q)
  have hsplit : ∑ v : V, |p v - q v| = 2 * (∑ v ∈ A, (p v - q v)) := by
    have h0 : ∑ v : V, (p v - q v) = 0 := by
      rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
    have hcompl : ∑ v ∈ Aᶜ, (p v - q v) = -(∑ v ∈ A, (p v - q v)) := by
      have hc := Finset.sum_add_sum_compl A (fun v => p v - q v)
      rw [show ∑ i ∈ A, (fun v => p v - q v) i
        = ∑ v ∈ A, (p v - q v) from rfl] at hc
      rw [h0] at hc
      linarith
    have habsA : ∀ v ∈ A, |p v - q v| = p v - q v := by
      intro v hv
      exact abs_of_pos (sub_pos.mpr (Finset.mem_filter.mp hv).2)
    have habsC : ∀ v ∈ Aᶜ, |p v - q v| = -(p v - q v) := by
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact abs_of_nonpos (by linarith)
    have hsplit2 : ∑ v : V, |p v - q v|
        = (∑ v ∈ A, |p v - q v|) + (∑ v ∈ Aᶜ, |p v - q v|) := by
      have h := Finset.sum_add_sum_compl A (fun v => |p v - q v|)
      simpa using h.symm
    rw [hsplit2]
    rw [Finset.sum_congr rfl (fun v hv => habsA v hv)]
    rw [Finset.sum_congr rfl (fun v hv => habsC v hv)]
    rw [Finset.sum_neg_distrib, hcompl]
    ring
  rw [hsplit]
  -- sum_A (p-q) <= sum_A (p ln) <= full sum
  have hnonneg : ∀ v ∈ A, (0:ℝ) ≤ p v * Real.log (p v / q v) := by
    intro v hv
    have hlt : q v < p v := (Finset.mem_filter.mp hv).2
    have hlog : (0:ℝ) ≤ Real.log (p v / q v) := by
      have : (1:ℝ) < p v / q v :=
        (one_lt_div (hq v)).mpr hlt
      exact le_of_lt (log_pos this)
    exact mul_nonneg (hp v).le hlog
  calc (1:ℝ)/2 * (2 * (∑ v ∈ A, (p v - q v)))
      = ∑ v ∈ A, (p v - q v) := by ring
    _ ≤ ∑ v ∈ A, p v * Real.log (p v / q v) :=
      Finset.sum_le_sum hpt

open Finset Real in
/-- **Бхаттачаря
≤ 1 (R470)**:
Σ√(p·q) ≤ 1 — Коши
(sum_mul_sq_le_sq_mul_sq
в форме квадратов с
sq_sqrt-свёрткой).
Кирпич Пинскер-цепи
(BC→KL). -/
theorem bhattacharyya_cauchy {V : Type*} [Fintype V]
    (p q : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 ≤ q v)
    (hp1 : ∑ v : V, p v = 1) (hq1 : ∑ v : V, q v = 1) :
    (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)) ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    Finset.univ (fun v => Real.sqrt (p v)) (fun v => Real.sqrt (q v))
  have hsq : (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)) ^ 2
      ≤ (∑ v : V, p v) * (∑ v : V, q v) := by
    have h1 : (∑ v : V, Real.sqrt (p v) ^ 2) = ∑ v : V, p v := by
      exact Finset.sum_congr rfl (fun v _ => by
        rw [sq_sqrt (hp v)])
    have h2 : (∑ v : V, Real.sqrt (q v) ^ 2) = ∑ v : V, q v := by
      exact Finset.sum_congr rfl (fun v _ => by
        rw [sq_sqrt (hq v)])
    rw [h1, h2] at h
    simpa [pow_two] using h
  have hge : (0:ℝ) ≤ ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hp1' : (0:ℝ) ≤ (∑ v : V, p v) * (∑ v : V, q v) := by
    rw [hp1, hq1]; norm_num
  rw [hp1, hq1] at hsq
  norm_num at hsq
  norm_num at hsq
  by_contra hc
  have hgt : (1:ℝ) < ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
    push_neg at hc
    exact hc
  have h2 : (1:ℝ) < (∑ v : V, Real.sqrt (p v)
      * Real.sqrt (q v)) ^ 2 := by
    nlinarith [hgt]
  linarith [abs_le.mp hsq |>.2]

open Finset Real in
/-- **1 − BC ≤ KL/2 (R471)**:
1 − Σ√(p·q) ≤
(1/2)·Σp·ln(p/q).
Per-v ядро: с t := √(p/q):
p − √(pq) = √(pq)(t−1),
(1/2)p·ln(p/q) = √(pq)·t·ln t,
и t−1 ≤ t·ln t (из
ln u ≤ u−1 с u := 1/t).
С R470 (BC ≤ 1) замыкает
Пинскер-цепь: 1−BC ≤ KL/2. -/
theorem one_minus_bc_le_half_kl {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  have tlem : ∀ t : ℝ, 0 < t → t - 1 ≤ t * Real.log t := by
    intro t ht
    have h1 : Real.log t⁻¹ ≤ t⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    have h2 : t * Real.log t⁻¹ ≤ t * (t⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt ht)
    have h3 : t * (t⁻¹ - 1) = 1 - t := by
      field_simp
    have h6 : t * Real.log t = -(t * Real.log t⁻¹) := by
      rw [Real.log_inv t]; ring
    linarith
  have hsplit : 1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      = ∑ v : V, (p v - Real.sqrt (p v) * Real.sqrt (q v)) := by
    have h1 : ∑ v : V, (p v - Real.sqrt (p v) * Real.sqrt (q v))
        = (∑ v : V, p v)
          - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) :=
      by rw [Finset.sum_sub_distrib]
    rw [h1, hp1]
  have hsqpv : ∀ v : V, Real.sqrt (p v) * Real.sqrt (q v)
      * Real.sqrt (p v / q v) = p v := by
    intro v
    have h1 : Real.sqrt (p v) * Real.sqrt (q v)
        = Real.sqrt (p v * q v) :=
      (Real.sqrt_mul (hp v).le (q v)).symm
    have h2 : Real.sqrt (p v * q v) * Real.sqrt (p v / q v)
        = Real.sqrt (p v * q v * (p v / q v)) :=
      (Real.sqrt_mul (mul_nonneg (hp v).le (hq v).le)
        (p v / q v)).symm
    rw [h1, h2]
    have hfe : p v * q v * (p v / q v) = p v * p v := by
      field_simp [(hp v).ne', (hq v).ne']
    rw [hfe, ← sq (p v), Real.sqrt_sq_eq_abs, abs_of_pos (hp v)]
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  set t : ℝ := Real.sqrt (p v / q v) with ht_def
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos (hp v) (hq v))
  have hsq := hsqpv v
  have hte : p v / q v = t ^ 2 :=
    (Real.sq_sqrt (div_nonneg (hp v).le (hq v).le)).symm
  have hlogt : Real.log (p v / q v) = 2 * Real.log t := by
    rw [hte, show t ^ 2 = t * t from sq t,
      Real.log_mul (ne_of_gt htpos) (ne_of_gt htpos)]
    ring
  have hspos : (0:ℝ) < Real.sqrt (p v) * Real.sqrt (q v) :=
    mul_pos (Real.sqrt_pos.mpr (hp v)) (Real.sqrt_pos.mpr (hq v))
  have step1 : p v - Real.sqrt (p v) * Real.sqrt (q v)
      = Real.sqrt (p v) * Real.sqrt (q v) * (t - 1) := by
    have h2' : Real.sqrt (p v) * Real.sqrt (q v) * (t - 1)
        = Real.sqrt (p v) * Real.sqrt (q v) * t
          - Real.sqrt (p v) * Real.sqrt (q v) := by ring
    rw [h2', hsq]
  have hpv : p v * Real.log t
      = (Real.sqrt (p v) * Real.sqrt (q v) * t) * Real.log t := by
    rw [hsq]
  have step2 : (1/2) * (p v * Real.log (p v / q v))
      = Real.sqrt (p v) * Real.sqrt (q v) * (t * Real.log t) := by
    rw [hlogt]
    rw [show (1/2:ℝ) * (p v * (2 * Real.log t))
        = p v * Real.log t from by ring, hpv]
    ring
  rw [step1, step2]
  have h8 := tlem t htpos
  nlinarith

open Finset Real in
/-- **Пинскер,
слабая √-форма
(R472)**:
(1/2)·Σ|p−q| ≤
√(KL).
Цепь: тождество
|p−q| = |√p−√q|·(√p+√q)
+ Коши (суммы
квадратов) →
Σ|p−q| ² ≤
(2−2BC)(2+2BC) =
4(1−BC)(1+BC) ≤
8(1−BC) ≤ 4·KL
(R470: BC ≤ 1; R471:
1−BC ≤ KL/2) →
TV ≤ √(KL).
Выборочный код:
K на R469–R471.
Точная форма
(KL/2) требует
двоич-редукций
(DPI + калкулус) —
не в этом юните. -/
theorem pinsker_sqrt_kl {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, |p v - q v|
      ≤ Real.sqrt (∑ v : V, p v * Real.log (p v / q v)) := by
  set KL : ℝ := ∑ v : V, p v * Real.log (p v / q v) with hKL
  set BC : ℝ := ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) with hBC
  set s : V → ℝ := fun v => Real.sqrt (p v) - Real.sqrt (q v) with hs
  set t : V → ℝ := fun v => Real.sqrt (p v) + Real.sqrt (q v) with htt
  -- per-v: |p - q| = |s| * t
  have hv : ∀ v, |p v - q v| = |s v| * t v := by
    intro v
    have h1 : p v - q v = (Real.sqrt (p v) - Real.sqrt (q v))
        * (Real.sqrt (p v) + Real.sqrt (q v)) := by
      rw [show (Real.sqrt (p v) - Real.sqrt (q v))
          * (Real.sqrt (p v) + Real.sqrt (q v))
          = Real.sqrt (p v) ^ 2 - Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    rw [h1, abs_mul, abs_of_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  -- Cauchy
  have hC2 : (∑ v : V, |p v - q v|) ^ 2
      ≤ (∑ v : V, |s v| ^ 2) * (∑ v : V, t v ^ 2) := by
    have hC := Finset.sum_mul_sq_le_sq_mul_sq
      Finset.univ (fun v => |s v|) t
    rw [Finset.sum_congr rfl (fun v _ => (hv v).symm)] at hC
    exact hC
  -- sum of squares of s: 2 - 2 BC
  have hA : ∑ v : V, |s v| ^ 2 = 2 - 2 * BC := by
    have h2 : ∀ v : V, |s v| ^ 2 = p v + q v
        - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [sq_abs, show s v ^ 2 = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  -- sum of squares of t: 2 + 2 BC
  have hB : ∑ v : V, t v ^ 2 = 2 + 2 * BC := by
    have h2 : ∀ v : V, t v ^ 2 = p v + q v
        + 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [show t v ^ 2 = Real.sqrt (p v) ^ 2
          + 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  rw [hA, hB] at hC2
  -- BC <= 1 and chain
  have hBC1 : BC ≤ 1 :=
    bhattacharyya_cauchy p q (fun v => (hp v).le)
      (fun v => (hq v).le) hp1 hq1
  have hR : 1 - BC ≤ KL / 2 := by
    have := one_minus_bc_le_half_kl p q hp hp1 hq hq1
    rw [← hBC] at this
    linarith
  have h4 : (1 - BC) * (1 + BC) ≤ 2 * (1 - BC) := by
    by_contra hc
    push_neg at hc
    nlinarith [hBC1, sub_nonneg.mpr hBC1]
  have hM : 2 * (KL / 2) = KL := by field_simp
  have i1 : 2 * (1 - BC) ≤ KL := by linarith [hR, hM]
  have hstep : (∑ v : V, |p v - q v|) ^ 2 ≤ 4 * KL := by
    have hc := hC2
    have e1 : (2 - 2 * BC) * (2 + 2 * BC)
        = 4 * ((1 - BC) * (1 + BC)) := by ring
    rw [e1] at hc
    have h5 : 4 * ((1 - BC) * (1 + BC)) ≤ 4 * (2 * (1 - BC)) := by
      exact mul_le_mul_of_nonneg_left h4 (by norm_num)
    linarith [hc, h5, i1]
  -- final sqrt step
  have hS : (0:ℝ) ≤ ∑ v : V, |p v - q v| := by
    apply Finset.sum_nonneg
    intro v _
    exact abs_nonneg _
  have hs2 : (0:ℝ) ≤ (1/2) * ∑ v : V, |p v - q v| := by
    linarith [hS]
  have hS2 : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2 ≤ KL := by
    have e2 : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
        = (∑ v : V, |p v - q v|) ^ 2 / 4 := by ring
    linarith [hstep, e2]
  exact Real.le_sqrt_of_sq_le hS2

open Finset Real in
/-- **Дуальная
характеризация
TV (R473)**:
для любой 0 ≤ f ≤ 1
|E_p f − E_q f| ≤ TV.
Верх: расщепление
Σ(p−q)f →
Σ_A(p−q)f + 0 ≤
Σ_A(p−q) = TV;
низ — заменой
f → 1−f.
PAC-Bayes-кирпич (дуальность
TV). -/
theorem tv_dual_abs {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V → ℝ) (f : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hf0 : ∀ v, 0 ≤ f v) (hf1 : ∀ v, f v ≤ 1) :
    |∑ v : V, p v * f v - ∑ v : V, q v * f v|
      ≤ (1/2) * ∑ v : V, |p v - q v| := by
  set A : Finset V := Finset.filter (fun v => q v < p v) Finset.univ with hA
  -- TV split: (1/2) sum |p-q| = sum_A (p - q)
  have hT : (1/2) * ∑ v : V, |p v - q v|
      = ∑ v ∈ A, (p v - q v) := by
    have h0 : ∑ v : V, (p v - q v) = 0 := by
      rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
    have hcompl : ∑ v ∈ Aᶜ, (p v - q v) = -(∑ v ∈ A, (p v - q v)) := by
      have hc := Finset.sum_add_sum_compl A (fun v => p v - q v)
      rw [show ∑ i ∈ A, (fun v => p v - q v) i
        = ∑ v ∈ A, (p v - q v) from rfl] at hc
      rw [h0] at hc
      linarith
    have habsA : ∀ v ∈ A, |p v - q v| = p v - q v := by
      intro v hv
      exact abs_of_pos (sub_pos.mpr (Finset.mem_filter.mp hv).2)
    have habsC : ∀ v ∈ Aᶜ, |p v - q v| = -(p v - q v) := by
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact abs_of_nonpos (by linarith)
    have hsplit2 : ∑ v : V, |p v - q v|
        = (∑ v ∈ A, |p v - q v|) + (∑ v ∈ Aᶜ, |p v - q v|) := by
      have h := Finset.sum_add_sum_compl A (fun v => |p v - q v|)
      simpa using h.symm
    rw [hsplit2]
    rw [Finset.sum_congr rfl (fun v hv => habsA v hv),
      Finset.sum_congr rfl (fun v hv => habsC v hv)]
    rw [Finset.sum_neg_distrib, hcompl]
    ring
  -- upper bound for any 0<=f<=1
  have hupper : ∀ g : V → ℝ, (∀ v, 0 ≤ g v) → (∀ v, g v ≤ 1) →
      ∑ v : V, p v * g v - ∑ v : V, q v * g v
        ≤ (1/2) * ∑ v : V, |p v - q v| := by
    intro g hg0 hg1
    have hd : ∑ v : V, p v * g v - ∑ v : V, q v * g v
        = ∑ v : V, (p v - q v) * g v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    have hup1 : ∑ v ∈ A, (p v - q v) * g v
        ≤ ∑ v ∈ A, (p v - q v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (mul_le_mul_of_nonneg_left (hg1 v)
        (le_of_lt (sub_pos.mpr (Finset.mem_filter.mp hv).2))).trans
        (by rw [mul_one])
    have hup2 : ∑ v ∈ Aᶜ, (p v - q v) * g v ≤ 0 := by
      apply Finset.sum_nonpos
      intro v hv
      have hle : p v ≤ q v := by
        by_contra hc
        push_neg at hc
        rw [Finset.mem_compl] at hv
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      exact le_trans (mul_le_mul_of_nonneg_right
        (sub_nonpos.mpr hle) (hg0 v)) (by rw [zero_mul])
    calc ∑ v : V, p v * g v - ∑ v : V, q v * g v
        = ∑ v : V, (p v - q v) * g v := hd
      _ = (∑ v ∈ A, (p v - q v) * g v)
          + (∑ v ∈ Aᶜ, (p v - q v) * g v) := by
          have h := Finset.sum_add_sum_compl A
            (fun v => (p v - q v) * g v)
          linarith
      _ ≤ ∑ v ∈ A, (p v - q v) + 0 := by linarith
      _ = (1/2) * ∑ v : V, |p v - q v| := by
          rw [add_zero]; exact hT.symm
  have hup := hupper f hf0 hf1
  -- lower bound via 1 - f
  have hf0' : ∀ v, 0 ≤ 1 - f v := by intro v; linarith [hf1 v]
  have hf1' : ∀ v, 1 - f v ≤ 1 := by intro v; linarith [hf0 v]
  have hneg := hupper (fun v => 1 - f v) hf0' hf1'
  have hd2 : ∑ v : V, p v * (1 - f v) - ∑ v : V, q v * (1 - f v)
      = -(∑ v : V, p v * f v - ∑ v : V, q v * f v) := by
    have e3 : ∀ v : V, p v * (1 - f v) = p v - p v * f v :=
      fun v => by ring
    have e4 : ∀ v : V, q v * (1 - f v) = q v - q v * f v :=
      fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => e3 v),
      Finset.sum_congr rfl (fun v _ => e4 v),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hp1, hq1]
    linarith
  rw [abs_le]
  exact ⟨by linarith [hd2, hneg], hup⟩

open Finset Real in
/-- **−ln BC ≤ KL/2
(R474)**:
−ln Σ√(p·q) ≤
(1/2)·Σp·ln(p/q).
Log-sum R451 с
парой a := p,
b := √(p·q)
(LHS = ln(1/BC)); per-v:
p/√(pq) = √(p/q),
т.е. ln(p/√(pq)) =
(1/2)ln(p/q) (log_sqrt).
Эквив: BC ≥
e^{−KL/2} — кирпич
Бретаньоль–Юбера. -/
theorem neg_log_bc_le_half_kl {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hp1 : ∑ v : V, p v = 1) :
    -Real.log (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v))
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  have hper : ∀ v : V, p v / (Real.sqrt (p v) * Real.sqrt (q v))
      = Real.sqrt (p v / q v) := by
    intro v
    have hsq : Real.sqrt (p v) * Real.sqrt (p v) = p v := by
      rw [← sq (Real.sqrt (p v))]
      exact sq_sqrt (hp v).le
    have e3 : p v / (√(p v) * √(q v))
        = (Real.sqrt (p v) * Real.sqrt (p v))
          / (Real.sqrt (p v) * Real.sqrt (q v)) := by
      nth_rewrite 1 [← hsq]
      rfl
    have e4 : (Real.sqrt (p v) * Real.sqrt (p v))
        / (Real.sqrt (p v) * Real.sqrt (q v))
        = Real.sqrt (p v) / Real.sqrt (q v) := by
      exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr (hp v)).ne'
    exact e3.trans ((e4.trans
      (Real.sqrt_div (hp v).le (q v)).symm))
  have hlogper : ∀ v : V,
      Real.log (p v / (Real.sqrt (p v) * Real.sqrt (q v)))
      = (1/2) * Real.log (p v / q v) := by
    intro v
    rw [hper v, Real.log_sqrt ((div_nonneg (hp v).le (hq v).le))]
    ring
  have hBCpos : (0:ℝ) < ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) :=
    Finset.sum_pos (fun v _ => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have h := log_sum_ineq p
    (fun v => Real.sqrt (p v) * Real.sqrt (q v))
    hp (fun v => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
  simp only [hlogper] at h
  have hrhs : (∑ v : V, p v) * Real.log ((∑ v : V, p v)
      / (∑ v : V, Real.sqrt (p v) * Real.sqrt (q v)))
      = Real.log (1 / (∑ v : V, Real.sqrt (p v)
        * Real.sqrt (q v))) := by
    rw [hp1, one_mul]
  rw [hrhs] at h
  rw [← Real.log_inv, inv_eq_one_div]
  have hconv : ∑ x : V, p x * (1/2 * Real.log (p x / q x))
      = (1/2) * ∑ x : V, p x * Real.log (p x / q x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [← hconv]
  exact h

open Finset Real in
/-- **Бретаньоль–
Юбер (R475)**:
TV ≤
√(1−e^{−KL})
.
Цепь: Коши
(R472-механика) →
Σ|p−q|² ≤
4(1−BC²);
R474: BC ≥
e^{−KL/2} →
1−BC² ≤
1−e^{−KL}.
Тиснее R472 при
большом KL
(√(1−e^{−KL}) ≤ 1). -/
theorem tv_le_sqrt_one_minus_exp {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, |p v - q v|
      ≤ Real.sqrt (1 - Real.exp
        (-(∑ v : V, p v * Real.log (p v / q v)))) := by
  set KL : ℝ := ∑ v : V, p v * Real.log (p v / q v) with hKL
  set BC : ℝ := ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) with hBC
  set s : V → ℝ := fun v => Real.sqrt (p v) - Real.sqrt (q v) with hs
  set t : V → ℝ := fun v => Real.sqrt (p v) + Real.sqrt (q v) with htt
  have hv : ∀ v, |p v - q v| = |s v| * t v := by
    intro v
    have h1 : p v - q v = (Real.sqrt (p v) - Real.sqrt (q v))
        * (Real.sqrt (p v) + Real.sqrt (q v)) := by
      rw [show (Real.sqrt (p v) - Real.sqrt (q v))
          * (Real.sqrt (p v) + Real.sqrt (q v))
          = Real.sqrt (p v) ^ 2 - Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    rw [h1, abs_mul, abs_of_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hC2 : (∑ v : V, |p v - q v|) ^ 2
      ≤ (∑ v : V, |s v| ^ 2) * (∑ v : V, t v ^ 2) := by
    have hC := Finset.sum_mul_sq_le_sq_mul_sq
      Finset.univ (fun v => |s v|) t
    rw [Finset.sum_congr rfl (fun v _ => (hv v).symm)] at hC
    exact hC
  have hA : ∑ v : V, |s v| ^ 2 = 2 - 2 * BC := by
    have h2 : ∀ v : V, |s v| ^ 2 = p v + q v
        - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [sq_abs, show s v ^ 2 = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  have hB : ∑ v : V, t v ^ 2 = 2 + 2 * BC := by
    have h2 : ∀ v : V, t v ^ 2 = p v + q v
        + 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
      intro v
      rw [show t v ^ 2 = Real.sqrt (p v) ^ 2
          + 2 * (Real.sqrt (p v) * Real.sqrt (q v))
            + Real.sqrt (q v) ^ 2 from by ring,
        sq_sqrt (hp v).le, sq_sqrt (hq v).le]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp1, hq1]
    ring
  rw [hA, hB] at hC2
  have e1 : (2 - 2 * BC) * (2 + 2 * BC) = 4 * (1 - BC ^ 2) := by ring
  rw [e1] at hC2
  -- BC >= exp(-KL/2)
  have hBCpos : (0:ℝ) < BC := by
    rw [hBC]
    exact Finset.sum_pos (fun v _ => mul_pos (Real.sqrt_pos.mpr (hp v))
      (Real.sqrt_pos.mpr (hq v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hR74 := neg_log_bc_le_half_kl p q hp hq hp1
  rw [← hBC] at hR74
  rw [← hKL] at hR74
  have h2 : Real.exp (-(KL / 2)) ≤ BC := by
    have h1 : -(KL / 2) ≤ Real.log BC := by linarith [hR74]
    have h2p := Real.exp_le_exp.mpr h1
    rw [Real.exp_log hBCpos] at h2p
    exact h2p
  have e1b : (Real.exp (-(KL / 2))) ^ 2 = Real.exp (-(KL)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    linarith
  have hb2 : (Real.exp (-(KL / 2))) ^ 2 ≤ BC ^ 2 := by
    have hBCe : (0:ℝ) ≤ BC + Real.exp (-(KL / 2)) := by
      linarith [hBCpos, Real.exp_pos (-(KL / 2))]
    have hmul : (BC - Real.exp (-(KL / 2)))
        * (BC + Real.exp (-(KL / 2))) ≥ 0 :=
      mul_nonneg (sub_nonneg.mpr h2) hBCe
    have e3r : (BC - Real.exp (-(KL / 2)))
        * (BC + Real.exp (-(KL / 2)))
        = BC ^ 2 - (Real.exp (-(KL / 2))) ^ 2 := by ring
    rw [e3r] at hmul
    linarith
  have e2r : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
      = (∑ v : V, |p v - q v|) ^ 2 / 4 := by ring
  have hTV : ((1:ℝ)/2 * ∑ v : V, |p v - q v|) ^ 2
      ≤ 1 - Real.exp (-(KL)) := by
    linarith [hC2, e2r, hb2, e1b]
  exact Real.le_sqrt_of_sq_le hTV

open Finset Real in
/-- **Совместная
выпуклость KL
(R476)**: для c ∈ (0,1):
KL(c·p₁+(1−c)·p₂
‖ c·q₁+(1−c)·q₂)
≤
c·KL(p₁‖q₁) +
(1−c)·KL(p₂‖q₂).
Per-v — двухточечный
log-sum: R451 на
Fin 2 с парами
(c·p₁v, (1−c)·p₂v) и
(c·q₁v, (1−c)·q₂v);
разбавение диляций
mul_div_mul_left. -/
theorem kl_joint_convex {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p₁ p₂ q₁ q₂ : V → ℝ) (c : ℝ)
    (hp₁ : ∀ v, 0 < p₁ v) (hp₁1 : ∑ v : V, p₁ v = 1)
    (hp₂ : ∀ v, 0 < p₂ v) (hp₂1 : ∑ v : V, p₂ v = 1)
    (hq₁ : ∀ v, 0 < q₁ v) (hq₂ : ∀ v, 0 < q₂ v)
    (hc0 : 0 < c) (hc1 : c < 1) :
    ∑ v : V, (c * p₁ v + (1 - c) * p₂ v)
        * Real.log ((c * p₁ v + (1 - c) * p₂ v)
          / (c * q₁ v + (1 - c) * q₂ v))
      ≤ (1 - c) * (∑ v : V, p₂ v * Real.log (p₂ v / q₂ v))
        + c * (∑ v : V, p₁ v * Real.log (p₁ v / q₁ v)) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have ha : ∀ i : Fin 2,
      0 < (fun i => if i = 0 then c * p₁ v else (1 - c) * p₂ v) i := by
    intro i
    by_cases hz : i = 0
    · simp only [hz, if_pos hz]
      exact mul_pos hc0 (hp₁ v)
    · simp only [if_neg hz]
      exact mul_pos (by linarith) (hp₂ v)
  have hb : ∀ i : Fin 2,
      0 < (fun i => if i = 0 then c * q₁ v else (1 - c) * q₂ v) i := by
    intro i
    by_cases hz : i = 0
    · simp only [hz, if_pos hz]
      exact mul_pos hc0 (hq₁ v)
    · simp only [if_neg hz]
      exact mul_pos (by linarith) (hq₂ v)
  have hv := log_sum_ineq
    (fun i => if i = 0 then c * p₁ v else (1 - c) * p₂ v)
    (fun i => if i = 0 then c * q₁ v else (1 - c) * q₂ v)
    ha hb
  simp only [Fin.sum_univ_two] at hv
  simp only [if_pos rfl, if_neg (by omega : ¬((1 : Fin 2) = 0)),
    Fin.isValue, reduceIte] at hv
  rw [mul_div_mul_left _ _ hc0.ne',
    mul_div_mul_left _ _ (by linarith)] at hv
  have hv2 : (1 - c) * (p₂ v * Real.log (p₂ v / q₂ v))
      + c * (p₁ v * Real.log (p₁ v / q₁ v))
      = c * p₁ v * Real.log (p₁ v / q₁ v)
        + (1 - c) * p₂ v * Real.log (p₂ v / q₂ v) := by
    ring
  rw [hv2]
  linarith

open Finset Real in
/-- **Донскер–
Варадхан,
нижняя грань
(R477)**: KL(p‖q) ≥
E_p f −
ln(Σq·e^f).
Механика: софтмакс
r := q·e^f/Z,
KL(p‖r) ≥ 0 (R447),
per-v
ln(p/r) =
ln(p/q) − f + ln Z. -/
theorem kl_variational_lower {V : Type*} [Fintype V] [Nonempty V]
    (p q f : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    ∑ v : V, p v * Real.log (p v / q v)
      ≥ ∑ v : V, p v * f v
        - Real.log (∑ v : V, q v * Real.exp (f v)) := by
  set Z : ℝ := ∑ v : V, q v * Real.exp (f v) with hZ
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => mul_pos (hq v) (Real.exp_pos (f v)))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set r : V → ℝ := fun v => q v * Real.exp (f v) / Z with hr
  have hrpos : ∀ v, 0 < r v := fun v =>
    div_pos (mul_pos (hq v) (Real.exp_pos (f v))) hZpos
  have hS2 : (∑ v : V, q v * Real.exp (f v)) = Z := hZ.symm
  have hr1 : ∑ v : V, r v = 1 := by
    have e1 : ∑ v : V, r v
        = ∑ v : V, (q v * Real.exp (f v) / Z) := rfl
    rw [e1, ← Finset.sum_div, hS2]
    exact div_self hZpos.ne'
  have hkl := finite_kl_nonneg p r hp hp1 hrpos hr1
  have hper : ∀ v : V, Real.log (p v / r v)
      = Real.log (p v / q v) - f v + Real.log Z := by
    intro v
    have e1 : p v / r v
        = p v * Z / (q v * Real.exp (f v)) := by
      rw [hr]
      field_simp
    rw [e1, Real.log_div (mul_pos (hp v) hZpos).ne'
      (mul_pos (hq v) (Real.exp_pos (f v))).ne',
      Real.log_mul (hp v).ne' hZpos.ne',
      Real.log_div (hp v).ne' (hq v).ne']
    rw [Real.log_mul (hq v).ne'
      (Real.exp_pos (f v)).ne', Real.log_exp (f v)]
    ring
  have hper2 : ∀ v : V, p v * Real.log (p v / r v)
      = p v * Real.log (p v / q v) - p v * f v
        + p v * Real.log Z := by
    intro v
    rw [hper v]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hper2 v)] at hkl
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hkl
  have hZsum : ∑ v : V, p v * Real.log Z = Real.log Z := by
    rw [Finset.sum_congr rfl
      (fun v _ => mul_comm (p v) (Real.log Z)),
      ← Finset.mul_sum, hp1, mul_one]
  rw [hZsum] at hkl
  linarith

open Finset Real in
/-- **PAC-Чернофф
для событий
(R478)**: при
KL(p‖q) ≤ κ:
Σ_{v∈s} p ≤ κ +
ln(1+(e−1)·q(s))
— одложенная
софтмакс-форма
R477 с f :=
индикатором s;
ключевой
PAC-Bayes-кирпич. -/
theorem pac_chernoff_events {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q : V → ℝ) (s : Finset V) (κ : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hκ : ∑ v : V, p v * Real.log (p v / q v) ≤ κ) :
    ∑ v ∈ s, p v
      ≤ κ + Real.log (1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v) := by
  have hR := kl_variational_lower p q (fun v => if v ∈ s then (1:ℝ) else 0)
    hp hp1 hq hq1
  -- per-v equations
  have hpe1 : ∀ v ∈ s, p v * (if v ∈ s then (1:ℝ) else 0) = p v := by
    intro v hv; rw [if_pos hv, mul_one]
  have hpe2 : ∀ v ∈ sᶜ, p v * (if v ∈ s then (1:ℝ) else 0) = 0 := by
    intro v hv; rw [if_neg (Finset.mem_compl.mp hv), mul_zero]
  have hqe1 : ∀ v ∈ s,
      q v * Real.exp (if v ∈ s then (1:ℝ) else 0)
      = Real.exp 1 * q v := by
    intro v hv; rw [if_pos hv]; ring
  have hqe2 : ∀ v ∈ sᶜ,
      q v * Real.exp (if v ∈ s then (1:ℝ) else 0) = q v := by
    intro v hv
    rw [if_neg (Finset.mem_compl.mp hv), Real.exp_zero, mul_one]
  -- E_p[indicator] = p(s)
  have hEta : ∑ v : V, p v * (if v ∈ s then (1:ℝ) else 0)
      = ∑ v ∈ s, p v := by
    have h := Finset.sum_add_sum_compl s
      (fun v => p v * (if v ∈ s then (1:ℝ) else 0))
    rw [Finset.sum_congr rfl (fun v hv => hpe1 v hv)] at h
    have hX : ∑ v ∈ sᶜ, p v * (if v ∈ s then (1:ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun v hv => by rw [hpe2 v hv])
    linarith [h, hX]
  -- Z = 1 + (e-1) q(s)
  have hZeta : ∑ v : V, q v * Real.exp (if v ∈ s then (1:ℝ) else 0)
      = 1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v := by
    have h := Finset.sum_add_sum_compl s
      (fun v => q v * Real.exp (if v ∈ s then (1:ℝ) else 0))
    rw [Finset.sum_congr rfl (fun v hv => hqe1 v hv),
      Finset.sum_congr rfl (fun v hv => hqe2 v hv),
      ← Finset.mul_sum] at h
    have hC : ∑ v ∈ sᶜ, q v = 1 - ∑ v ∈ s, q v := by
      have hc := Finset.sum_add_sum_compl s (fun v => q v)
      rw [show ∑ i ∈ s, (fun v => q v) i = ∑ v ∈ s, q v from rfl,
        show ∑ i ∈ sᶜ, (fun v => q v) i = ∑ v ∈ sᶜ, q v from rfl,
        hq1] at hc
      linarith
    have hRr : Real.exp 1 * ∑ v ∈ s, q v
        + (1 - ∑ v ∈ s, q v)
        = 1 + (Real.exp 1 - 1) * ∑ v ∈ s, q v := by
      ring
    linarith [h, hC, hRr]
  rw [hEta, hZeta] at hR
  linarith [hR, hκ]


end Hagi.Probability

export Hagi.Probability (kl_variational_lower one_minus_bc_le_half_kl pinsker_sqrt_kl tv_dual_abs)

/-! ### Константная-4 форма Пинскера + CMI-итерация
(перенесено из Hagi.Information.Pinsker, консолидация:
один модуль = всё семейство Пинскера. Namespace сохранён —
потребители `Hagi.Information.pinsker4_fin` и т.д. не ломаются.) -/

open Hagi.Prelude Real
open scoped NNReal

namespace Hagi.Information

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- **Pinsker (constant 4), finite form**: for positive
distributions `q, p` (summing to 1) and any `f : V → [0,1]`,

  |∑ q·f − ∑ p·f| ≤ 2 * sqrt (klDef q p). -/
theorem pinsker4_fin (q p f : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * f v) ≤ 2 * Real.sqrt (klDef q p) := by
  classical
  set A : ℝ := ∑ v, Real.sqrt (q v * p v) with hA
  have hApos : 0 < A :=
    Finset.sum_pos (fun v _ => Real.sqrt_pos.mpr (mul_pos (hq v) (hp v)))
      Finset.univ_nonempty
  -- Σ q·√(p/q) = A
  have hsum : ∑ v, q v * Real.sqrt (p v / q v) = A := by
    rw [hA]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hL : (0:ℝ) ≤ q v * Real.sqrt (p v / q v) :=
      mul_nonneg (hq v).le (Real.sqrt_nonneg _)
    have hsq : (q v * Real.sqrt (p v / q v)) ^ 2 = q v * p v := by
      rw [mul_pow, Real.sq_sqrt (div_pos (hp v) (hq v)).le]
      field_simp
    calc q v * Real.sqrt (p v / q v)
        = Real.sqrt ((q v * Real.sqrt (p v / q v)) ^ 2) :=
          (Real.sqrt_sq hL).symm
      _ = Real.sqrt (q v * p v) := by rw [hsq]
  -- Jensen-free: Σ q ln t ≤ ln A  where Σ q t = A
  have hjensen : ∑ v, q v * Real.log (Real.sqrt (p v / q v)) ≤ Real.log A := by
    have h1 : ∀ v : V, Real.log (Real.sqrt (p v / q v) / A)
        ≤ Real.sqrt (p v / q v) / A - 1 :=
      fun v => Real.log_le_sub_one_of_pos
        (div_pos (Real.sqrt_pos.mpr (div_pos (hp v) (hq v))) hApos)
    have h2 : ∑ v, q v * (Real.sqrt (p v / q v) / A - 1) = 0 := by
      have hexp : ∀ v : V, q v * (Real.sqrt (p v / q v) / A - 1)
          = q v * Real.sqrt (p v / q v) / A - q v := by
        intro v
        ring
      rw [Finset.sum_congr rfl (fun v _ => hexp v)]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      rw [show ∑ v, q v * Real.sqrt (p v / q v) = A from hsum]
      rw [hsumq]
      field_simp
      ring
    have h3 : ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
        ≤ ∑ v, q v * (Real.sqrt (p v / q v) / A - 1) :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h1 v) (hq v).le
    rw [h2] at h3
    have h4 : ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
        = ∑ v, q v * Real.log (Real.sqrt (p v / q v)) - Real.log A := by
      have hexp : ∀ v : V,
          q v * Real.log (Real.sqrt (p v / q v) / A)
            = q v * Real.log (Real.sqrt (p v / q v)) - q v * Real.log A := by
        intro v
        rw [Real.log_div (Real.sqrt_pos.mpr (div_pos (hp v) (hq v))).ne'
          hApos.ne']
        rw [mul_sub]
        try rw [mul_div_cancel₀ (hq v).ne']
      calc ∑ v, q v * Real.log (Real.sqrt (p v / q v) / A)
          = ∑ v, (q v * Real.log (Real.sqrt (p v / q v))
              - q v * Real.log A) :=
            Finset.sum_congr rfl fun v _ => hexp v
        _ = ∑ v, q v * Real.log (Real.sqrt (p v / q v))
              - ∑ v, q v * Real.log A :=
              Finset.sum_sub_distrib _ _
        _ = ∑ v, q v * Real.log (Real.sqrt (p v / q v)) - Real.log A := by
            rw [Finset.sum_congr rfl
              (fun v _ => mul_comm (q v) (Real.log A))]
            rw [← Finset.mul_sum, hsumq, mul_one]
    rw [h4] at h3
    linarith
  -- KL = 2·Σ q ln√(q/p) = -2·Σ q ln√(p/q) ≥ -2 ln A
  have hklform : klDef q p
      = -2 * ∑ v, q v * Real.log (Real.sqrt (p v / q v)) := by
    unfold klDef
    have hterm : ∀ v : V,
        q v * Real.log (q v / p v)
          = -2 * (q v * Real.log (Real.sqrt (p v / q v))) := by
      intro v
      rw [Real.log_div (hq v).ne' (hp v).ne',
        show Real.log (Real.sqrt (p v / q v))
          = Real.log (p v / q v) / 2 from
          Real.log_sqrt (div_pos (hp v) (hq v)).le,
        Real.log_div (hp v).ne' (hq v).ne']
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    try rw [← Finset.mul_sum]
  -- final KL-part: KL ≥ -2 ln A ≥ 2(1 - A)
  have hkl : 2 * (1 - A) ≤ klDef q p := by
    have hlog : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos hApos
    have hge : -2 * Real.log A ≥ -2 * (A - 1) := by nlinarith
    have h1 : -2 * (A - 1) = 2 * (1 - A) := by ring
    rw [h1] at hge
    have hklraw : -2 * Real.log A ≤ klDef q p := by
      rw [hklform]
      have hin : ∑ v, q v * Real.log (Real.sqrt (p v / q v)) ≤ Real.log A := hjensen
      nlinarith [hin]
    linarith
  -- TV part: |Eq f - Ep f| ≤ Σ_{q≥p} (q - p) =: δ ≤ 2√2·H, H² = 1 - A
  set d : V → ℝ := fun v => q v - p v with hd
  set up : V → Prop := fun v => p v ≤ q v with hup
  -- E_q f - E_p f = Σ d·f
  have hdiff : ∑ v, q v * f v - ∑ v, p v * f v = ∑ v, (q v - p v) * f v := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  -- TV machinery: F = up-set, split, bound
  letI : DecidablePred (fun v : V => p v ≤ q v) := fun v => Classical.dec _
  set F : Finset V := Finset.univ.filter (fun v => p v ≤ q v) with hF
  have hsplit : ∑ v, (q v - p v) * f v
      = (∑ v ∈ F, (q v - p v) * f v) + ∑ v ∈ Fᶜ, (q v - p v) * f v :=
    (Finset.sum_add_sum_compl F (fun v => (q v - p v) * f v)).symm
  have hcompl : ∀ v ∈ Fᶜ, (q v - p v) * f v ≤ 0 := by
    intro v hv
    have hv' : ¬ (p v ≤ q v) := by
      have h1 : v ∉ F := Finset.mem_compl.mp hv
      by_contra hc
      exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
    nlinarith [(hf v).1]
  have hcomplsum : ∑ v ∈ Fᶜ, (q v - p v) * f v ≤ 0 := Finset.sum_nonpos hcompl
  -- upper bound: Σ d f ≤ Σ_F d
  have hupper : ∑ v, (q v - p v) * f v ≤ ∑ v ∈ F, (q v - p v) := by
    have hterm : ∀ v ∈ F, (q v - p v) * f v ≤ (q v - p v) := by
      intro v hv
      have hv' : p v ≤ q v := (Finset.mem_filter.mp hv).2
      nlinarith [(hf v).2]
    calc ∑ v, (q v - p v) * f v
        = (∑ v ∈ F, (q v - p v) * f v) + ∑ v ∈ Fᶜ, (q v - p v) * f v := hsplit
      _ ≤ (∑ v ∈ F, (q v - p v)) + 0 := by
          refine add_le_add (Finset.sum_le_sum hterm) hcomplsum
      _ = ∑ v ∈ F, (q v - p v) := by ring
  -- lower bound: -Σ d f ≤ Σ_F d  (by symmetry, using Σ d = 0)
  have hsumzero : ∑ v, (q v - p v) = 0 := by
    rw [Finset.sum_sub_distrib, hsumq, hsump, sub_self]
  -- δ := Σ_F (q - p) equals Σ_{Fᶜ} (p - q), both nonneg
  have hdelta_pos : (0:ℝ) ≤ ∑ v ∈ F, (q v - p v) := by
    have hterm : ∀ v ∈ F, (0:ℝ) ≤ q v - p v := by
      intro v hv
      have := (Finset.mem_filter.mp hv).2
      linarith
    exact Finset.sum_nonneg hterm
  have hsplit0 : (∑ v ∈ F, (q v - p v)) + (∑ v ∈ Fᶜ, (q v - p v)) = 0 := by
    have := Finset.sum_add_sum_compl F (fun v => q v - p v)
    linarith [this, hsumzero]
  -- |Σ d f| ≤ δ: upper via hupper, lower via complement side
  have hlower : -(∑ v, (q v - p v) * f v) ≤ ∑ v ∈ F, (q v - p v) := by
    -- -Σ df = Σ_{Fᶜ}(p-q)f - Σ_F (q-p)f  ≤ Σ_{Fᶜ}(p-q)
    have hterm : ∀ v : V, (p v - q v) * f v = -((q v - p v) * f v) := by
      intro v; ring
    have hsplit2 : ∑ v, (p v - q v) * f v
        = (∑ v ∈ F, (p v - q v) * f v) + ∑ v ∈ Fᶜ, (p v - q v) * f v :=
      (Finset.sum_add_sum_compl F (fun v => (p v - q v) * f v)).symm
    -- Σ_F (p-q)f ≤ 0
    have hFle : ∑ v ∈ F, (p v - q v) * f v ≤ 0 := by
      refine Finset.sum_nonpos fun v hv => ?_
      have hv' : p v ≤ q v := (Finset.mem_filter.mp hv).2
      nlinarith [(hf v).1]
    -- Σ_{Fᶜ}(p-q)f ≤ Σ_{Fᶜ}(p-q)
    have hcle : ∑ v ∈ Fᶜ, (p v - q v) * f v ≤ ∑ v ∈ Fᶜ, (p v - q v) := by
      refine Finset.sum_le_sum fun v hv => ?_
      have hv' : ¬ (p v ≤ q v) := by
        have h1 : v ∉ F := Finset.mem_compl.mp hv
        by_contra hc
        exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
      nlinarith [(hf v).2]
    -- Σ_{Fᶜ}(p-q) = δ
    have hcomp : ∑ v ∈ Fᶜ, (p v - q v) = ∑ v ∈ F, (q v - p v) := by
      have hsumcompl : ∑ v ∈ Fᶜ, (q v - p v) = -(∑ v ∈ F, (q v - p v)) := by
        have hall := Finset.sum_add_sum_compl F (fun v => q v - p v)
        have htot : (∑ v ∈ F, (q v - p v)) + (∑ v ∈ Fᶜ, (q v - p v))
            = ∑ v, (q v - p v) := hall
        rw [hsumzero] at htot
        linarith
      have hneg : ∑ v ∈ Fᶜ, (p v - q v) = -(∑ v ∈ Fᶜ, (q v - p v)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [hneg, hsumcompl, neg_neg]
    -- combine: -Σdf = Σ_F(p-q)f + Σ_{Fᶜ}(p-q)f ≤ 0 + δ = δ
    have hnegform : -(∑ v, (q v - p v) * f v)
        = ∑ v, (p v - q v) * f v := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hnegform, hsplit2]
    have hstep : (∑ v ∈ F, (p v - q v) * f v)
        + ∑ v ∈ Fᶜ, (p v - q v) * f v ≤ ∑ v ∈ F, (q v - p v) := by
      have h1 := add_le_add hFle hcle
      rw [hcomp] at h1
      linarith
    exact hstep
  have habs : abs (∑ v, (q v - p v) * f v) ≤ ∑ v ∈ F, (q v - p v) :=
    abs_le.mpr ⟨by linarith, hupper⟩
  -- Cauchy: δ = Σ_F (√q-√p)(√q+√p) ≤ √(Σ_F(√q-√p)²)·√(Σ_F(√q+√p)²)
  have hcauchy : ∑ v ∈ F, (q v - p v)
      ≤ Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
    have hterm : ∀ v ∈ F, (q v - p v)
        = (Real.sqrt (q v) - Real.sqrt (p v))
          * (Real.sqrt (q v) + Real.sqrt (p v)) := by
      intro v hv
      conv_lhs => rw [show q v = (Real.sqrt (q v)) ^ 2 from
          (Real.sq_sqrt (hq v).le).symm,
        show p v = (Real.sqrt (p v)) ^ 2 from (Real.sq_sqrt (hp v).le).symm]
      rw [mul_comm, ← sq_sub_sq]
    have hrewrite : ∑ v ∈ F, (q v - p v)
        = ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v))
            * (Real.sqrt (q v) + Real.sqrt (p v)) :=
      Finset.sum_congr rfl hterm
    rw [hrewrite]
    -- Cauchy-Schwarz on F
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun v => Real.sqrt (q v) - Real.sqrt (p v))
      (fun v => Real.sqrt (q v) + Real.sqrt (p v))
    have hP0 : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 :=
      Finset.sum_nonneg fun v _ => sq_nonneg _
    have hQ0 : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 :=
      Finset.sum_nonneg fun v _ => sq_nonneg _
    have hxy : (0:ℝ) ≤ ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v))
        * (Real.sqrt (q v) + Real.sqrt (p v)) := by
      rw [← hrewrite]
      exact hdelta_pos
    have hPQ : (Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)) ^ 2
        = (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
          * (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hQ0]
    have hr : (0:ℝ) ≤ Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        * Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2) := by
      positivity
    nlinarith [hxy, hPQ, hr, hsq]
  -- Σ_all (√q-√p)² = 2(1-A) ≥ Σ_F;  Σ_all (√q+√p)² = 2(1+A) ≤ 4
  have hallsub : ∑ v, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 = 2 * (1 - A) := by
    have hterm : ∀ v : V, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2
        = (q v + p v) - 2 * Real.sqrt (q v * p v) := by
      intro v
      rw [sub_sq, Real.sq_sqrt (hq v).le, Real.sq_sqrt (hp v).le,
        Real.sqrt_mul (hq v).le (p v)]
      ring
    have hsplit : ∑ v, ((q v + p v) - 2 * Real.sqrt (q v * p v))
        = (∑ v, q v + ∑ v, p v) - 2 * ∑ v, Real.sqrt (q v * p v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), hsplit, hA, hsumq, hsump]
    ring
  have halladd : ∑ v, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 = 2 * (1 + A) := by
    have hterm : ∀ v : V, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2
        = (q v + p v) + 2 * Real.sqrt (q v * p v) := by
      intro v
      rw [add_sq, Real.sq_sqrt (hq v).le, Real.sq_sqrt (hp v).le,
        Real.sqrt_mul (hq v).le (p v)]
      ring
    have hsplit : ∑ v, ((q v + p v) + 2 * Real.sqrt (q v * p v))
        = (∑ v, q v + ∑ v, p v) + 2 * ∑ v, Real.sqrt (q v * p v) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), hsplit, hA, hsumq, hsump]
    ring
  have hFsub : ∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2 ≤ 2 * (1 - A) := by
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun v => (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
      (Finset.subset_univ F) (fun v _ _ => sq_nonneg _)
    rw [hallsub] at hmono
    exact hmono
  have hAle : A ≤ 1 := by
    have hkey := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun v => Real.sqrt (q v)) (fun v => Real.sqrt (p v))
    have hlhs : ∑ v, Real.sqrt (q v) * Real.sqrt (p v) = A := by
      rw [hA]
      exact Finset.sum_congr rfl fun v _ => by
        rw [Real.sqrt_mul (hq v).le (p v)]
    have hsq1 : ∑ v, (Real.sqrt (q v)) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun v _ => Real.sq_sqrt (hq v).le, hsumq]
    have hsq2 : ∑ v, (Real.sqrt (p v)) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun v _ => Real.sq_sqrt (hp v).le, hsump]
    rw [hlhs, hsq1, hsq2] at hkey
    have hpos : (0:ℝ) ≤ A := hApos.le
    calc A ≤ Real.sqrt (A ^ 2) := (Real.sqrt_sq hpos).symm.le
      _ ≤ Real.sqrt (1 * 1) := Real.sqrt_le_sqrt hkey
      _ = 1 := by norm_num
  have hFadd : ∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2 ≤ 4 := by
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun v => (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)
      (Finset.subset_univ F) (fun v _ _ => sq_nonneg _)
    rw [halladd] at hmono
    have h4 : 2 * (1 + A) ≤ 4 := by linarith [hAle]
    linarith
  -- assemble: |Eq f - Ep f| ≤ δ ≤ √(2(1-A))·2 = 2√(2(1-A)) ≤ 2√KL
  have hdelta1 : ∑ v ∈ F, (q v - p v)
      ≤ 2 * Real.sqrt (2 * (1 - A)) := by
    have h1 := hcauchy
    have h2 : Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) - Real.sqrt (p v)) ^ 2)
        ≤ Real.sqrt (2 * (1 - A)) := Real.sqrt_le_sqrt hFsub
    have h3 : Real.sqrt (∑ v ∈ F, (Real.sqrt (q v) + Real.sqrt (p v)) ^ 2)
        ≤ 2 := by
      refine le_trans (Real.sqrt_le_sqrt hFadd) ?_
      norm_num
    have hprod := mul_le_mul h2 h3 (by positivity) (by positivity)
    have hkey := le_trans hcauchy hprod
    have hsplit3 : 2 * Real.sqrt (2 * (1 - A))
        = 2 * Real.sqrt (2 * (1 - A)) := rfl
    nlinarith [hkey, Real.sqrt_nonneg (2 * (1 - A))]
  -- |Δ| ≤ 2√(2(1-A)) and 2(1-A) ≤ KL: conclude |Δ| ≤ 2√KL
  rw [hdiff]
  calc abs (∑ v, (q v - p v) * f v)
      ≤ ∑ v ∈ F, (q v - p v) := habs
    _ ≤ 2 * Real.sqrt (2 * (1 - A)) := hdelta1
    _ ≤ 2 * Real.sqrt (klDef q p) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkl) (by norm_num)

/-- **Generalization = stability + information** (R376, the
sup-pair core of the Steinke–Zakynthinou CMI proof): for
distributions `q, p` (the conditional hypothesis laws on the
two selections of a sup-pair) and losses `f, g` (evaluated on
the two points, both in [0,1]), the expected swap gap obeys

  |E_q f − E_p g| ≤ E_q|f − g| + 2·√(KL(q‖p)):

the first term is the algorithmic STABILITY of the loss under
point swap, the second is the INFORMATION the hypothesis
carries about the selection — exactly the decomposition the
bounded-CMI theorem iterates over the sample. -/
theorem gen_pair_bound (q p : V → ℝ) (f g : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (hg : ∀ v, 0 ≤ g v ∧ g v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * g v)
      ≤ ∑ v, q v * abs (f v - g v) + 2 * Real.sqrt (klDef q p) := by
  -- decompose: x = (E_q f - E_q g) + (E_q g - E_p g)
  have hsplit : ∑ v, q v * f v - ∑ v, p v * g v
      = (∑ v, q v * (f v - g v)) + ((∑ v, q v * g v) - (∑ v, p v * g v)) := by
    have h1 : ∑ v, q v * (f v - g v) = ∑ v, q v * f v - ∑ v, q v * g v := by
      rw [Finset.sum_congr rfl (fun v _ => (mul_sub (q v) (f v) (g v))),
        Finset.sum_sub_distrib]
    rw [h1]
    linarith
  -- part 1: |E_q (f−g)| ≤ E_q |f−g|
  have hpart1 : abs (∑ v, q v * (f v - g v))
      ≤ ∑ v, q v * abs (f v - g v) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : ∑ v, -(q v * abs (f v - g v)) ≤ ∑ v, q v * (f v - g v) := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_abs_le _) (hq v).le
      rw [Finset.sum_neg_distrib] at h1
      exact h1
    · exact Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (le_abs_self _) (hq v).le
  -- part 2: |E_q g − E_p g| ≤ 2√KL
  have hpart2 : abs (∑ v, q v * g v - ∑ v, p v * g v)
      ≤ 2 * Real.sqrt (klDef q p) :=
    Hagi.Information.pinsker4_fin q p g hq hp hsumq hsump hg
  -- triangle assembly
  have htr : abs ((∑ v, q v * (f v - g v)) + (∑ v, q v * g v - ∑ v, p v * g v))
      ≤ abs (∑ v, q v * (f v - g v))
        + abs (∑ v, q v * g v - ∑ v, p v * g v) :=
    abs_add_le _ _
  rw [hsplit]
  exact le_trans htr (add_le_add hpart1 hpart2)

/-- **CMI iteration** (R377, final assembly of the bounded-CMI
route): given per-pair swap gaps `Δ i`, each bounded by its
stability term plus information term
(`Δ i ≤ stab i + 2√(KL i)` — the R376 sup-pair bound), the
AVERAGE gap obeys the square-root rate:

  (1/n)·Σ Δ i ≤ (1/n)·Σ stab i + 2·√((1/n)·Σ KL i).

The information terms average via Cauchy–Schwarz concavity of
√ — exactly the mechanism by which the Steinke–Zakynthinou
theorem turns bounded CMI (the average KL) into the
√(CMI/n) generalization rate. Together with R374–R376 this
completes the CMI pipeline: Hoeffding (mgf) + Pinsker (KL/TV)
+ stability-information decomposition + this iteration. -/
theorem cmi_iteration (n : ℕ) (hn : 0 < n) (stab KL Δ : Fin n → ℝ)
    (hKL : ∀ i, 0 ≤ KL i) (hst : ∀ i, 0 ≤ stab i)
    (hΔ : ∀ i, Δ i ≤ stab i + 2 * Real.sqrt (KL i)) :
    (∑ i, Δ i) / n
      ≤ (∑ i, stab i) / n + 2 * Real.sqrt ((∑ i, KL i) / n) := by
  -- step 1: sum the per-pair bounds
  have hsum : ∑ i, Δ i ≤ ∑ i, stab i + 2 * ∑ i, Real.sqrt (KL i) := by
    calc ∑ i, Δ i
        ≤ ∑ i, (stab i + 2 * Real.sqrt (KL i)) := Finset.sum_le_sum (fun i _ => hΔ i)
      _ = ∑ i, stab i + ∑ i, 2 * Real.sqrt (KL i) :=
          Finset.sum_add_distrib
      _ = ∑ i, stab i + 2 * ∑ i, Real.sqrt (KL i) := by
          rw [Finset.mul_sum]
  -- step 2: Cauchy (Σ √KL)² ≤ n · ΣKL
  have hcauchy : (∑ i, Real.sqrt (KL i)) ^ 2
      ≤ (∑ i, KL i) * n := by
    have hkey := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun i => Real.sqrt (KL i)) (fun _ => 1)
    simp only [mul_one, Real.sq_sqrt (hKL _), one_pow, pow_two,
      Finset.sum_const, Fintype.card_fin, Nat.smul_one_eq_cast] at hkey
    rw [Finset.card_univ, Fintype.card_fin] at hkey
    rw [pow_two]
    exact hkey
  -- step 3: (Σ√)/n ≤ √(ΣKL/n)
  have hn' : ((0:ℝ) < n) := by exact_mod_cast hn
  have hsumsq : (0:ℝ) ≤ ∑ i, Real.sqrt (KL i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hsumKL : (0:ℝ) ≤ ∑ i, KL i := Finset.sum_nonneg (fun i _ => hKL i)
  have hstep3 : (∑ i, Real.sqrt (KL i)) / n
      ≤ Real.sqrt ((∑ i, KL i) / n) := by
    have hle : ((∑ i, Real.sqrt (KL i)) ^ 2) / n ^ 2
        ≤ (∑ i, KL i) / n := by
      have hnn : ((∑ i, KL i) / n) * n ^ 2 = (∑ i, KL i) * n := by
        field_simp
      rw [div_le_div_iff₀ (by nlinarith [hn'] : (0:ℝ) < n ^ 2) hn']
      nlinarith [hcauchy, hnn, hn', sq_nonneg (n:ℝ)]

    calc (∑ i, Real.sqrt (KL i)) / n
        ≤ Real.sqrt (((∑ i, Real.sqrt (KL i)) / n) ^ 2) := by
          refine (Real.sqrt_sq ?_).symm.le
          exact div_nonneg hsumsq hn'.le
      _ = Real.sqrt (((∑ i, Real.sqrt (KL i)) ^ 2) / n ^ 2) := by
          rw [div_pow]
      _ ≤ Real.sqrt ((∑ i, KL i) / n) := by
          refine Real.sqrt_le_sqrt ?_
          exact hle
  -- step 4: assemble
  have hd1 : (∑ i, Δ i) / n
      ≤ ((∑ i, stab i) + 2 * ∑ i, Real.sqrt (KL i)) / n :=
    (div_le_div_iff_of_pos_right hn').mpr hsum
  have hd2 : ((∑ i, stab i) + 2 * ∑ i, Real.sqrt (KL i)) / n
      = (∑ i, stab i) / n + 2 * ((∑ i, Real.sqrt (KL i)) / n) := by
    rw [add_div, mul_div_assoc']
  refine hd1.trans ?_
  rw [hd2]
  nlinarith [hstep3]

end Hagi.Information
