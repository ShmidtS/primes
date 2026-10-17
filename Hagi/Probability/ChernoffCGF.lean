/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.PinskerTV
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

namespace Hagi.Probability


open Finset Real

open Finset Real in
/-- **ТочностьДВ
(R479)**: sup Донскера
достигается: существует f
(f := ln(p/q)), для
которой KL(p‖q) ≤
E_p f − ln(Σq·e^f)
(с R477 — эквивалентность:
KL = sup_f
(E_p f − ln E_q e^f));
Z = Σq·(p/q) =
Σp = 1 через
exp_log и field_simp. -/
theorem kl_dv_attained {V : Type*} [Fintype V] [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    ∃ f : V → ℝ,
      ∑ v : V, p v * Real.log (p v / q v)
        ≤ ∑ v : V, p v * f v
          - Real.log (∑ v : V, q v * Real.exp (f v)) := by
  refine ⟨fun v => Real.log (p v / q v), ?_⟩
  have hZ : ∑ v : V, q v * Real.exp (Real.log (p v / q v)) = (1:ℝ) := by
    have e1 : ∀ v : V,
        q v * Real.exp (Real.log (p v / q v)) = p v := by
      intro v
      rw [Real.exp_log (div_pos (hp v) (hq v))]
      field_simp [(hq v).ne']
    rw [Finset.sum_congr rfl (fun v _ => e1 v), hp1]
  rw [hZ, Real.log_one]
  have hbe : ∑ v : V, p v * (fun v => Real.log (p v / q v)) v
      = ∑ v : V, p v * Real.log (p v / q v) := rfl
  rw [hbe, sub_zero]

open Finset Real in
/-- **Hellinger-кирпичи
(R480)**: H²(p,q) :=
(1/2)·Σ(√p−√q)²
= 1 − BC — точное
тождество (квадрат
разности корней
разворачивается
в p+q−2√(pq)); с R471
— мост H² ≤ KL/2. -/
theorem hellinger_sq_eq_one_minus_bc {V : Type*} [Fintype V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      = 1 - ∑ v : V, Real.sqrt (p v) * Real.sqrt (q v) := by
  have hper : ∀ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      = p v + q v - 2 * (Real.sqrt (p v) * Real.sqrt (q v)) := by
    intro v
    rw [show (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
        = Real.sqrt (p v) ^ 2
          - 2 * (Real.sqrt (p v) * Real.sqrt (q v))
          + Real.sqrt (q v) ^ 2 from by ring,
      sq_sqrt (hp v).le, sq_sqrt (hq v).le]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hper v),
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp1, hq1]
  ring

theorem hellinger_le_half_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    (1/2) * ∑ v : V, (Real.sqrt (p v) - Real.sqrt (q v)) ^ 2
      ≤ (1/2) * ∑ v : V, p v * Real.log (p v / q v) := by
  rw [hellinger_sq_eq_one_minus_bc p q hp hp1 hq hq1]
  exact one_minus_bc_le_half_kl p q hp hp1 hq hq1

open Finset Real in
/-- **Чернофф-наклон
(R481)**: для любого c:
c·E_p g − ln E_q e^{c·g}
≤ KL(p‖q)
(инстанс R477 с
f := c·g — Cramér-
параметризация
функции моментов). -/
theorem kl_chernoff_tilt {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    c * ∑ v : V, p v * g v
      - Real.log (∑ v : V, q v * Real.exp (c * g v))
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hR := kl_variational_lower p q (fun v => c * g v) hp hp1 hq hq1
  have hconv : ∑ v : V, p v * (c * g v)
      = c * ∑ v : V, p v * g v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hconv] at hR
  exact hR

open Finset Real in
/-- **Конечный
Марков (R482)**:
для g ≥ 0 и t > 0:
t·p({g ≥ t}) ≤ E_p g
(фильтр {t ≤ g},
per-v p·t ≤ p·g,
подсумма → полная
сумма через
nonneg-расширение). -/
theorem markov_finite {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p g : V → ℝ) (t : ℝ)
    (hp : ∀ v, 0 < p v) (hg : ∀ v, 0 ≤ g v) (ht : 0 < t) :
    t * ∑ v ∈ Finset.filter (fun v => t ≤ g v) Finset.univ, p v
      ≤ ∑ v : V, p v * g v := by
  set s' : Finset V := Finset.filter (fun v => t ≤ g v) Finset.univ with hs'
  rw [Finset.mul_sum]
  have h1 : ∑ v ∈ s', t * p v ≤ ∑ v ∈ s', p v * g v := by
    apply Finset.sum_le_sum
    intro v hv
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Finset.mem_filter.mp hv).2 (le_of_lt (hp v))
  have h2 : ∑ v ∈ s', p v * g v ≤ ∑ v : V, p v * g v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun v _ _ => mul_nonneg (hp v).le (hg v))
  linarith

open Finset Real in
/-- **Чернофф
на событии
(R483)**: для λ > 0:
p({g ≥ t}) ≤
e^{−λt}·E_p e^{λg}
(марковский
R482 на
H := e^{λg}; эквивим
фильтров через
exp-монотонность). -/
theorem chernoff_event {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p g : V → ℝ) (hl t : ℝ)
    (hp : ∀ v, 0 < p v) (hltp : 0 < hl) :
    ∑ v ∈ Finset.filter (fun v => t ≤ g v) Finset.univ, p v
      ≤ (∑ v : V, p v * Real.exp (hl * g v)) / Real.exp (hl * t) := by
  set s₁ : Finset V := Finset.filter (fun v => t ≤ g v) Finset.univ with hs₁
  have hm := markov_finite p (fun v => Real.exp (hl * g v))
    (Real.exp (hl * t)) hp
    (fun v => Real.exp_nonneg _) (Real.exp_pos _)
  have hiff : ∀ v : V,
      (Real.exp (hl * g v) ≥ Real.exp (hl * t)) ↔ (t ≤ g v) := by
    intro v
    constructor
    · intro hge
      have hh := Real.exp_le_exp.mp hge
      nlinarith [hh, hltp]
    · intro hle
      exact Real.exp_le_exp.mpr (by nlinarith [hltp])
  have heq : Finset.filter (fun v =>
      Real.exp (hl * g v) ≥ Real.exp (hl * t)) Finset.univ = s₁ := by
    apply Finset.ext
    intro v
    rw [Finset.mem_filter, Finset.mem_filter, hiff v]
  rw [heq] at hm
  exact le_div_iff₀' (Real.exp_pos (hl * t)) |>.mpr hm

open Finset Real in
/-- **Экспоненциальная
интерполяция
(R484)**: для a ≤ g ≤ b:
Σp·e^{c·g} ≤
e^{ca}·Σp·w₁
+ e^{cb}·Σp·w₂,
w₁ = (b−g)/(b−a),
w₂ = (g−a)/(b−a)
— выпуклость e^
через двухточечный
АМ-ГМ (R454):
три случая (краи
аналітика +середина),
p·множение
самсого-сумы-суммой
через
mul_le_mul_of_nonneg_left. -/
theorem exp_tilt_interpol {V : Type*} [Fintype V] [Nonempty V]
    (p g : V → ℝ) (c a b : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hgb : ∀ v, g v ≤ b) (hga : ∀ v, a ≤ g v) (hxx : a < b) :
    ∑ v : V, p v * Real.exp (c * g v)
      ≤ Real.exp (c * a)
        * ∑ v : V, p v * ((b - g v) / (b - a))
        + Real.exp (c * b)
          * ∑ v : V, p v * ((g v - a) / (b - a)) := by
  have hw1 : ∀ v : V, (0:ℝ) ≤ (b - g v) / (b - a) := by
    intro v; exact div_nonneg (by linarith [hgb v]) (by linarith)
  have hw2 : ∀ v : V, (0:ℝ) ≤ (g v - a) / (b - a) := by
    intro v; exact div_nonneg (by linarith [hga v]) (by linarith)
  have hws : ∀ v : V, (b - g v) / (b - a) + (g v - a) / (b - a) = 1 := by
    intro v
    rw [← add_div, show (b - g v) + (g v - a) = (b - a) from by ring,
      div_self (by linarith)]
  have hmid : ∀ v : V, (b - g v) / (b - a) * (c * a)
      + (g v - a) / (b - a) * (c * b) = c * g v := by
    intro v
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      show (b - g v) * (c * a) + (g v - a) * (c * b)
        = c * g v * (b - a) from by ring]
    rw [mul_div_assoc (c * g v) (b - a)]
    rw [div_self (show (b - a : ℝ) ≠ 0 by linarith), mul_one]
  have hpos : ∀ v : V, (0:ℝ) < (b - g v) / (b - a) * Real.exp (c * a)
      + (g v - a) / (b - a) * Real.exp (c * b) := by
    intro v
    by_cases hlt : g v < b
    · have h1 : (0:ℝ) < (b - g v) / (b - a) :=
        div_pos (by linarith) (by linarith)
      exact lt_add_of_pos_of_le
        (mul_pos h1 (Real.exp_pos (c * a)))
        (mul_nonneg (hw2 v) (Real.exp_nonneg (c * b)))
    · have hge : g v = b := le_antisymm (hgb v) (by linarith)
      have h2 : (0:ℝ) < (g v - a) / (b - a) := by
        rw [hge]
        exact div_pos (by linarith) (by linarith)
      exact lt_add_of_le_of_pos
        (mul_nonneg (hw1 v) (Real.exp_nonneg (c * a)))
        (mul_pos h2 (Real.exp_pos (c * b)))
  have hper : ∀ v : V, Real.exp (c * g v)
      ≤ (b - g v) / (b - a) * Real.exp (c * a)
        + (g v - a) / (b - a) * Real.exp (c * b) := by
    intro v
    rcases eq_or_lt_of_le (hga v) with hga' | hgt
    · have hw1e : (b - g v) / (b - a) = (1:ℝ) := by
        rw [show (b - g v) = (b - a) from by rw [hga']]
        exact div_self (by linarith)
      have hw2e : (g v - a) / (b - a) = (0:ℝ) := by
        rw [show (g v - a) = (0:ℝ) from by rw [hga']; ring, zero_div]
      rw [hw1e, hw2e, one_mul, zero_mul, add_zero]
      exact Real.exp_le_exp.mpr (by rw [hga'])
    · rcases eq_or_lt_of_le (hgb v) with hgb' | hlt
      · have hb : (b - g v) = (0:ℝ) := by rw [hgb']; ring
        have ha2 : (g v - a) = (b - a) := by rw [hgb']
        have hw1f : (b - g v) / (b - a) = (0:ℝ) := by
          rw [hb, zero_div]
        have hw2f : (g v - a) / (b - a) = (1:ℝ) := by
          rw [ha2]
          exact div_self (ne_of_gt
            (show (0:ℝ) < b - a by linarith))
        rw [hw1f, hw2f, zero_mul, one_mul, zero_add]
        exact Real.exp_le_exp.mpr (by rw [hgb'])
      · have hw1s : (0:ℝ) < (b - g v) / (b - a) :=
          div_pos (by linarith) (by linarith)
        have hw2s : (0:ℝ) < (g v - a) / (b - a) :=
          div_pos (by linarith) (by linarith)
        have hlam2 : (b - g v) / (b - a) < 1 := by linarith [hws v]
        have hR := log_concave_two hw1s hlam2
          (Real.exp_pos (c * a)) (Real.exp_pos (c * b))
        rw [Real.log_exp (c * a), Real.log_exp (c * b)] at hR
        have hw2eq : (g v - a) / (b - a)
            = 1 - (b - g v) / (b - a) := by linarith [hws v]
        have hmid2 : (b - g v) / (b - a) * (c * a)
            + (1 - (b - g v) / (b - a)) * (c * b) = c * g v := by
          have h2 := hmid v
          rw [hw2eq] at h2
          exact h2
        rw [hmid2] at hR
        have hX := Real.exp_le_exp.mpr hR
        have hpos2 : (0:ℝ) < (b - g v) / (b - a) * Real.exp (c * a)
            + (1 - (b - g v) / (b - a)) * Real.exp (c * b) := by
          rw [← hw2eq]
          exact hpos v
        rw [Real.exp_log hpos2, ← hw2eq] at hX
        exact hX
  refine le_trans (Finset.sum_le_sum (fun v _ =>
    mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hp v)))) ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  exact le_of_eq (by ring)

open Finset Real in
/-- **Cramér-наклон
(R485)**: если E_p g ≥ t,
то для любого
c > 0: c·t −
ln Σq·e^{c·g} ≤
KL(p‖q).
Опора arXiv 2401.01148
(PAC-Bayes-Chernoff,
NeurIPS 2024) — первый
кирпич вертикали. -/
theorem cramer_tilt_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hc : 0 < c) (hge : t ≤ ∑ v : V, p v * g v) :
    c * t - Real.log (∑ v : V, q v * Real.exp (c * g v))
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hR := kl_chernoff_tilt p q g c hp hp1 hq hq1
  have hmono : c * t ≤ c * ∑ v : V, p v * g v :=
    mul_le_mul_of_nonneg_left hge hc.le
  linarith [hR, hmono]

open Finset Real in
/-- **Cramér-sup (R486)**: при E_p g ≥ t:
sSup по c > 0
функционала c·t −
ln Σq·e^{c·g}
≤ KL(p‖q)
(вертикаль arXiv
2401.01148, кирпич 2;
САВ (sup + bound) = Cramér-оболочка). -/
theorem cramer_sup_le_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hge : t ≤ ∑ v : V, p v * g v) :
    sSup {x : ℝ | ∃ c > 0, x = c * t
      - Real.log (∑ v : V, q v * Real.exp (c * g v))}
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  apply csSup_le
  · exact ⟨1 * t - Real.log (∑ v : V, q v * Real.exp (1 * g v)),
      ⟨(1:ℝ), by norm_num, rfl⟩⟩
  · intro x hx
    rcases hx with ⟨c, hc, hxe⟩
    refine hxe ▸ cramer_tilt_kl p q g t c hp hp1 hq hq1 hc ?_
    exact hge

open Finset Real in
/-- **CGF-форма
Cramér (R487)**: если
ln Σq·e^{c(g−μ)} ≤ ψ(c)
и E_p g ≥ t, то
c·(t−μ) − ψ(c) ≤
KL(p‖q) для любого
c > 0 — кирпич CGF-вертикали
(2401.01148 /
JMLR 23-1360: параметр-свободная
CGF-оболочка). -/
theorem cramer_cgf {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (t μ : ℝ) (ψ : ℝ → ℝ) (c : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hc : 0 < c) (hge : t ≤ ∑ v : V, p v * g v)
    (hcgf : Real.log (∑ v : V, q v * Real.exp (c * (g v - μ))) ≤ ψ c) :
    c * (t - μ) - ψ c ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  have hper : ∀ v : V, q v * Real.exp (c * g v)
      = Real.exp (c * μ) * (q v * Real.exp (c * (g v - μ))) := by
    intro v
    have h1 : c * g v = c * (g v - μ) + c * μ := by ring
    rw [h1, Real.exp_add]
    ring
  have hsplit : ∑ v : V, q v * Real.exp (c * g v)
      = Real.exp (c * μ) * ∑ v : V,
          q v * Real.exp (c * (g v - μ)) := by
    rw [Finset.sum_congr rfl (fun v _ => hper v), ← Finset.mul_sum]
  have hpos : (0:ℝ) < ∑ v : V, q v * Real.exp (c * (g v - μ)) :=
    Finset.sum_pos (fun v _ => mul_pos (hq v)
      (Real.exp_pos _)) ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hR := cramer_tilt_kl p q g t c hp hp1 hq hq1 hc hge
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne'
    hpos.ne'] at hR
  rw [Real.log_exp (c * μ)] at hR
  linarith [hR, hcgf]

open Finset Real in
/-- **Sub-Gaussian
измерение
(R488)**: при CGF-границе
ln Σq·e^{c(g−μ)} ≤
c²σ²/2 и μ ≤ E_p g:
(E_p g − μ)²/(2σ²) ≤
KL(p‖q) — λ*подстановка
λ = (E_p g − μ)/σ² в R487
без дифференциального
исчисления (оптимум
Cramér-функционала). -/
theorem subgauss_dev_kl {V : Type*} [Fintype V] [Nonempty V]
    (p q g : V → ℝ) (μ σ2 : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hs2 : 0 < σ2) (hm : μ ≤ ∑ v : V, p v * g v)
    (hcgf : ∀ c : ℝ, 0 < c →
      Real.log (∑ v : V, q v * Real.exp (c * (g v - μ)))
        ≤ c ^ 2 * σ2 / 2) :
    ((∑ v : V, p v * g v) - μ) ^ 2 / (2 * σ2)
      ≤ ∑ v : V, p v * Real.log (p v / q v) := by
  set T := ∑ v : V, p v * g v with hT
  rcases eq_or_lt_of_le hm with hhe | hlt
  · rw [← hhe]
    have hkl := finite_kl_nonneg p q hp hp1 hq hq1
    simpa using hkl
  · have hc : (0:ℝ) < (T - μ) / σ2 := div_pos (by linarith) hs2
    have hR := cramer_cgf p q g T μ (fun x => x ^ 2 * σ2 / 2)
      ((T - μ) / σ2) hp hp1 hq hq1 hc (by linarith)
      (hcgf _ hc)
    have hval : (T - μ) / σ2 * (T - μ)
        - ((T - μ) / σ2) ^ 2 * σ2 / 2
        = (T - μ) ^ 2 / (2 * σ2) := by
      field_simp
      ring
    rw [hval] at hR
    exact hR

open Finset Real in
/-- **Сдвиг-среднего
~ TV (R489)**: при
a ≤ g ≤ b:
|E_p g − E_q g| ≤
(b−a)·TV(p,q).
Механика: нормировка
f = (g−a)/(b−a) —
дуальность R473 +
центрировка μ-сдвига
(=с линейным
мостом Δ = d·F
через
partition sum_div). -/
theorem mean_shift_tv {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (p q g : V → ℝ) (a b : ℝ)
    (hp : ∀ v, 0 < p v) (hp1 : ∑ v : V, p v = 1)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (hab : a < b) :
    |∑ v : V, p v * g v - ∑ v : V, q v * g v|
      ≤ (b - a) * ((1/2) * ∑ v : V, |p v - q v|) := by
  have hD : (0:ℝ) < b - a := by linarith
  have hf0 : ∀ v, 0 ≤ (g v - a) / (b - a) :=
    fun v => div_nonneg (by linarith [hlo v]) hD.le
  have hf1 : ∀ v, (g v - a) / (b - a) ≤ 1 := by
    intro v
    rw [div_le_one hD]
    linarith [hhi v]
  set Δ := ∑ v : V, p v * g v - ∑ v : V, q v * g v with hΔ
  set F := ∑ v : V, p v * ((g v - a) / (b - a))
    - ∑ v : V, q v * ((g v - a) / (b - a)) with hF
  have hΔF : Δ = (b - a) * F := by
    have hEp : ∑ v : V, p v * ((g v - a) / (b - a))
        = (∑ v : V, p v * (g v - a)) / (b - a) := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_div_assoc' (p v) _ _), Finset.sum_div]
    have hEq : ∑ v : V, q v * ((g v - a) / (b - a))
        = (∑ v : V, q v * (g v - a)) / (b - a) := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_div_assoc' (q v) _ _), Finset.sum_div]
    have hbn : ∑ v : V, p v * (g v - a)
        = ∑ v : V, p v * g v - a := by
      have h2 : ∑ v : V, p v * (g v - a)
          = ∑ v : V, p v * g v - ∑ v : V, p v * a := by
        rw [Finset.sum_congr rfl (fun v _ => by rw [mul_sub]),
          Finset.sum_sub_distrib]
      rw [h2]
      have h3 : ∑ v : V, p v * a = a := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (p v) a),
          ← Finset.mul_sum, hp1, mul_one]
      rw [h3]
    have hqn : ∑ v : V, q v * (g v - a)
        = ∑ v : V, q v * g v - a := by
      have h2 : ∑ v : V, q v * (g v - a)
          = ∑ v : V, q v * g v - ∑ v : V, q v * a := by
        rw [Finset.sum_congr rfl (fun v _ => by rw [mul_sub]),
          Finset.sum_sub_distrib]
      rw [h2]
      have h3 : ∑ v : V, q v * a = a := by
        rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a),
          ← Finset.mul_sum, hq1, mul_one]
      rw [h3]
    rw [hΔ, hF, hEp, hEq, hbn, hqn, div_sub_div_same]
    rw [show (∑ v : V, p v * g v - a) - (∑ v : V, q v * g v - a)
        = ∑ v : V, p v * g v - ∑ v : V, q v * g v from by ring]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hD)]
  have hf0 : ∀ v, 0 ≤ (g v - a) / (b - a) :=
    fun v => div_nonneg (by linarith [hlo v]) hD.le
  have hf1 : ∀ v, (g v - a) / (b - a) ≤ 1 := by
    intro v
    rw [div_le_one hD]
    linarith [hhi v]
  have hdual := tv_dual_abs p q (fun v => (g v - a) / (b - a))
    hp hp1 hq hq1 hf0 hf1
  rw [hΔF, abs_mul, abs_of_pos hD]
  exact mul_le_mul_of_nonneg_left hdual hD.le

open Finset Real in
/-- **Центрирование
CGF (R490)**: ln Σq·e^{c·g}
= c·μ +
ln Σq·e^{c(g−μ)} —
standalone-лемма
(выделена из R487 по
Rule-of-Three: центр-мост
дублировался). -/
theorem cgf_centering {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (μ c : ℝ)
    (hq : ∀ v, 0 < q v) :
    Real.log (∑ v : V, q v * Real.exp (c * g v))
      = c * μ + Real.log (∑ v : V,
          q v * Real.exp (c * (g v - μ))) := by
  have hper : ∀ v : V, q v * Real.exp (c * g v)
      = Real.exp (c * μ) * (q v * Real.exp (c * (g v - μ))) := by
    intro v
    have h1 : c * g v = c * (g v - μ) + c * μ := by ring
    rw [h1, Real.exp_add]
    ring
  have hpos : (0:ℝ) < ∑ v : V, q v * Real.exp (c * (g v - μ)) :=
    Finset.sum_pos (fun v _ => mul_pos (hq v)
      (Real.exp_pos _)) ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  rw [Finset.sum_congr rfl (fun v _ => hper v), ← Finset.mul_sum,
    Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp (c * μ)]

open Finset Real in
/-- **Чернов-subG-хвост
(R491)**: при CGF-границе
ln Σq·e^{c(g−μ)} ≤ c²σ²/2:
q({g ≥ μ+u}) ≤
e^{−u²/(2σ²)} (λ = u/σ²;
R483 + R490-центринг
+ exp_sub-RHS-переупаковка;
h2.le-связка). -/
theorem chernoff_subgauss_tail {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (q g : V → ℝ) (μ σ2 u : ℝ)
    (hq : ∀ v, 0 < q v) (hs2 : 0 < σ2) (hu : 0 < u)
    (hcgf : ∀ c : ℝ, 0 < c →
      Real.log (∑ v : V, q v * Real.exp (c * (g v - μ)))
        ≤ c ^ 2 * σ2 / 2) :
    ∑ v ∈ Finset.filter (fun v => μ + u ≤ g v) Finset.univ, q v
      ≤ Real.exp (-(u ^ 2) / (2 * σ2)) := by
  have lam0 : (0:ℝ) < u / σ2 := div_pos hu hs2
  have hq' := chernoff_event q g (u / σ2) (μ + u) hq lam0
  -- CGF upper at lam = u/σ2 after centering
  have hC := hcgf (u / σ2) lam0
  have hZ2 : Real.log (∑ v : V, q v * Real.exp ((u / σ2) * g v))
      ≤ (u / σ2) * μ + (u / σ2) ^ 2 * σ2 / 2 :=
    (le_of_eq (cgf_centering q g μ (u / σ2) hq)).trans
      (by linarith [hC])
  -- exponent arithmetic: λμ + λ²σ2/2 − λ(μ+u) = −u²/(2σ2)
  have hex : (u / σ2) * μ + (u / σ2) ^ 2 * σ2 / 2
      - (u / σ2) * (μ + u) = -(u ^ 2) / (2 * σ2) := by
    field_simp
    ring
  -- hq' div-form: Σ_s q ≤ (Σ q e^{λg}) / e^{λ(μ+u)}, with
  -- Σ q e^{λg} ≤ e^{λμ+λ²σ2/2} (from exp_le_exp.mpr hZ2)
  have h1 : (∑ v : V, q v * Real.exp ((u / σ2) * g v))
      / Real.exp ((u / σ2) * (μ + u))
      ≤ Real.exp ((u / σ2) * μ + (u / σ2) ^ 2 * σ2 / 2)
        / Real.exp ((u / σ2) * (μ + u)) :=
    (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr
      (by
        have hL : Real.exp (Real.log (∑ v : V,
            q v * Real.exp ((u / σ2) * g v)))
          = ∑ v : V, q v * Real.exp ((u / σ2) * g v) :=
            Real.exp_log (Finset.sum_pos (fun v _ =>
              mul_pos (hq v) (Real.exp_pos _))
              ⟨Classical.arbitrary V, Finset.mem_univ _⟩)
        rw [← hL]
        exact exp_le_exp.mpr hZ2)
  have h2 : Real.exp ((u / σ2) * μ + (u / σ2) ^ 2 * σ2 / 2)
        / Real.exp ((u / σ2) * (μ + u))
      = Real.exp (-(u ^ 2) / (2 * σ2)) := by
    rw [← Real.exp_sub, hex]
  exact le_trans hq' (le_trans h1 h2.le)

/-- Дополнение хвоста: мера {g < t} = 1 − мера{g ≥ t} для
вероятностных весов q. -/
theorem tail_complement {V : Type*} [Fintype V] [DecidableEq V]
    (q g : V → ℝ) (t : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1) :
    ∑ v ∈ Finset.filter (fun v => g v < t) Finset.univ, q v
      + ∑ v ∈ Finset.filter (fun v => t ≤ g v) Finset.univ, q v = 1 := by
  classical
  set A : Finset V := Finset.filter (fun v => g v < t) Finset.univ with hA
  set B : Finset V := Finset.filter (fun v => t ≤ g v) Finset.univ with hB
  have hd : A ∩ B = ∅ := by
    ext v
    simp [Finset.mem_inter, hA, hB, Finset.mem_filter, Finset.mem_univ]
  have hun : A ∪ B = Finset.univ := by
    ext v
    simp only [Finset.mem_union, hA, hB, Finset.mem_filter, Finset.mem_univ,
      true_and]
    cases lt_or_ge (g v) t <;> simp [*]
  have hunion : ∑ v ∈ A ∪ B, q v
      = ∑ v ∈ A, q v + ∑ v ∈ B, q v := by
    have hi := Finset.sum_union_inter (f := q) (s₁ := A) (s₂ := B)
    rw [hd] at hi
    simp at hi
    exact hi
  have hfull : ∑ v : V, q v = ∑ v ∈ A ∪ B, q v := by rw [hun]
  rw [hfull] at hq1
  linarith

end Hagi.Probability

export Hagi.Probability (cgf_centering chernoff_event chernoff_subgauss_tail cramer_cgf cramer_sup_le_kl cramer_tilt_kl exp_tilt_interpol hellinger_le_half_kl hellinger_sq_eq_one_minus_bc kl_chernoff_tilt kl_dv_attained markov_finite mean_shift_tv subgauss_dev_kl tail_complement)
