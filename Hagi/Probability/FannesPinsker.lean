/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.GibbsCore
import Hagi.Probability.GibbsCooling

set_option linter.style.header false

/-!
# FannesPinsker — consolidated Fannes + Pinsker canon (A5 §R3, C235)

Merge of `Hagi.Unified.FannesComplete` (discrete Fannes, mixed-entropy
bounds; namespace `Hagi.Unified` preserved), `Hagi.Unified.InfoCanonical`
(entDef/tvDef-world bridges), `Hagi.Unified.NernstFannes` (Nernst via
Fannes), and `Hagi.Probability.PinskerTV` (Pinsker family; namespaces
`Hagi.Probability` and tail `Hagi.Information` preserved). FQNs of all
moved declarations preserved via namespace blocks (C234 pattern);
statements byte-identical. Definitions live in `Hagi.Prelude.InfoCore`.
-/

/-!
# Полная Fannes-граница без моста (R532)

Закрытие открытого пункта STATUS «полная Fannes-граница»:
безусловная дискретная refined-Fannes для весовых векторов,
без hbridge-гипотезы (entropy диагонали = Shannon —
сортированные корни диагонали отсутствуют в Mathlib v4.34.1).

Ядро — чисто вещественная KL-иерархия:

* `nml_mul` — расщепление negMulLog(c·x);
* `xlogx_superadd` — супераддитивность x·log x (Дженсен
  против нуля = монотонность логарифма);
* `mix_point` — поэлементная верхняя оценка смеси;
* `mix_entropy_upper` — H(aq+bû) ≤ aH(q)+bH(û)+h₂(b);
* `zs_kl` — zero-safe KL ≥ 0 (носитель-сужение
  log_sum_ineq_on);
* `mix_entropy_lower` — вогнутость aH(q)+bH(û) ≤ H(aq+bû);
* `shannon_le_log_card` — H ≤ log d (KL с uniform);
* `fannes_unconditional` — ГЛАВНАЯ: H(p)−H(q) ≤ t·log d +
  (1+t)·h₂(t/(1+t)), t = Hagi.Information.tvHalf p q.
-/

namespace Hagi.Unified

open Real Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zs_kl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ι → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hA1 : ∑ i, A i = 1) (hB1 : ∑ i, B i ≤ 1)
    (hsupp : ∀ i, 0 < A i → 0 < B i) :
    0 ≤ ∑ i, A i * Real.log (A i / B i) := by
  classical
  set S : Finset ι := Finset.filter (fun i => 0 < A i) Finset.univ with hSdef
  have hAz : ∀ i, i ∉ S → A i = 0 := by
    intro i hi
    by_contra hne
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      lt_of_le_of_ne (hA i) (Ne.symm hne)⟩)
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hz : ∑ i, A i = 0 :=
      Finset.sum_eq_zero (fun i _ => hAz i (fun hmem =>
        absurd hmem (by rw [hempty]; simp)))
    linarith
  have hha : ∀ i ∈ S, 0 < A i := fun i hi => Finset.mem_filter.mp hi |>.2
  have hhb : ∀ i ∈ S, 0 < B i := fun i hi => hsupp i (hha i hi)
  have key : ∀ (f : ι → ℝ), (∀ i, i ∉ S → f i = 0) → ∑ i, f i = ∑ i ∈ S, f i :=
    fun f hf => (Finset.sum_subset S.subset_univ
      (fun i _ hi => hf i hi)).symm
  have hsumA : ∑ i ∈ S, A i = 1 := by rw [← key A (fun i hi => hAz i hi)]; exact hA1
  -- ∑_S B ≤ 1
  have hsumB : ∑ i ∈ S, B i ≤ 1 := by
    have hkey2 : ∑ i ∈ S, (fun i => if i ∈ S then B i else 0) i
        = ∑ i ∈ Finset.univ, (fun i => if i ∈ S then B i else 0) i :=
      Finset.sum_subset S.subset_univ (fun i _ hi => by simp [hi])
    have hSS : ∑ i ∈ S, (fun i => if i ∈ S then B i else 0) i = ∑ i ∈ S, B i :=
      Finset.sum_congr rfl (fun i hi => by simp [hi])
    have hle : ∀ i ∈ Finset.univ,
        (fun i => if i ∈ S then B i else 0) i ≤ B i := by
      intro i _
      simp only []
      by_cases hi : i ∈ S
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact hB i
    have htot : ∑ i ∈ Finset.univ, (fun i => if i ∈ S then B i else 0) i
        ≤ ∑ i ∈ Finset.univ, B i := Finset.sum_le_sum hle
    rw [← hkey2, hSS] at htot
    simpa using htot.trans hB1
  have hsplit : ∑ i, A i * Real.log (A i / B i)
      = ∑ i ∈ S, A i * Real.log (A i / B i) :=
    key _ (fun i hi => by rw [hAz i hi, zero_mul])
  have hSne2 := hSne
  obtain ⟨j, hj⟩ := hSne2
  have hposB : 0 < ∑ i ∈ S, B i := by
    have h1 : (0:ℝ) < B j := hhb j hj
    have h2 : B j ≤ ∑ i ∈ S, B i :=
      Finset.single_le_sum (f := B) (fun i _ => hB i) hj
    linarith
  rw [hsplit]
  have hli := log_sum_ineq_on S hSne A B hha hhb
  rw [hsumA] at hli
  have hlog : 0 ≤ Real.log (1 / (∑ i ∈ S, B i)) := by
    apply Real.log_nonneg
    rw [one_le_div_iff]
    exact Or.inl ⟨hposB, hsumB⟩
  have hone : (1:ℝ) * Real.log (1 / ∑ i ∈ S, B i)
      = Real.log (1 / ∑ i ∈ S, B i) := by ring
  rw [hone] at hli
  linarith


lemma nml_mul (c x : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    Real.negMulLog (c * x) = c * Real.negMulLog x + x * Real.negMulLog c := by
  by_cases hc0 : c = 0
  · simp [hc0, Real.negMulLog]
  by_cases hx0 : x = 0
  · simp [hx0, Real.negMulLog]
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hlog : Real.log (c * x) = Real.log c + Real.log x :=
    Real.log_mul hcpos.ne' hxpos.ne'
  unfold Real.negMulLog
  rw [hlog]
  ring_nf

-- superadditivity of x·log x (Jensen against 0 = log monotonicity)
lemma xlogx_superadd (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * Real.log s + t * Real.log t ≤ (s + t) * Real.log (s + t) := by
  have hkey : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x * Real.log x ≤ x * Real.log (x + y) := by
    intro x y hx hy
    by_cases hx0 : x = 0
    · rw [hx0, zero_mul, zero_mul]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hle : Real.log x ≤ Real.log (x + y) :=
        Real.log_le_log hxpos (by linarith)
      exact mul_le_mul_of_nonneg_left hle hx
  have h1 := hkey s t hs ht
  have h2 := hkey t s ht hs
  have hring : s * Real.log (s + t) + t * Real.log (t + s)
      = (s + t) * Real.log (s + t) := by
    rw [add_comm t s]
    ring
  linarith

open Finset
-- elementwise upper: negMulLog(ax+by) ≤ a·negMulLog x + b·negMulLog y + x·negMulLog a + y·negMulLog b
lemma mix_point (x y a b : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a * x + b * y)
      ≤ a * Real.negMulLog x + b * Real.negMulLog y
        + x * Real.negMulLog a + y * Real.negMulLog b := by
  have h1 := xlogx_superadd (a * x) (b * y) (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hnp : ∀ z : ℝ, z * Real.log z = -(Real.negMulLog z) := by
    intro z; unfold Real.negMulLog; ring
  rw [hnp, hnp, hnp] at h1
  -- LHS: (ax+by)·log(ax+by) = -negMulLog(ax+by) — expand the two summands
  rw [nml_mul a x ha hx, nml_mul b y hb hy] at h1
  linarith

-- summation: H(aq+bû) ≤ aH(q)+bH(û)+negMulLog a+negMulLog b = ...+h₂(b)
theorem mix_entropy_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q u : ι → ℝ) (a b : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hu : ∀ i, 0 ≤ u i)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hq1 : ∑ i, q i = 1) (hu1 : ∑ i, u i = 1) :
    ∑ i, Real.negMulLog (a * q i + b * u i)
      ≤ a * ∑ i, Real.negMulLog (q i)
        + b * ∑ i, Real.negMulLog (u i)
        + Real.binEntropy b := by
  have hsum : ∑ i, (Real.negMulLog (a * q i + b * u i))
      ≤ ∑ i, (a * Real.negMulLog (q i) + b * Real.negMulLog (u i)
        + q i * Real.negMulLog a + u i * Real.negMulLog b) :=
    Finset.sum_le_sum (fun i _ =>
      mix_point (q i) (u i) a b (hq i) (hu i) ha hb)
  -- distribute the four sums
  have hs1 : ∑ i, a * Real.negMulLog (q i) = a * ∑ i, Real.negMulLog (q i) :=
    (Finset.mul_sum Finset.univ (fun i => Real.negMulLog (q i)) a).symm
  have hs2 : ∑ i, b * Real.negMulLog (u i) = b * ∑ i, Real.negMulLog (u i) :=
    (Finset.mul_sum Finset.univ (fun i => Real.negMulLog (u i)) b).symm
  have hs3 : ∑ i, q i * Real.negMulLog a = Real.negMulLog a := by
    rw [← Finset.sum_mul, hq1, one_mul]
  have hs4 : ∑ i, u i * Real.negMulLog b = Real.negMulLog b := by
    rw [← Finset.sum_mul, hu1, one_mul]
  -- combine
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have heq : ∑ i, a * Real.negMulLog (q i) + ∑ i, b * Real.negMulLog (u i)
      + Real.negMulLog a + Real.negMulLog b
      = a * ∑ i, Real.negMulLog (q i) + b * ∑ i, Real.negMulLog (u i)
        + Real.negMulLog a + Real.negMulLog b := by
    rw [hs1, hs2]
  -- binEntropy b = negMulLog b + negMulLog (1-b), 1-b = a
  have hbE : Real.binEntropy b
      = Real.negMulLog b + Real.negMulLog a := by
    have hba : 1 - b = a := by linarith
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hba]
  rw [hbE]
  linarith [hsum, heq]


/-- **Вогнутость (нижняя оценка смеси, R532)**:
aH(q)+bH(û) ≤ H(aq+bû) для весов и вероятностных векторов. -/
theorem mix_entropy_lower (q u : ι → ℝ) (a b : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hu : ∀ i, 0 ≤ u i)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * ∑ i, Real.negMulLog (q i) + b * ∑ i, Real.negMulLog (u i)
      ≤ ∑ i, Real.negMulLog (a * q i + b * u i) := by
  have hpoint : ∀ i : ι, a * Real.negMulLog (q i) + b * Real.negMulLog (u i)
      ≤ Real.negMulLog (a * q i + b * u i) := by
    intro i
    have h := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset (Fin 2)))
      (w := ![a, b]) (p := ![q i, u i])
      (fun j _ => by
        fin_cases j
        · exact ha
        · exact hb)
      (by
        show (∑ j : Fin 2, (![a, b] : Fin 2 → ℝ) j) = 1
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith)
      (fun j _ => by
        fin_cases j
        · exact hq i
        · exact hu i)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul] at h
    exact h
  have hsum : a * ∑ i, Real.negMulLog (q i) + b * ∑ i, Real.negMulLog (u i)
      = ∑ i, (a * Real.negMulLog (q i) + b * Real.negMulLog (u i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hsum]
  exact Finset.sum_le_sum (fun i _ => hpoint i)

/-- **H ≤ log d (R532)**: энтропия вероятностного вектора на
носителе из d точек не превосходит log d (zero-safe KL с
uniform). -/
theorem shannon_le_log_card (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i)
      ≤ Real.log (Fintype.card ι) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc0 | hcpos
  · -- пустой носитель: Σp = 1 невозможно, противоречие
    exfalso
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc0
    have h0 : ∑ i, p i = 0 := by
      simp [Finset.univ_eq_empty_iff]
    linarith
  · letI : Nonempty ι := Fintype.card_pos_iff.mp hcpos
    exact Hagi.Prelude.sum_negMulLog_le_log_card p hp hp1

/-- **Полная Fannes без моста (R532, ГЛАВНАЯ)**: для весовых
векторов p, q ≥ 0 с Σ = 1 каждый и t = ½‖p−q‖₁:
H(p) − H(q) ≤ t·log d + (1+t)·h₂(t/(1+t)). -/
theorem fanes_unconditional
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    Hagi.Information.shannon p - Hagi.Information.shannon q ≤
      (Hagi.Information.tvHalf p q) * Real.log (Fintype.card ι : ℝ)
      + (1 + Hagi.Information.tvHalf p q)
        * Real.binEntropy (Hagi.Information.tvHalf p q
          / (1 + Hagi.Information.tvHalf p q)) := by
  classical
  set r := Hagi.Information.posPart p q with hr
  set s := Hagi.Information.negPart p q with hs
  have hsums := Hagi.Information.pos_neg_sums p q hps hqs
  -- t = Σr = Σs = tvHalf
  have habs : (∑ i, r i) + (∑ i, s i) = ∑ i, |p i - q i| := hsums.2
  have ht : Hagi.Information.tvHalf p q = ∑ i, r i := by
    unfold Hagi.Information.tvHalf
    have := hsums.1
    linarith [habs]
  -- разбор вырожденного случая p = q
  rcases eq_or_ne (∑ i, |p i - q i|) 0 with hzero | hposL1
  · -- p = q: цель 0 ≤ 0 + 1·h₂(0) = 0
    have hpq : ∀ i, p i = q i := by
      intro i
      by_contra hne
      have hgt : 0 < |p i - q i| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have hle : |p i - q i| ≤ ∑ j, |p j - q j| :=
        Finset.single_le_sum (f := fun j => |p j - q j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
    have hsh : Hagi.Information.shannon p = Hagi.Information.shannon q := by
      unfold Hagi.Information.shannon
      exact Finset.sum_congr rfl (fun i _ => by rw [hpq i])
    rw [hsh, sub_self]
    have htv : Hagi.Information.tvHalf p q = 0 := by
      unfold Hagi.Information.tvHalf
      rw [hzero, zero_div]
    rw [htv]
    norm_num
  -- основная ветка: t > 0
  have htpos : 0 < ∑ i, r i := by
    have h2 : ∑ i, |p i - q i| = (∑ i, r i) + (∑ i, s i) := habs.symm
    rcases lt_trichotomy (0:ℝ) (∑ i, r i) with h | h | h
    · exact h
    · have hs0 : ∑ i, s i = 0 := by linarith [hsums.1, h]
      have hzz : ∑ i, |p i - q i| = 0 := by linarith [h2, h, hs0]
      exact absurd hzz hposL1
    · have hs_lt : ∑ i, s i < 0 := by linarith [hsums.1, h]
      have hs_nn : 0 ≤ ∑ i, s i :=
        Finset.sum_nonneg (fun i _ => Hagi.Information.negPart_nonneg p q i)
      linarith
  -- нормированные векторы: û = r/t, v̂ = s/t
  set u : ι → ℝ := fun i => (∑ i, r i)⁻¹ * r i with hu
  set v : ι → ℝ := fun i => (∑ i, s i)⁻¹ * s i with hv
  have hs_pos : 0 < ∑ i, s i := by rw [← hsums.1]; exact htpos
  have hu_nneg : ∀ i, 0 ≤ u i := by
    intro i; exact mul_nonneg (inv_nonneg.mpr htpos.le) (Hagi.Information.posPart_nonneg p q i)
  have hv_nneg : ∀ i, 0 ≤ v i := by
    intro i; exact mul_nonneg (inv_nonneg.mpr hs_pos.le) (Hagi.Information.negPart_nonneg p q i)
  have hu1 : ∑ i, u i = 1 := by
    show ∑ i, (∑ j, r j)⁻¹ * r i = 1
    rw [← Finset.mul_sum, inv_mul_cancel₀ (ne_of_gt htpos)]

  have hv_le_one : ∀ i, v i ≤ 1 := by
    intro i
    have hle : s i ≤ ∑ j, s j :=
      Finset.single_le_sum (f := s) (fun j _ => Hagi.Information.negPart_nonneg p q j)
        (Finset.mem_univ i)
    rw [hv, inv_mul_le_one₀ hs_pos]
    exact hle
  have hv1 : ∑ i, v i = 1 := by
    show ∑ i, (∑ j, s j)⁻¹ * s i = 1
    rw [← Finset.mul_sum, inv_mul_cancel₀ (ne_of_gt hs_pos)]
  -- смесевые параметры
  set t : ℝ := ∑ i, r i with htdef
  set a : ℝ := 1 / (1 + t) with ha
  set b : ℝ := t / (1 + t) with hb
  have h1t : 0 < 1 + t := by positivity
  have hab : a + b = 1 := by
    rw [ha, hb]
    field_simp
  -- w-тождество: a*q + b*v = (q+s)/(1+t) = (p+r)/(1+t) = a*p + b*u
  have hts : t = ∑ i, s i := htdef.trans hsums.1
  have hwq : ∀ i, a * q i + b * u i = (q i + r i) / (1 + t) := by
    intro i
    show (1/(1+t)) * q i + (t/(1+t)) * ((∑ j, r j)⁻¹ * r i) = (q i + r i) / (1 + t)
    have hkey : t * ((∑ j, r j)⁻¹ * r i) = r i := by
      rw [htdef, mul_inv_cancel_left₀ (ne_of_gt htpos)]
    have hsplit : (t/(1+t)) * ((∑ j, r j)⁻¹ * r i)
        = (1/(1+t)) * (t * ((∑ j, r j)⁻¹ * r i)) := by field_simp
    rw [hsplit, hkey]
    field_simp
  have hwp : ∀ i, a * p i + b * v i = (p i + s i) / (1 + t) := by
    intro i
    show (1/(1+t)) * p i + (t/(1+t)) * ((∑ j, s j)⁻¹ * s i) = (p i + s i) / (1 + t)
    have hkey : t * ((∑ j, s j)⁻¹ * s i) = s i := by
      rw [hts, mul_inv_cancel_left₀ (ne_of_gt hs_pos)]
    have hsplit : (t/(1+t)) * ((∑ j, s j)⁻¹ * s i)
        = (1/(1+t)) * (t * ((∑ j, s j)⁻¹ * s i)) := by field_simp
    rw [hsplit, hkey]
    field_simp
  have hsame : ∀ i, (q i + r i) / (1 + t) = (p i + s i) / (1 + t) := by
    intro i
    have h : p i + s i = q i + r i :=
      Hagi.Information.posPart_negPart_pointwise p q i
    rw [div_eq_div_iff (ne_of_gt h1t) (ne_of_gt h1t)]
    nlinarith [h]
  -- вогнутость (нижняя): a·H(p) + b·H(u) ≤ H(w), w = a·p + b·u
  set w : ι → ℝ := fun i => a * p i + b * u i with hwdef
  have hlower := mix_entropy_lower p v a b hp hv_nneg
    (by rw [ha]; exact div_nonneg (by norm_num : (0:ℝ) ≤ 1) h1t.le)
    (by rw [hb]; exact div_nonneg htpos.le h1t.le) hab
  -- верх: H(w') ≤ a·H(q) + b·H(v) + h₂(b), w' = a·q + b·v
  have hupper := mix_entropy_upper q u a b hq hu_nneg
    (by rw [ha]; exact div_nonneg (by norm_num : (0:ℝ) ≤ 1) h1t.le)
    (by rw [hb]; exact div_nonneg htpos.le h1t.le) hab hqs hu1
  -- H(w) = H(w') поэлементно
  have hw_eq : ∀ i, a * p i + b * v i = a * q i + b * u i := by
    intro i
    rw [hwp i, hwq i]
    exact (hsame i).symm
  have hsum_eq : ∑ i, Real.negMulLog (a * p i + b * v i)
      = ∑ i, Real.negMulLog (a * q i + b * u i) :=
    Finset.sum_congr rfl (fun i _ => by rw [hw_eq i])
  rw [hsum_eq] at hlower
  -- H(u) ≥ 0 и H(v) ≤ log d
  have hHu_le : ∑ i, Real.negMulLog (u i) ≤ Real.log (Fintype.card ι : ℝ) :=
    shannon_le_log_card u hu_nneg hu1
  have hHv_ge : 0 ≤ ∑ i, Real.negMulLog (v i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Real.negMulLog_nonneg
    · exact hv_nneg i
    · exact hv_le_one i
  -- цепочка: a·H(p) + b·H(v) ≤ a·H(q) + b·H(u) + h₂(b)
  -- ⟹ a(H(p) − H(q)) ≤ b(H(v) − H(u)) + h₂(b) ≤ b·log d + h₂(b)
  have hchain : a * (∑ i, Real.negMulLog (p i))
      ≤ a * (∑ i, Real.negMulLog (q i)) + b * Real.log (Fintype.card ι : ℝ)
        + Real.binEntropy b := by
    have h1 : a * ∑ i, Real.negMulLog (p i) + b * ∑ i, Real.negMulLog (v i)
        ≤ a * ∑ i, Real.negMulLog (q i) + b * ∑ i, Real.negMulLog (u i)
          + Real.binEntropy b := by
      have hlow2 : a * ∑ i, Real.negMulLog (p i) + b * ∑ i, Real.negMulLog (v i)
          ≤ ∑ i, Real.negMulLog (a * q i + b * u i) := hlower
      exact le_trans hlow2 hupper
    have hbnng : 0 ≤ b * ∑ i, Real.negMulLog (v i) := by
      have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg htpos.le h1t.le
      exact mul_nonneg hb0 (Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hv_nneg i) (hv_le_one i)))
    have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg htpos.le h1t.le
    have hbu_le : b * ∑ i, Real.negMulLog (u i)
        ≤ b * Real.log (Fintype.card ι : ℝ) :=
      mul_le_mul_of_nonneg_left hHu_le hb0
    nlinarith [h1, hbu_le, hbnng]
  -- финальное масштабирование
  have hapos : 0 < a := by rw [ha]; exact div_pos (by norm_num) h1t
  have hbscale : b / a = t := by
    rw [ha, hb]
    field_simp
  have hhscale : Real.binEntropy b / a = (1 + t) * Real.binEntropy b := by
    have : a = 1 / (1 + t) := ha
    rw [this]
    field_simp
  have hbb : b = t / (1 + t) := hb
  -- заменяем Σ|p−q| = 2t в цели
  have hsumAbs : (∑ i, |p i - q i|) / 2 = t := by
    have := ht
    unfold Hagi.Information.tvHalf at this
    linarith
  unfold Hagi.Information.shannon Hagi.Information.tvHalf
  rw [hsumAbs]
  -- из hchain делением на a
  have hkey : a * ((∑ i, Real.negMulLog (p i)) - ∑ i, Real.negMulLog (q i))
      ≤ b * Real.log (Fintype.card ι : ℝ) + Real.binEntropy b := by
    nlinarith [hchain]
  -- a·H ≤ b·log d + h₂(b); делим на a и подставляем масштабы
  have hscale : b * Real.log (Fintype.card ι : ℝ) + Real.binEntropy b
      = a * (t * Real.log (Fintype.card ι : ℝ)
        + (1 + t) * Real.binEntropy (t / (1 + t))) := by
    have hbt : b = t / (1 + t) := hb
    have hat : a = 1 / (1 + t) := ha
    rw [hbt, hat]
    field_simp
  rw [hscale] at hkey
  nlinarith [hkey, hapos]


end Hagi.Unified


/-!
# InfoCanonical — канонические мосты теории информации (TD-03, цикл 15)
# (в Unified: мост потребляет FannesComplete из того же слоя)

Дублирование определений (аудит TD-03): энтропия/TV определены
независимо в `Prelude.Info` (entDef/tvDef) и
`Information.DiscreteFannes` (shannon/tvHalf). Мосты ниже
устанавливают ТОЧНЫЕ тождества, после чего любой набор теорем
(Пинскер из Probability.PinskerTV, Фаннес из
Unified.FannesComplete) применим к обоим мирам без дублей —
merge-before-delete: сначала мосты, удаление дублирующих
обёрток — отдельное решение после аудита потребителей.
-/

open Finset

namespace Hagi.Unified.InfoCanonical

/-- Энтропии совпадают: shannon = entDef. -/
theorem shannon_eq_entDef {V : Type*} [Fintype V] (p : V → ℝ) :
    Hagi.Information.shannon p = Hagi.Prelude.entDef p := by
  simp [Hagi.Information.shannon, Hagi.Prelude.entDef,
    Real.negMulLog]

/-- Полная вариация: tvHalf = tvDef. -/
theorem tvHalf_eq_tvDef {V : Type*} [Fintype V] (p q : V → ℝ) :
    Hagi.Information.tvHalf p q = Hagi.Prelude.tvDef p q := by
  rfl

/-- ПРИМЕР ДЕЛЕГАЦИИ: фаннес-граница Фаннеса в мире Prelude:
через мост переносится главная теорема FannesComplete. -/
theorem fanes_entDef {V : Type*} [Fintype V] [DecidableEq V]
    (p q : V → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    Hagi.Prelude.entDef p - Hagi.Prelude.entDef q
      ≤ (Hagi.Prelude.tvDef p q) * Real.log (Fintype.card V)
        + (1 + Hagi.Prelude.tvDef p q)
          * Real.binEntropy (Hagi.Prelude.tvDef p q
            / (1 + Hagi.Prelude.tvDef p q)) := by
  have hkey := Hagi.Unified.fanes_unconditional (ι := V) p q hp hq
    hp1 hq1
  rw [shannon_eq_entDef p, shannon_eq_entDef q, tvHalf_eq_tvDef] at hkey
  exact hkey

end Hagi.Unified.InfoCanonical

/-!
# Нернст через Фаннес (R539)

Третья теорема термодинамики для обучения: энтропия
Гиббс-распределения стремится к нулю при охлаждении.
Ядро статьи — композиция двух уже доказанных машин:

* переводчик δ-зазора в TV-расстояние до дирака: если
  минимум энергии отделён зазором δ, то полная масса вне
  минимума t_n = Σ_{v≠v*} p_{T_n}(v) ≤ C·e^{−δ/T_n}
  (граница R386 `gibbs_concentration`);
* Fannes-граница (R532 `fanes_unconditional`): энтропия
  распределения,-close к дираку на t, ограничена
  t·log d + (1+t)·h₂(t/(1+t)).

Итог: S(p_T) ≤ C·e^{−δ/T}·log d + (1+C·e^{−δ/T})·h₂(·) —
явная экспоненциальная оценка, стремящаяся к нулю при
T → 0⁺ (термин экспоненциально мал, Nernst).

* `shannon_dirac_zero` — энтропия дирака равна нулю;
* `tvHalf_dirac_eq` — tvHalf p (dirac v*) = масса вне v*;
* `nernst_fannes` — S(p) ≤ t·log d + (1+t)·h₂(t/(1+t)),
  t = масса вне v*;
* `nernst_explicit` — при Gibbs-весах с зазором δ: явная
  экспоненциальная граница S ≤ Ce^{−δ/T}·log d + ….
-/

namespace Hagi.Unified.NernstFannes

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Дирак-вектор массы 1 в точке v*. -/
noncomputable def dirac (vstar : V) : V → ℝ :=
  fun v => if v = vstar then 1 else 0

/-- Дирак — вероятностный вектор. -/
theorem dirac_sum (vstar : V) : ∑ v, dirac vstar v = 1 := by
  classical
  rw [Finset.sum_eq_single vstar]
  · simp [dirac]
  · intro v _ hv
    simp [dirac, hv]
  · simp

/-- Энтропия дирака равна нулю. -/
theorem shannon_dirac_zero (vstar : V) :
    Hagi.Information.shannon (dirac vstar) = 0 := by
  classical
  unfold Hagi.Information.shannon
  rw [Finset.sum_eq_single vstar]
  · simp [dirac]
  · intro v _ hv
    simp [dirac, hv]
  · simp

/-- Полная масса вне v* для дирак-сравнения: tvHalf = t. -/
theorem tvHalf_dirac_eq (p : V → ℝ) (vstar : V)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (t : ℝ) (ht : ∑ v ∈ univ.erase vstar, p v = t) :
    Hagi.Information.tvHalf p (dirac vstar) = t := by
  classical
  unfold Hagi.Information.tvHalf
  have hsplit : ∑ v, |p v - dirac vstar v|
      = |p vstar - dirac vstar vstar|
        + ∑ v ∈ univ.erase vstar, |p v - dirac vstar v| := by
    have hsum := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun v => v = vstar) (fun v => |p v - dirac vstar v|)
    have hfil : univ.filter (fun v => v = vstar) = {vstar} := by
      ext v
      by_cases hv : v = vstar
      · subst hv
        simp
      · simp [hv]
    have hnot : univ.filter (fun v => ¬ v = vstar) = univ.erase vstar := by
      ext v
      by_cases hv : v = vstar
      · subst hv
        simp
      · simp [hv]
    rw [hfil, Finset.sum_singleton, hnot] at hsum
    exact hsum.symm
  rw [hsplit, add_div]
  have h1 : |p vstar - dirac vstar vstar| = ∑ v ∈ univ.erase vstar, p v := by
    have hdir1 : dirac vstar vstar = 1 := by unfold dirac; norm_num
    have hsplit2 : ∑ v ∈ univ.erase vstar, p v + p vstar = ∑ v, p v := by
      exact Finset.sum_erase_add (s := univ) p (a := vstar)
        (Finset.mem_univ vstar)
    rw [ht] at hsplit2
    have hps2 : p vstar = 1 - t := by linarith [hsplit2, hps]
    rw [hdir1, hps2]
    show |1 - t - 1| = ∑ v ∈ univ.erase vstar, p v
    have htv : t = 1 - p vstar := by linarith [hsplit2, hps]
    have hple : p vstar ≤ 1 := by
      have hmem : vstar ∈ univ := Finset.mem_univ vstar
      have hsingle := Finset.single_le_sum (f := p)
        (fun v _ => hp v) hmem
      linarith [hsplit2, hps]
    have htnn : 0 ≤ t := by linarith [htv, hple]
    have hneg : (1:ℝ) - t - 1 = -t := by ring
    rw [hneg, abs_neg, abs_of_nonneg htnn, ht]
  have h2 : ∑ v ∈ univ.erase vstar, |p v - dirac vstar v|
      = ∑ v ∈ univ.erase vstar, p v := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hvne : v ≠ vstar := Finset.ne_of_mem_erase hv
    have hdir0 : dirac vstar v = 0 := by unfold dirac; simp [hvne]
    show |p v - dirac vstar v| = p v
    rw [hdir0, sub_zero, abs_of_nonneg (hp v)]
  show |p vstar - dirac vstar vstar| / 2
      + (∑ v ∈ univ.erase vstar, |p v - dirac vstar v|) / 2 = t
  rw [h1, h2, ht]
  ring

/-- **Нернст-ядро через Фаннес (R539)**: если p — вероятностный
вектор с полной массой t вне v*, то энтропия ограничена
Fannes-границей с дирак-сравнением: S(p) ≤ t·log d +
(1+t)·h₂(t/(1+t)). При t → 0 энтропия → 0 — третья
теорема термодинамики. -/
theorem nernst_fannes (p : V → ℝ) (vstar : V)
    (hp : ∀ v, 0 ≤ p v) (hps : ∑ v, p v = 1)
    (t : ℝ) (ht : ∑ v ∈ univ.erase vstar, p v = t) :
    Hagi.Information.shannon p
      ≤ t * Real.log (Fintype.card V : ℝ)
        + (1 + t) * Real.binEntropy (t / (1 + t)) := by
  have hkey := Hagi.Unified.fanes_unconditional p (dirac vstar)
    hp (fun v => by
      by_cases hv : v = vstar
      · simp [dirac, hv]
      · simp [dirac, hv]) hps (dirac_sum vstar)
  rw [tvHalf_dirac_eq p vstar hp hps t ht] at hkey
  have hzero : Hagi.Information.shannon (dirac vstar) = 0 :=
    shannon_dirac_zero vstar
  rw [hzero, sub_zero] at hkey
  exact hkey


/-- **Гиббс + Нернст (R549)**: у Гиббс-распределения с δ-зазором
энтропия экспоненциально затухает при охлаждении: с
t̂ = (d−1)·e^{−δ/T} (оценка массы вне v* из `gibbs_concentration`):
S(p_T) ≤ t̂·log d + (1+t̂)·log 2 — третий закон с явной
экспоненциальной скоростью (композиция gibbs_concentration +
nernst_fannes + binEntropy ≤ log 2). -/
theorem gibbs_nernst {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Hagi.Information.shannon
        (fun v => Real.exp (-(E v) / T)
          / ∑ w, Real.exp (-(E w) / T))
      ≤ ((Finset.univ.erase vstar).card : ℝ) * Real.exp (-δ / T)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T)) * Real.log 2 := by
  classical
  set p : V → ℝ := fun v => Real.exp (-(E v) / T)
      / ∑ w, Real.exp (-(E w) / T) with hpdef
  set t : ℝ := ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) with htdef
  -- нормировка и неотрицательность Гиббса
  have hZpos : 0 < ∑ w, Real.exp (-(E w) / T) :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hpsum : ∑ v, p v = 1 := by
    rw [hpdef, ← Finset.sum_div, div_self (ne_of_gt hZpos)]
  have hpnn : ∀ v, 0 ≤ p v := fun v => by
    unfold p
    positivity
  -- масса вне v* : hm ≤ t  (обращение gibbs_concentration)
  have hconc := gibbs_concentration E δ vstar hgap T hT
  have hmass : ∑ v ∈ Finset.univ.erase vstar, p v
      + p vstar = ∑ v, p v := by
    exact Finset.sum_erase_add (s := Finset.univ) p (a := vstar)
      (Finset.mem_univ vstar)
  have hpvs : p vstar = Real.exp (-(E vstar) / T)
      / ∑ w, Real.exp (-(E w) / T) := rfl
  have hmass1 : ∑ v ∈ Finset.univ.erase vstar, p v + p vstar = 1 := by
    rw [hmass, hpsum]
  have hmle : ∑ v ∈ Finset.univ.erase vstar, p v ≤ t := by
    have hkey : ∑ v ∈ Finset.univ.erase vstar, p v
        + (Real.exp (-(E vstar) / T) / ∑ w, Real.exp (-(E w) / T))
      = 1 := by rw [← hpvs]; exact hmass1
    linarith [hkey, hconc]
  -- Фаннес-граница при фактической массе (Σ вне v*)
  have hS0 : 0 ≤ ∑ v ∈ Finset.univ.erase vstar, p v :=
    Finset.sum_nonneg (fun v _ => hpnn v)
  have hfact := nernst_fannes p vstar hpnn hpsum _ rfl
  -- грубая форма: h₂ ≤ log 2 и монотонность по массе ≤ t
  have hh2 : ∀ x : ℝ, Real.binEntropy (x / (1 + x)) ≤ Real.log 2 :=
    fun x => Real.binEntropy_le_log_two
  have hlin : ∀ x : ℝ, x ≤ t → 0 ≤ x →
      x * Real.log (Fintype.card V : ℝ)
        + (1 + x) * Real.log 2 ≤
      t * Real.log (Fintype.card V : ℝ) + (1 + t) * Real.log 2 := by
    intro x hx h0
    have hcard : (1 : ℝ) ≤ Fintype.card V := by
      have : 0 < Fintype.card V :=
        Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩
      exact_mod_cast this
    have hlogd : 0 ≤ Real.log (Fintype.card V : ℝ) :=
      Real.log_nonneg hcard
    have h1 : x * Real.log (Fintype.card V : ℝ)
        ≤ t * Real.log (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right hx hlogd
    have h2 : (1 + x) * Real.log 2 ≤ (1 + t) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith)
        (Real.log_pos (by norm_num)).le
    linarith
  calc Hagi.Information.shannon p
      ≤ (∑ v ∈ Finset.univ.erase vstar, p v)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ∑ v ∈ Finset.univ.erase vstar, p v)
            * Real.binEntropy
              ((∑ v ∈ Finset.univ.erase vstar, p v)
                / (1 + ∑ v ∈ Finset.univ.erase vstar, p v)) := hfact
    _ ≤ (∑ v ∈ Finset.univ.erase vstar, p v)
          * Real.log (Fintype.card V : ℝ)
        + (1 + ∑ v ∈ Finset.univ.erase vstar, p v) * Real.log 2 :=
        by
          refine add_le_add_right (mul_le_mul_of_nonneg_left
            (hh2 _) (by linarith)) _
    _ ≤ t * Real.log (Fintype.card V : ℝ) + (1 + t) * Real.log 2 :=
        hlin _ hmle hS0

end Hagi.Unified.NernstFannes


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
