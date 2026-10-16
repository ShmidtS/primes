/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.EntropyConvexity
import Hagi.Information.DiscreteFannes
set_option linter.style.header false

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
  -- KL(p ‖ uniform) ≥ 0: Σ p·log(p·d) ≥ 0 ⟹ H ≤ log d
  classical
  have hdpos : 0 < (Fintype.card ι : ℝ) := by positivity
  have hBsum : ∑ i : ι, 1 / (Fintype.card ι : ℝ) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hsupp : ∀ i, 0 < p i → 0 < 1 / (Fintype.card ι : ℝ) :=
    fun i _ => div_pos one_pos hdpos
  have hkl := zs_kl p (fun _ => 1 / (Fintype.card ι : ℝ)) hp
    (fun i => div_nonneg (by norm_num : (0:ℝ) ≤ 1) hdpos.le)
    hp1 (le_of_eq hBsum) hsupp
  -- разложение: log(p/(1/d)) = log p + log d (p > 0);
  -- при p = 0 слагаемое 0·log 0 = 0, вклад 0·log d = 0
  have hterm : ∀ i, p i * Real.log (p i / (1 / (Fintype.card ι : ℝ)))
      = p i * Real.log (p i) + p i * Real.log ((Fintype.card ι : ℝ)) := by
    intro i
    by_cases hpi : p i = 0
    · have hz0 : (0:ℝ) / (1 / (Fintype.card ι : ℝ)) = 0 := zero_div _
      rw [hpi, hz0, Real.log_zero, mul_zero, zero_mul]
      ring
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
      have hdiv : p i / (1 / (Fintype.card ι : ℝ))
          = p i * (Fintype.card ι : ℝ) := by
        field_simp
      have hcardne : (Fintype.card ι : ℝ) ≠ 0 := by positivity
      rw [hdiv, Real.log_mul hpos.ne' hcardne]
      ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hkl
  -- Σ p·log p = −Σ negMulLog p; Σ p·log d = log d·Σp = log d
  have hsplit : ∀ z : ℝ, z * Real.log z = -(Real.negMulLog z) := by
    intro z; unfold Real.negMulLog; ring
  have hsumL : ∑ i, p i * Real.log (p i) = -(∑ i, Real.negMulLog (p i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => hsplit (p i))
  have hsumR : ∑ i, p i * Real.log ((Fintype.card ι : ℝ))
      = Real.log ((Fintype.card ι : ℝ)) := by
    rw [← Finset.sum_mul, hp1, one_mul]
  rw [Finset.sum_add_distrib, hsumL, hsumR] at hkl
  -- 0 ≤ −H + log d ⟹ H ≤ log d
  linarith

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
