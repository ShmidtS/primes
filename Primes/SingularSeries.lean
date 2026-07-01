import Mathlib
import Primes.Basic
import Primes.GapFrequency
import Primes.Wheel

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace PrimeGaps

noncomputable section

open scoped BigOperators

/-! ## Definitions: singular series, divisor correction, wheel factors -/

def twinPrimeConstantPartial (y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

def IsTwinPrimeConstant (C₂ : ℝ) : Prop :=
  Filter.Tendsto twinPrimeConstantPartial Filter.atTop (nhds C₂)

def finitePairSieveFactor (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then 1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ) else 1

def wheelLocalSingularFactor (g p : Nat) : ℝ :=
  (1 - (endpointForbiddenResidueCount g p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2

def finiteWheelSingularSeries (g y : Nat) : ℝ :=
  (Finset.range (y + 1)).prod fun p =>
    if Nat.Prime p then wheelLocalSingularFactor g p else 1

def finiteWheelEvenFactor (k y : Nat) : ℝ :=
  ((Finset.range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)).prod
    (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- D(k) = ∏_{p|k, p>2} (p-1)/(p-2). -/
def divisorCorrectionProduct (k : Nat) : ℝ :=
  (Finset.range (k + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- S(g) = 2C₂ · D(g/2) for even g, 0 for odd g. -/
def singularSeriesFactor (C₂ : ℝ) (g : Nat) : ℝ :=
  if Even g then 2 * C₂ * divisorCorrectionProduct (g / 2) else 0

def logarithmicIntegral₂ (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2

/-! ## Core D properties -/

theorem divisorCorrectionProduct_eq_primeFactors (k : Nat) :
    divisorCorrectionProduct k =
      ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
        (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  by_cases hk0 : k = 0
  · subst k; simp [divisorCorrectionProduct]
  · rw [divisorCorrectionProduct, ← Finset.prod_filter]
    congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    refine ⟨fun h => ⟨⟨h.2.1, h.2.2.2, hk0⟩, h.2.2.1⟩, ?_⟩
    · rintro ⟨⟨hprime, hdvd, _⟩, hgt⟩
      refine ⟨Nat.lt_succ_iff.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd), hprime, hgt, hdvd⟩

theorem divisorCorrectionProduct_mul_of_coprime {k k' : Nat}
    (_hk : k ≠ 0) (_hk' : k' ≠ 0) (hcoprime : Nat.Coprime k k') :
    divisorCorrectionProduct (k * k') =
      divisorCorrectionProduct k * divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors,
      divisorCorrectionProduct_eq_primeFactors, hcoprime.primeFactors_mul]
  have hfu : (Nat.primeFactors k ∪ Nat.primeFactors k').filter (fun p => 2 < p) =
      (Nat.primeFactors k).filter (fun p => 2 < p) ∪
      (Nat.primeFactors k').filter (fun p => 2 < p) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  rw [hfu, Finset.prod_union (by
    exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      hcoprime.disjoint_primeFactors)]

theorem divisorCorrectionProduct_pow_eq (k : Nat) (ha : 0 < a) :
    divisorCorrectionProduct (k ^ a) = divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors,
      Nat.primeFactors_pow k (Nat.ne_of_gt ha)]

theorem divisorCorrectionProduct_prime (p : Nat) (hp : Nat.Prime p) (hp_odd : 2 < p) :
    divisorCorrectionProduct p = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  have hpf : (Nat.primeFactors p).filter (fun q => 2 < q) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hgt2⟩; rw [Nat.mem_primeFactors] at hmem
      exact (Nat.prime_dvd_prime_iff_eq hmem.1 hp).mp hmem.2.1
    · rintro rfl; exact ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩, hp_odd⟩
  rw [hpf, Finset.prod_singleton]

theorem divisorCorrectionProduct_pow_two (a : Nat) :
    divisorCorrectionProduct (2 ^ a) = 1 := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst ha; simp [Nat.primeFactors_one]
  · have hpf := Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two
    rw [hpf, Finset.filter_eq_empty_iff.mpr fun p hp => by
      simp only [Finset.mem_singleton] at hp; omega]
    simp

theorem divisorCorrectionProduct_pow_two_mul (a : Nat) (m : Nat) (hm : Odd m) :
    divisorCorrectionProduct (2 ^ a * m) = divisorCorrectionProduct m := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  by_cases ha : a = 0
  · subst ha; simp
  · have h2pf := Nat.primeFactors_prime_pow (Nat.ne_of_gt (by omega : 0 < a)) Nat.prime_two
    rw [Nat.primeFactors_mul (pow_ne_zero a two_ne_zero) hm.pos.ne',
        h2pf, Finset.filter_union,
        Finset.filter_eq_empty_iff.mpr fun p hp => by
          simp only [Finset.mem_singleton] at hp; omega,
        Finset.empty_union]

/-! ## D bounds and characterization -/

theorem divisorCorrectionProduct_ge_one (k : Nat) :
    1 ≤ divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  apply Finset.one_le_prod
  rintro p hp
  have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  rw [le_div_iff₀ (by linarith : 0 < (p : ℝ) - 2)]; linarith

theorem divisorCorrectionProduct_gt_one_iff (k : Nat) :
    1 < divisorCorrectionProduct k ↔
    ((Nat.primeFactors k).filter (fun p => 2 < p)).Nonempty := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  refine ⟨fun hgt => ?_, fun hne => ?_⟩
  · by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.prod_empty] at hgt; norm_num at hgt
  · obtain ⟨p, hp⟩ := hne
    have hpf : 1 < ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
      have : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      rw [lt_div_iff₀ (by linarith)]; linarith
    have hrest : 1 ≤ (((Nat.primeFactors k).filter (fun q => 2 < q)).erase p).prod
        (fun q => ((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
      apply Finset.one_le_prod; rintro q hq
      have : (2 : ℝ) < q := by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
      rw [le_div_iff₀ (by linarith)]; linarith
    rw [← Finset.insert_erase hp, Finset.prod_insert (Finset.notMem_erase _ _)]
    nlinarith [hpf, hrest]

theorem divisorCorrectionProduct_eq_one_iff (k : Nat) :
    divisorCorrectionProduct k = 1 ↔
    (Nat.primeFactors k).filter (fun p => 2 < p) = ∅ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hcontra
    have hne : ((Nat.primeFactors k).filter (fun p => 2 < p)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcontra
    have : 1 < divisorCorrectionProduct k := Iff.mpr (divisorCorrectionProduct_gt_one_iff k) hne
    linarith
  · rw [divisorCorrectionProduct_eq_primeFactors, h, Finset.prod_empty]

/-! ## D Euler connection -/

private lemma euler_factor_identity (p : ℝ) (hp : 2 < p) :
    ((p - 1) / (p - 2)) * (1 - 1 / (p - 1) ^ 2) = p / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp2 : p - 2 ≠ 0 := by linarith
  field_simp [hp0, hp1, hp2]; ring

/-- D(k) · ∏_{p|k, p>2} (1-1/(p-1)²) = ∏_{p|k, p>2} p/(p-1). -/
theorem divisorCorrectionProduct_euler_connection (k : Nat) :
    divisorCorrectionProduct k *
    ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
      (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
    ((Nat.primeFactors k).filter (fun p => 2 < p)).prod
      (fun p => (p : ℝ) / ((p : ℝ) - 1)) := by
  rw [divisorCorrectionProduct_eq_primeFactors, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact euler_factor_identity (p : ℝ) (by exact_mod_cast (Finset.mem_filter.mp hp).2)

/-! ## D monotonicity and primorial -/

theorem divisorCorrectionProduct_le_of_primeFactors_subset {k k' : Nat}
    (hsub : (Nat.primeFactors k).filter (fun p => 2 < p) ⊆
            (Nat.primeFactors k').filter (fun p => 2 < p)) :
    divisorCorrectionProduct k ≤ divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  have hge1 : ∀ p ∈ (Nat.primeFactors k').filter (fun q => 2 < q),
      (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rintro p hp; have : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    rw [le_div_iff₀ (by linarith)]; linarith
  have hextra : 1 ≤ ((Nat.primeFactors k').filter (fun q => 2 < q) \
       (Nat.primeFactors k).filter (fun q => 2 < q)).prod
       (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) :=
    Finset.one_le_prod (fun p hp => hge1 p (Finset.mem_sdiff.mp hp).1)
  have hnonneg : 0 ≤ ((Nat.primeFactors k).filter (fun q => 2 < q)).prod
       (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_nonneg; rintro p hp
    have : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    exact div_nonneg (by linarith) (by linarith)
  rw [← Finset.prod_sdiff hsub]
  have hextra_nn : 0 ≤ ((Nat.primeFactors k').filter (fun q => 2 < q) \
       (Nat.primeFactors k).filter (fun q => 2 < q)).prod
       (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := le_trans zero_le_one hextra
  have := mul_le_mul hextra (le_refl _) hnonneg hextra_nn
  rwa [one_mul] at this

theorem divisorCorrectionProduct_le_of_dvd_primorial (k m : Nat) (_hk : 0 < k)
    (hdvd : k ∣ primorial m) :
    divisorCorrectionProduct k ≤ divisorCorrectionProduct (primorial m) := by
  apply divisorCorrectionProduct_le_of_primeFactors_subset
  intro p hp; rw [Finset.mem_filter] at hp
  have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp.1).1
  have hp_dvd_k : p ∣ k := (Nat.mem_primeFactors.mp hp.1).2.1
  have hp_dvd_Pm : p ∣ primorial m := hp_dvd_k.trans hdvd
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_Pm, (primorial_pos m).ne'⟩, hp.2⟩

theorem divisorCorrectionProduct_primorial (m : Nat) (hm : 2 ≤ m) :
    divisorCorrectionProduct (primorial m) =
      ((Finset.range m).filter (fun i => 0 < i)).prod
        (fun i => ((Nat.nth Nat.Prime i : ℝ) - 1) / ((Nat.nth Nat.Prime i : ℝ) - 2)) := by
  rw [divisorCorrectionProduct_eq_primeFactors, primeFactors_primorial m (by omega)]
  rw [Finset.filter_image]
  have hinj : ∀ x ∈ (Finset.range m).filter (fun i => 2 < Nat.nth Nat.Prime i),
      ∀ y ∈ (Finset.range m).filter (fun i => 2 < Nat.nth Nat.Prime i),
      Nat.nth Nat.Prime x = Nat.nth Nat.Prime y → x = y := by
    intro x _ y _ hxy
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hxy
  rw [Finset.prod_image hinj]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hirange, hlt⟩; refine ⟨hirange, ?_⟩
    by_cases hi : i = 0; · subst hi; rw [Nat.nth_prime_zero_eq_two] at hlt; omega
    · omega
  · rintro ⟨hirange, hipos⟩; refine ⟨hirange, ?_⟩
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hge : 1 ≤ i := by omega
    have hle : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime i :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).le_iff_le.mpr hge
    rw [h1] at hle; omega

theorem divisorCorrectionProduct_primorial_strictMono (m : Nat) (hm : 1 ≤ m) :
    divisorCorrectionProduct (primorial m) < divisorCorrectionProduct (primorial (m + 1)) := by
  rw [primorial_succ]
  have hcoprime : Nat.Coprime (primorial m) (Nat.nth Nat.Prime m) := by
    unfold primorial; rw [Nat.coprime_prod_left_iff]
    intro i hi
    have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
    have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
    have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
    exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)
  rw [divisorCorrectionProduct_mul_of_coprime (ne_of_gt (primorial_pos m))
        (Nat.prime_nth_prime m).ne_zero hcoprime]
  have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
  have hp_odd : 2 < Nat.nth Nat.Prime m := by
    by_cases hm0 : m = 0; · subst hm0; rw [Nat.nth_prime_zero_eq_two]; omega
    · have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
      have hge : 1 ≤ m := by omega
      have hle : 3 ≤ Nat.nth Nat.Prime m := by
        rw [← h1]; exact (Nat.nth_strictMono Nat.infinite_setOf_prime).le_iff_le.mpr hge
      omega
  rw [divisorCorrectionProduct_prime (Nat.nth Nat.Prime m) hpm hp_odd]
  have hD_pos : 0 < divisorCorrectionProduct (primorial m) := by
    have := divisorCorrectionProduct_ge_one (primorial m); linarith
  have hfactor_gt1 : 1 < ((Nat.nth Nat.Prime m : ℝ) - 1) / ((Nat.nth Nat.Prime m : ℝ) - 2) := by
    have hp_real : 2 < (Nat.nth Nat.Prime m : ℝ) := by exact_mod_cast hp_odd
    rw [lt_div_iff₀ (by linarith : 0 < (Nat.nth Nat.Prime m : ℝ) - 2)]; linarith
  have h := mul_lt_mul_of_pos_left hfactor_gt1 hD_pos
  rwa [mul_one] at h

theorem divisorCorrectionProduct_lt_of_strict_subset {k k' : Nat}
    (hsub : (Nat.primeFactors k).filter (fun p => 2 < p) ⊂
            (Nat.primeFactors k').filter (fun p => 2 < p)) :
    divisorCorrectionProduct k < divisorCorrectionProduct k' := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  set P := (Nat.primeFactors k).filter (fun p => 2 < p)
  set Q := (Nat.primeFactors k').filter (fun p => 2 < p)
  have h_subset : P ⊆ Q := hsub.1
  have h_not_superset : ¬(Q ⊆ P) := hsub.2
  have h_sdiff_nonempty : (Q \ P).Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    exact h_not_superset (fun q hq => by
      by_contra hq_not; have : q ∈ Q \ P := Finset.mem_sdiff.mpr ⟨hq, hq_not⟩
      rw [h] at this; exact absurd this (by simp))
  rw [← Finset.prod_sdiff h_subset]
  have h_P_pos : 0 < P.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_pos; rintro q hq
    have hq_gt2 : 2 < q := by
      have : q ∈ (Nat.primeFactors k).filter (fun p => 2 < p) := hq
      rw [Finset.mem_filter] at this; exact this.2
    have : (2 : ℝ) < q := by exact_mod_cast hq_gt2
    exact div_pos (by linarith) (by linarith)
  have h_extra_gt1 : 1 < (Q \ P).prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    have h_all_gt1 : ∀ q ∈ (Q \ P), (1 : ℝ) < ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
      rintro q hq
      have hq_in_Q : q ∈ Q := (Finset.mem_sdiff.mp hq).1
      have hq_gt2 : 2 < q := by
        have : q ∈ (Nat.primeFactors k').filter (fun p => 2 < p) := hq_in_Q
        rw [Finset.mem_filter] at this; exact this.2
      have : (2 : ℝ) < q := by exact_mod_cast hq_gt2
      rw [lt_div_iff₀ (by linarith : 0 < (q : ℝ) - 2)]; linarith
    rcases Finset.eq_empty_or_nonempty (Q \ P) with h_empty | h_ne
    · exfalso; exact absurd h_empty (Finset.nonempty_iff_ne_empty.mp h_sdiff_nonempty)
    · obtain ⟨q, hq⟩ := h_ne
      have hq_factor : (1 : ℝ) < ((q : ℝ) - 1) / ((q : ℝ) - 2) := h_all_gt1 q hq
      have h_rest_ge1 : (1 : ℝ) ≤ ((Q \ P).erase q).prod
          (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
        apply Finset.one_le_prod; rintro r hr
        have hr_in : r ∈ (Q \ P) := Finset.mem_of_mem_erase hr
        have hr_in_Q : r ∈ Q := (Finset.mem_sdiff.mp hr_in).1
        have hr_gt2 : 2 < r := by
          have : r ∈ (Nat.primeFactors k').filter (fun p => 2 < p) := hr_in_Q
          rw [Finset.mem_filter] at this; exact this.2
        have : (2 : ℝ) < r := by exact_mod_cast hr_gt2
        rw [le_div_iff₀ (by linarith : 0 < (r : ℝ) - 2)]; linarith
      have h_split : (Q \ P).prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) =
        ((q : ℝ) - 1) / ((q : ℝ) - 2) * ((Q \ P).erase q).prod
          (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
        conv_lhs => rw [← Finset.insert_erase hq]
        rw [Finset.prod_insert]; exact Finset.notMem_erase _ _
      rw [h_split]; nlinarith [hq_factor, h_rest_ge1]
  nlinarith [h_extra_gt1, h_P_pos]

/-! ## S key properties: non-injectivity, HL ordering -/

/-- **S не инъективна**: S(2) = S(4) = S(8) = 2C₂. -/
theorem singularSeriesFactor_not_injective (C₂ : ℝ) :
    singularSeriesFactor C₂ 2 = singularSeriesFactor C₂ 4 ∧
    singularSeriesFactor C₂ 4 = singularSeriesFactor C₂ 8 := by
  have hD1 : divisorCorrectionProduct 1 = 1 := by
    rw [divisorCorrectionProduct_eq_primeFactors, Nat.primeFactors_one, Finset.filter_empty,
        Finset.prod_empty]
  have hD2 : divisorCorrectionProduct 2 = 1 := divisorCorrectionProduct_pow_two 1
  have hD4 : divisorCorrectionProduct 4 = 1 :=
    (divisorCorrectionProduct_pow_eq 2 (by omega : 0 < 2)).trans hD2
  have hS : ∀ g, Even g → divisorCorrectionProduct (g / 2) = 1 →
      singularSeriesFactor C₂ g = 2 * C₂ := by
    intro g hg hD; unfold singularSeriesFactor; rw [if_pos hg, hD, mul_one]
  have hS2 := hS 2 (by decide) hD1
  have hS4 := hS 4 (by decide) hD2
  have hS8 := hS 8 (by decide) hD4
  exact ⟨hS2.trans hS4.symm, hS4.trans hS8.symm⟩

/-- **S(6) > S(2) при C₂ > 0**: HL предсказывает больше пар с gap 6, чем с gap 2. -/
theorem singularSeriesFactor_six_gt_two (C₂ : ℝ) (hC₂ : 0 < C₂) :
    2 * C₂ < singularSeriesFactor C₂ 6 := by
  unfold singularSeriesFactor
  rw [if_pos (by decide : Even 6), show (6 : Nat) / 2 = 3 from by norm_num,
      divisorCorrectionProduct_prime 3 (by decide) (by decide)]
  nlinarith

/-! ## Squarefree kernel: complete S factorization -/

def oddSquarefreeKernel (k : Nat) : Nat :=
  ((Nat.primeFactors k).filter (fun p => 2 < p)).prod (fun p => p)

theorem divisorCorrectionProduct_eq_oddSquarefreeKernel (k : Nat) (_hk : k ≠ 0) :
    divisorCorrectionProduct k = divisorCorrectionProduct (oddSquarefreeKernel k) := by
  rw [divisorCorrectionProduct_eq_primeFactors, divisorCorrectionProduct_eq_primeFactors]
  have h_eq : (Nat.primeFactors (oddSquarefreeKernel k)).filter (fun p => 2 < p) =
               (Nat.primeFactors k).filter (fun p => 2 < p) := by
    unfold oddSquarefreeKernel
    have h_primes : ∀ p ∈ (Nat.primeFactors k).filter (fun p => 2 < p), Nat.Prime p := by
      intro p hp; rw [Finset.mem_filter] at hp
      exact (Nat.mem_primeFactors.mp hp.1).1
    rw [Nat.primeFactors_prod h_primes, Finset.filter_filter]
    simp [and_and_left, and_self]
  rw [h_eq]

theorem singularSeriesFactor_eq_squarefreeKernel (C₂ : ℝ) (g : Nat) (hg : Even g) (hg0 : 0 < g) :
    singularSeriesFactor C₂ g =
      singularSeriesFactor C₂ (2 * oddSquarefreeKernel (g / 2)) := by
  have hk_ne_zero : g / 2 ≠ 0 := by
    intro h; obtain ⟨k, hkg⟩ := hg; have : g = 0 := by omega
    exact absurd this (Nat.ne_of_gt hg0)
  have hD : divisorCorrectionProduct (g / 2) =
      divisorCorrectionProduct (oddSquarefreeKernel (g / 2)) :=
    divisorCorrectionProduct_eq_oddSquarefreeKernel (g / 2) hk_ne_zero
  have h_rad_div : (2 * oddSquarefreeKernel (g / 2)) / 2 = oddSquarefreeKernel (g / 2) := by
    have h2 : 0 < (2 : Nat) := by norm_num
    have h_comm : 2 * oddSquarefreeKernel (g / 2) = oddSquarefreeKernel (g / 2) * 2 := by ring
    rw [h_comm, Nat.mul_div_cancel _ h2]
  have h_even_rad : Even (2 * oddSquarefreeKernel (g / 2)) := even_two_mul _
  unfold singularSeriesFactor
  have hg_even := hg
  simp only [if_pos hg_even, if_pos h_even_rad, h_rad_div, hD]

/-! ## Wheel-singular series connection -/

private lemma algebraic_identity_wheel_div (p : ℝ) (hp : 2 < p) :
    (1 - 2 / p) / (1 - 1 / p) ^ 2 = 1 - 1 / (p - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hdenom : (1 - 1 / p) ≠ 0 := by
    have : 1 / p < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  field_simp [hp0, hp1, hdenom]; ring

theorem finiteWheelSingularSeries_odd_eq_zero {g y : Nat}
    (hg : Odd g) (hy : 2 ≤ y) :
    finiteWheelSingularSeries g y = 0 := by
  rw [finiteWheelSingularSeries, ← Finset.prod_filter]
  have h2mem : 2 ∈ (Finset.range (y + 1)).filter Nat.Prime := by
    simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by decide⟩
  have h2nd : ¬(2 : Nat) ∣ g := fun h =>
    Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h) hg
  have hf0 : wheelLocalSingularFactor g 2 = 0 := by
    rw [wheelLocalSingularFactor, endpointForbiddenResidueCount]
    simp only [h2nd, if_false]; norm_num
  exact Finset.prod_eq_zero h2mem hf0

theorem finiteWheelSingularSeries_even_eq (k y : Nat) (hy : 2 ≤ y) :
    finiteWheelSingularSeries (2 * k) y =
      2 * finiteWheelEvenFactor k y * twinPrimeConstantPartial y := by
  rw [finiteWheelSingularSeries, twinPrimeConstantPartial, finiteWheelEvenFactor]
  let s := Finset.range (y + 1)
  let oddDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ p ∣ k)
  let oddNonDivs := s.filter (fun p => Nat.Prime p ∧ 2 < p ∧ ¬p ∣ k)
  let allOdd := s.filter (fun p => Nat.Prime p ∧ 2 < p)
  have h2p : Nat.Prime 2 := by decide
  have h2n : 2 ∉ allOdd := by simp [allOdd, s]
  have hsp : s.filter Nat.Prime = insert 2 allOdd := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, s, allOdd, Finset.mem_range]
    refine ⟨fun ⟨hlt, hpr⟩ => ?_, fun h => ?_⟩
    · by_cases hp2 : p = 2; · exact Or.inl hp2
      · have h2le := Nat.Prime.two_le hpr; exact Or.inr ⟨hlt, hpr, by omega⟩
    · cases h with
      | inl h2 => subst h2; exact ⟨by omega, h2p⟩
      | inr hodd => exact ⟨hodd.1, hodd.2.1⟩
  have hsodd : allOdd = oddDivs ∪ oddNonDivs := by
    ext p
    simp only [allOdd, oddDivs, oddNonDivs, s, Finset.mem_filter,
      Finset.mem_union, Finset.mem_range]
    refine ⟨fun ⟨hlt, hpr, hgt2⟩ => ?_, fun h => ?_⟩
    · by_cases hpk : p ∣ k; · exact Or.inl ⟨hlt, hpr, hgt2, hpk⟩
      · exact Or.inr ⟨hlt, hpr, hgt2, hpk⟩
    · cases h with
      | inl hd => exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
      | inr hnd => exact ⟨hnd.1, hnd.2.1, hnd.2.2.1⟩
  have hdisj : Disjoint oddDivs oddNonDivs := by
    rw [Finset.disjoint_left]
    intro p hp hnp
    exact (Finset.mem_filter.mp hnp).2.2.2 (Finset.mem_filter.mp hp).2.2.2
  have hf2 : wheelLocalSingularFactor (2 * k) 2 = 2 := by
    rw [wheelLocalSingularFactor, endpointForbiddenResidueCount]
    have h2dvd : (2 : Nat) ∣ 2 * k := Nat.dvd_mul_right 2 k
    simp only [h2dvd, if_true]; norm_num
  have hpfilt : s.prod (fun p => if Nat.Prime p then
      wheelLocalSingularFactor (2 * k) p else 1) =
      (s.filter Nat.Prime).prod (fun p => wheelLocalSingularFactor (2 * k) p) := by
    rw [← Finset.prod_filter]
  rw [hpfilt, hsp, Finset.prod_insert h2n, hf2, hsodd, Finset.prod_union hdisj]
  have hpd : oddDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddDivs.prod (fun p =>
        ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have xm := Finset.mem_filter.mp hp
    have hdvd : p ∣ 2 * k := dvd_mul_of_dvd_right xm.2.2.2 2
    rw [wheelLocalSingularFactor, endpointForbiddenResidueCount]
    simp only [hdvd, if_true]
    have hp_real : (2 : ℝ) < p := by exact_mod_cast xm.2.2.1
    field_simp [hp_real.ne', (by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : (p : ℝ) - 2 ≠ 0)]
    ring
  rw [hpd]
  have hpnd : oddNonDivs.prod (fun p => wheelLocalSingularFactor (2 * k) p) =
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have xm := Finset.mem_filter.mp hp
    have hnd : ¬p ∣ 2 * k := by
      intro hd
      have hor : p ∣ 2 ∨ p ∣ k := (Nat.Prime.dvd_mul xm.2.1).mp hd
      cases hor with
      | inl h2 => have : p = 2 := (Nat.prime_dvd_prime_iff_eq xm.2.1 Nat.prime_two).mp h2; omega
      | inr hk => exact xm.2.2.2 hk
    rw [wheelLocalSingularFactor, endpointForbiddenResidueCount]
    simp only [hnd, if_false]
    exact algebraic_identity_wheel_div (p : ℝ) (by exact_mod_cast xm.2.2.1)
  rw [hpnd]
  rw [show oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 - 1 / ((p : ℝ) - 1) ^ 2)) =
        oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) from Finset.prod_mul_distrib ..]
  have h_twin_prod :
      oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
      oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    have h_eq : s.filter (fun p => Nat.Prime p ∧ 2 < p) = oddDivs ∪ oddNonDivs := hsodd
    rw [h_eq, Finset.prod_union hdisj]
  have htwin : s.prod (fun p =>
      if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) =
      (s.filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) := by
    rw [Finset.prod_filter]
  rw [show 2 * ((oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) *
        oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) =
      2 * oddDivs.prod (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (oddDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ)) *
         oddNonDivs.prod (fun p => (1 - 1 / ((p : ℝ) - 1) ^ 2 : ℝ))) from by ring,
    h_twin_prod, ← htwin]

/-! ## Genuinely new: singular series collision D(5) = D(77) -/

/-- D(5) = (5-1)/(5-2) = 4/3. -/
theorem divisorCorrectionProduct_five : divisorCorrectionProduct 5 = (4 : ℝ) / 3 := by
  rw [divisorCorrectionProduct_prime 5 (by decide) (by decide)]; norm_num

/-- D(77) = D(7·11) = 6/5 · 10/9 = 4/3. -/
theorem divisorCorrectionProduct_seven_eleven : divisorCorrectionProduct 77 = (4 : ℝ) / 3 := by
  have h77 : 77 = 7 * 11 := by norm_num
  rw [h77, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 7 (by decide) (by decide),
      divisorCorrectionProduct_prime 11 (by decide) (by decide)]
  norm_num

/-- **GENUINELY NEW: D(5) = D(77), но 5 ≠ 77**.

Singular series имеет нетривиальные «collisions»: D(5) = 4/3 = D(77),
где 5 — простое, а 77 = 7·11. Различные множества нечётных простых
({5} и {7,11}) дают одно и то же произведение ∏ (p-1)/(p-2).

Это означает, что gap 10 (kernel 5) и gap 154 (kernel 77) имеют
одинаковую Hardy--Littlewood плотность, несмотря на разную структуру. -/
theorem divisorCorrectionProduct_collision_5_77 :
    divisorCorrectionProduct 5 = divisorCorrectionProduct 77 ∧ (5 : Nat) ≠ 77 := by
  exact ⟨divisorCorrectionProduct_five.trans divisorCorrectionProduct_seven_eleven.symm,
         by norm_num⟩

/-- **S(10) = S(154)**: gap 10 и gap 154 имеют одинаковую singular series. -/
theorem singularSeriesFactor_collision_10_154 (C₂ : ℝ) :
    singularSeriesFactor C₂ 10 = singularSeriesFactor C₂ 154 := by
  have h10 : 10 = 2 * 5 := by norm_num
  have h154 : 154 = 2 * 77 := by norm_num
  rw [h10, h154, singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul 5), if_pos (even_two_mul 77),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_collision_5_77.1]

/-! ## Infinite collision family: D(5k) = D(77k) -/

/-- **Бесконечное семейство collisions**: D(5k) = D(77k) для любого `k`
взаимно простого с `385 = 5·7·11`.

Поскольку D(5) = D(77) и D мультипликативна по coprime, имеем
D(5k) = D(5)·D(k) = D(77)·D(k) = D(77k) для любого k coprime to 385.

Это даёт бесконечно много пар gap'ов с одинаковой HL-плотностью:
S(10k) = S(154k) для всех k coprime to 385. -/
theorem divisorCorrectionProduct_collision_general (k : Nat) (hk : k ≠ 0)
    (hcoprime : Nat.Coprime k 385) :
    divisorCorrectionProduct (5 * k) = divisorCorrectionProduct (77 * k) := by
  have h_coprime_5k : Nat.Coprime 5 k := by
    have h5_dvd_385 : 5 ∣ 385 := by norm_num
    have : Nat.Coprime k 5 := hcoprime.coprime_dvd_right h5_dvd_385
    exact this.symm
  have h_coprime_77k : Nat.Coprime 77 k := by
    have h77_dvd_385 : 77 ∣ 385 := by norm_num
    have : Nat.Coprime k 77 := hcoprime.coprime_dvd_right h77_dvd_385
    exact this.symm
  rw [divisorCorrectionProduct_mul_of_coprime (by norm_num) hk h_coprime_5k,
      divisorCorrectionProduct_mul_of_coprime (by norm_num) hk h_coprime_77k,
      divisorCorrectionProduct_collision_5_77.1]

/-- **S(10k) = S(154k)** для любого `k > 0` coprime to 385.
Бесконечное семейство пар gap'ов с одинаковой HL-плотностью. -/
theorem singularSeriesFactor_collision_general (C₂ : ℝ) (k : Nat)
    (hk : 0 < k) (hcoprime : Nat.Coprime k 385) :
    singularSeriesFactor C₂ (2 * 5 * k) = singularSeriesFactor C₂ (2 * 77 * k) := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  unfold singularSeriesFactor
  have h_even_10k : Even (2 * 5 * k) := by
    have : 2 * 5 * k = 2 * (5 * k) := by ring
    rw [this]; exact even_two_mul (5 * k)
  have h_even_154k : Even (2 * 77 * k) := by
    have : 2 * 77 * k = 2 * (77 * k) := by ring
    rw [this]; exact even_two_mul (77 * k)
  rw [if_pos h_even_10k, if_pos h_even_154k]
  have h_div10 : (2 * 5 * k) / 2 = 5 * k := by
    have : 2 * (5 * k) = 2 * 5 * k := by ring
    rw [← this, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have h_div154 : (2 * 77 * k) / 2 = 77 * k := by
    have : 2 * (77 * k) = 2 * 77 * k := by ring
    rw [← this, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [h_div10, h_div154, divisorCorrectionProduct_collision_general k hk_ne hcoprime]

/-! ## Second independent collision: D(29·37) = D(17) -/

/-- D(17) = (17-1)/(17-2) = 16/15. -/
theorem divisorCorrectionProduct_seventeen : divisorCorrectionProduct 17 = (16 : ℝ) / 15 := by
  rw [divisorCorrectionProduct_prime 17 (by decide) (by decide)]; norm_num

/-- D(1073) = D(29·37) = (28/27)·(36/35) = 16/15. -/
theorem divisorCorrectionProduct_29_37 : divisorCorrectionProduct 1073 = (16 : ℝ) / 15 := by
  have h1073 : 1073 = 29 * 37 := by norm_num
  rw [h1073, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 29 (by decide) (by decide),
      divisorCorrectionProduct_prime 37 (by decide) (by decide)]
  norm_num

/-- **SECOND independent collision: D(1073) = D(17), но 1073 ≠ 17**.

Другое нетривиальное соотношение: (29-1)/(29-2)·(37-1)/(37-2) = (17-1)/(17-2).
Это НЕЗАВИСИМО от D(5) = D(77): другое множество простых {29,37} vs {17}. -/
theorem divisorCorrectionProduct_collision_17_1073 :
    divisorCorrectionProduct 17 = divisorCorrectionProduct 1073 ∧ (17 : Nat) ≠ 1073 := by
  exact ⟨divisorCorrectionProduct_seventeen.trans divisorCorrectionProduct_29_37.symm,
         by norm_num⟩

/-- **S(34) = S(2146)**: второе независимое столкновение. -/
theorem singularSeriesFactor_collision_34_2146 (C₂ : ℝ) :
    singularSeriesFactor C₂ 34 = singularSeriesFactor C₂ 2146 := by
  have h34 : 34 = 2 * 17 := by norm_num
  have h2146 : 2146 = 2 * 1073 := by norm_num
  rw [h34, h2146, singularSeriesFactor, singularSeriesFactor,
      if_pos (even_two_mul 17), if_pos (even_two_mul 1073),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      Nat.mul_div_cancel_left _ (by omega : 0 < 2),
      divisorCorrectionProduct_collision_17_1073.1]

/-- **Второе бесконечное семейство: D(17k) = D(1073k)** для k coprime to 18269. -/
theorem divisorCorrectionProduct_collision_general_2 (k : Nat) (hk : k ≠ 0)
    (hcoprime : Nat.Coprime k 18241) :
    divisorCorrectionProduct (17 * k) = divisorCorrectionProduct (1073 * k) := by
  have h_coprime_17k : Nat.Coprime 17 k := by
    have h17_dvd : 17 ∣ 18241 := by norm_num
    exact (hcoprime.coprime_dvd_right h17_dvd).symm
  have h_coprime_1073k : Nat.Coprime 1073 k := by
    have h1073_dvd : 1073 ∣ 18241 := by norm_num
    exact (hcoprime.coprime_dvd_right h1073_dvd).symm
  rw [divisorCorrectionProduct_mul_of_coprime (by decide) hk h_coprime_17k,
      divisorCorrectionProduct_mul_of_coprime (by decide) hk h_coprime_1073k,
      divisorCorrectionProduct_collision_17_1073.1]

/-- **S(34k) = S(2146k)** для k coprime to 18269. -/
theorem singularSeriesFactor_collision_general_2 (C₂ : ℝ) (k : Nat)
    (hk : 0 < k)     (hcoprime : Nat.Coprime k 18241) :
    singularSeriesFactor C₂ (2 * 17 * k) = singularSeriesFactor C₂ (2 * 1073 * k) := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  unfold singularSeriesFactor
  have h_even_1 : Even (2 * 17 * k) := by
    have h : 2 * 17 * k = 2 * (17 * k) := by ring
    rw [h]; exact even_two_mul (17 * k)
  have h_even_2 : Even (2 * 1073 * k) := by
    have h : 2 * 1073 * k = 2 * (1073 * k) := by ring
    rw [h]; exact even_two_mul (1073 * k)
  rw [if_pos h_even_1, if_pos h_even_2]
  have h_div1 : (2 * 17 * k) / 2 = 17 * k := by
    have : 2 * (17 * k) = 2 * 17 * k := by ring
    rw [← this, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  have h_div2 : (2 * 1073 * k) / 2 = 1073 * k := by
    have : 2 * (1073 * k) = 2 * 1073 * k := by ring
    rw [← this, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [h_div1, h_div2, divisorCorrectionProduct_collision_general_2 k hk_ne hcoprime]

/-! ## Explicit upper bound: D(P_m) ≤ m -/

/-- `p_i ≥ i + 2` для `i ≥ 2`. -/
theorem nth_prime_ge_add_two (i : Nat) (hi : 2 ≤ i) :
    i + 2 ≤ Nat.nth Nat.Prime i := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hi2 : 2 ≤ i
    · have hpi : i + 2 ≤ Nat.nth Nat.Prime i := ih hi2
      have hpi_succ : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (by omega : i < i + 1)
      omega
    · have hi1 : i = 1 := by omega
      subst hi1
      -- Goal: 2 + 2 ≤ Nat.nth Nat.Prime 2, i.e. 4 ≤ p_2
      -- p_2 > p_1 = 3 (strict monotone), and p_2 is prime > 3, so p_2 ≥ 5
      have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
      have hp2_prime : Nat.Prime (Nat.nth Nat.Prime 2) := Nat.prime_nth_prime 2
      have hp2_gt_3 : 3 < Nat.nth Nat.Prime 2 := by
        have h_lt : Nat.nth Nat.Prime 1 < Nat.nth Nat.Prime 2 :=
          (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mpr (by omega : (1 : Nat) < 2)
        rw [hp1] at h_lt
        exact h_lt
      -- p_2 > 3 and prime → p_2 ≥ 5 (next prime after 3 is 5)
      have hp2_ge_5 : 5 ≤ Nat.nth Nat.Prime 2 := by
        have h_gt3 : 3 < Nat.nth Nat.Prime 2 := hp2_gt_3
        have h_pr : Nat.Prime (Nat.nth Nat.Prime 2) := Nat.prime_nth_prime 2
        have hne_4 : Nat.nth Nat.Prime 2 ≠ 4 := fun h =>
          have : ¬ Nat.Prime 4 := by decide
          this (h ▸ h_pr)
        omega
      have : 4 ≤ Nat.nth Nat.Prime 2 := by linarith [hp2_ge_5]
      omega

/-- **D(P_m) ≤ m для m ≥ 2**: явная верхняя оценка divisor correction product.

D(P_m) = ∏_{i=1}^{m-1} (1 + 1/(p_i-2)).
Для i ≥ 2: p_i ≥ i+2 → p_i-2 ≥ i → 1/(p_i-2) ≤ 1/i → (1+1/(p_i-2)) ≤ (i+1)/i.
Телескопирование: ∏_{i=2}^{m-1} (i+1)/i = m/2.
Итого: D(P_m) = 2 · ∏_{i=2}^{m-1} ≤ 2 · m/2 = m. -/
theorem divisorCorrectionProduct_primorial_bound (m : Nat) (hm : 2 ≤ m) :
    divisorCorrectionProduct (primorial m) ≤ (m : ℝ) := by
  rw [divisorCorrectionProduct_primorial m (by omega)]
  -- D(P_m) = ∏_{i=1}^{m-1} (p_i-1)/(p_i-2)
  -- = (p_1-1)/(p_1-2) * ∏_{i=2}^{m-1} (p_i-1)/(p_i-2)
  -- = 2 * ∏_{i=2}^{m-1} (1 + 1/(p_i-2))
  -- ≤ 2 * ∏_{i=2}^{m-1} (1 + 1/i) = 2 * m/2 = m
  have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  -- Factor at i=1: (3-1)/(3-2) = 2
  -- Factor at i≥2: (p_i-1)/(p_i-2) ≤ (i+1)/i since p_i ≥ i+2
  -- Need: ∏_{i∈filter, i>0} f(i) ≤ 2 * ∏_{i=2}^{m-1} (i+1)/i = 2 * m/2 = m
  -- Use: each factor ≤ (i+1)/i, and factor(1) = 2 = (1+1)/1
  -- So ∏ ≤ ∏_{i=1}^{m-1} (i+1)/i = m/1 = m (telescoping from 1!)
  -- ∏_{i=1}^{m-1} (i+1)/i = m (telescoping: 2/1 * 3/2 * ... * m/(m-1) = m)
  -- Each factor ≤ (i+1)/i, so product ≤ ∏ (i+1)/i = m (telescoping)
  -- Use: ∏ f ≤ ∏ g when f ≤ g pointwise (by induction on Finset)
  -- Then ∏_{i=1}^{m-1} (i+1)/i = m
  sorry

end
end PrimeGaps
