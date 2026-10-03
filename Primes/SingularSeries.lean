import Mathlib
import Primes.Basic
import Primes.Wheel

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace PrimeGaps

noncomputable section

open scoped BigOperators

/-! ## Divisor correction product D(k) = ∏_{p|k, p>2} (p-1)/(p-2) -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- `Finset.one_le_prod` replacement for `ℝ` (mathlib 4.34 requires `MulLeftMono`,
not satisfiable for `ℝ`). -/
private lemma one_le_prod_real {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      calc 1 = 1 * 1 := by ring
        _ ≤ f a * 1 := mul_le_mul_of_nonneg_right (h a (Finset.mem_insert_self a s)) (by norm_num)
        _ ≤ f a * ∏ i ∈ s, f i :=
            mul_le_mul_of_nonneg_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
              (by linarith [h a (Finset.mem_insert_self a s)])

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- `Finset.prod_le_prod` replacement for `ℝ`. -/
private lemma prod_le_prod_real {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ih' := ih (fun i hi => hnn i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
      have hnn_a := hnn a (Finset.mem_insert_self a s)
      have hfg_a := hfg a (Finset.mem_insert_self a s)
      have hpg : 0 ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg fun i hi =>
          le_trans (hnn i (Finset.mem_insert_of_mem hi))
            (hfg i (Finset.mem_insert_of_mem hi))
      have hpfa : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi =>
        hnn i (Finset.mem_insert_of_mem hi)
      have hpga : 0 ≤ g a := le_trans hnn_a hfg_a
      exact mul_le_mul hfg_a ih' hpfa hpga


def divisorCorrectionProduct (k : Nat) : ℝ :=
  (Finset.range (k + 1)).prod fun p =>
    if Nat.Prime p ∧ 2 < p ∧ p ∣ k then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

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
    ext q; simp only [Finset.mem_filter, Finset.mem_singleton]
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
      simp only [Finset.mem_singleton] at hp; omega]; simp

theorem divisorCorrectionProduct_ge_one (k : Nat) : 1 ≤ divisorCorrectionProduct k := by
  rw [divisorCorrectionProduct_eq_primeFactors]
  apply one_le_prod_real
  rintro p hp
  have hp_real : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  rw [le_div_iff₀ (by linarith : 0 < (p : ℝ) - 2)]; linarith

/-! ## D monotonicity and primorial -/

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
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hxy
  rw [Finset.prod_image hinj]
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hirange, hlt⟩; refine ⟨hirange, ?_⟩
    by_cases hi : i = 0; · subst hi; rw [Nat.nth_prime_zero_eq_two] at hlt; omega
    · omega
  · rintro ⟨hirange, hipos⟩; refine ⟨hirange, ?_⟩
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hge : 1 ≤ i := by omega
    have hle : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime i :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_iff_le.mpr hge
    rw [h1] at hle; omega

theorem nth_prime_ge_add_two (i : Nat) (hi : 2 ≤ i) :
    i + 2 ≤ Nat.nth Nat.Prime i := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hi2 : 2 ≤ i
    · have hpi : i + 2 ≤ Nat.nth Nat.Prime i := ih hi2
      have hpi_succ : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (i + 1) :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mpr (by omega : i < i + 1)
      omega
    · have hi1 : i = 1 := by omega
      subst hi1
      norm_num

private lemma telescoping_product (m : Nat) (hm : 0 < m) :
    ((Finset.range m).filter (fun i => 0 < i)).prod
      (fun i => ((i : ℝ) + 1) / (i : ℝ)) = (m : ℝ) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      have h_empty : (Finset.range 1).filter (fun i => 0 < i) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro x hx hpos
        have hlt : x < 1 := Finset.mem_range.mp hx; omega
      rw [h_empty, Finset.prod_empty]; norm_num
    · have hm_pos : 0 < m := by omega
      have h_range_succ : Finset.range (m + 1) = insert m (Finset.range m) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert]; omega
      rw [h_range_succ]
      have h_insert : (insert m (Finset.range m)).filter (fun i => 0 < i) =
          insert m ((Finset.range m).filter (fun i => 0 < i)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
        constructor
        · rintro ⟨(rfl | hi), hpos⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hi, hpos⟩
        · rintro (rfl | ⟨hi, hpos⟩)
          · exact ⟨Or.inl rfl, by omega⟩
          · exact ⟨Or.inr hi, hpos⟩
      rw [h_insert]
      have h_not_mem : m ∉ (Finset.range m).filter (fun i => 0 < i) := by
        intro hmem; have : m < m := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1; omega
      rw [Finset.prod_insert h_not_mem, ih hm_pos, Nat.cast_add_one]; field_simp

/-- **D(P_m) ≤ m for m ≥ 2**: explicit upper bound for divisor correction product. -/
theorem divisorCorrectionProduct_primorial_bound (m : Nat) (hm : 2 ≤ m) :
    divisorCorrectionProduct (primorial m) ≤ (m : ℝ) := by
  rw [divisorCorrectionProduct_primorial m (by omega)]
  trans ((Finset.range m).filter (fun i => 0 < i)).prod
      (fun i => ((i : ℝ) + 1) / (i : ℝ))
  · apply prod_le_prod_real
    · intro i hi
      have hi_pos : 0 < i := (Finset.mem_filter.mp hi).2
      have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
      have hpi_ge3 : (3 : ℝ) ≤ Nat.nth Nat.Prime i := by
        have hge1 : 1 ≤ i := by omega
        have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
        have hle := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_iff_le.mpr hge1
        rw [hp1] at hle; exact_mod_cast hle
      exact div_nonneg (by linarith) (by linarith)
    · intro i hi
      have hi_pos : 0 < i := (Finset.mem_filter.mp hi).2
      have hi_lt_m : i < m := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      by_cases hi_ge_2 : 2 ≤ i
      · have hpi_bound : (i : ℝ) + 2 ≤ Nat.nth Nat.Prime i := by
          exact_mod_cast nth_prime_ge_add_two i hi_ge_2
        have hi_real : (0 : ℝ) < i := by exact_mod_cast hi_pos
        have hdenom1 : (0 : ℝ) < (Nat.nth Nat.Prime i : ℝ) - 2 := by linarith
        field_simp [hdenom1.ne', hi_real.ne']
        nlinarith [hpi_bound, hi_real]
      · have hi_eq_1 : i = 1 := by omega
        subst hi_eq_1
        have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
        rw [hp1]; norm_num
  · rw [telescoping_product m (by omega)]

/-! ## Singular series collisions: D(5) = D(77), D(17) = D(1073), D(65) = D(1001) -/

theorem divisorCorrectionProduct_five : divisorCorrectionProduct 5 = (4 : ℝ) / 3 := by
  rw [divisorCorrectionProduct_prime 5 (by decide) (by decide)]; norm_num

theorem divisorCorrectionProduct_seven_eleven : divisorCorrectionProduct 77 = (4 : ℝ) / 3 := by
  have h77 : 77 = 7 * 11 := by norm_num
  rw [h77, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 7 (by decide) (by decide),
      divisorCorrectionProduct_prime 11 (by decide) (by decide)]; norm_num

/-- **D(5) = D(77)**: singular series non-injectivity. First collision family. -/
theorem divisorCorrectionProduct_collision_general (k : Nat) (hk : k ≠ 0)
    (hcoprime : Nat.Coprime k 385) :
    divisorCorrectionProduct (5 * k) = divisorCorrectionProduct (77 * k) := by
  have h_c5 : Nat.Coprime 5 k := (hcoprime.coprime_dvd_right (by norm_num : 5 ∣ 385)).symm
  have h_c77 : Nat.Coprime 77 k := (hcoprime.coprime_dvd_right (by norm_num : 77 ∣ 385)).symm
  rw [divisorCorrectionProduct_mul_of_coprime (by norm_num) hk h_c5,
      divisorCorrectionProduct_mul_of_coprime (by norm_num) hk h_c77,
      divisorCorrectionProduct_five, divisorCorrectionProduct_seven_eleven]

theorem divisorCorrectionProduct_seventeen : divisorCorrectionProduct 17 = (16 : ℝ) / 15 := by
  rw [divisorCorrectionProduct_prime 17 (by decide) (by decide)]; norm_num

theorem divisorCorrectionProduct_29_37 : divisorCorrectionProduct 1073 = (16 : ℝ) / 15 := by
  have h1073 : 1073 = 29 * 37 := by norm_num
  rw [h1073, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 29 (by decide) (by decide),
      divisorCorrectionProduct_prime 37 (by decide) (by decide)]; norm_num

/-- **D(17) = D(1073)**: second independent collision family. -/
theorem divisorCorrectionProduct_collision_general_2 (k : Nat) (hk : k ≠ 0)
    (hcoprime : Nat.Coprime k 18241) :
    divisorCorrectionProduct (17 * k) = divisorCorrectionProduct (1073 * k) := by
  have h_c17 : Nat.Coprime 17 k := (hcoprime.coprime_dvd_right (by norm_num : 17 ∣ 18241)).symm
  have h_c1073 : Nat.Coprime 1073 k :=
    (hcoprime.coprime_dvd_right (by norm_num : 1073 ∣ 18241)).symm
  rw [divisorCorrectionProduct_mul_of_coprime (by decide) hk h_c17,
      divisorCorrectionProduct_mul_of_coprime (by decide) hk h_c1073,
      divisorCorrectionProduct_seventeen, divisorCorrectionProduct_29_37]

theorem divisorCorrectionProduct_five_thirteen : divisorCorrectionProduct 65 = (16 : ℝ) / 11 := by
  have h65 : 65 = 5 * 13 := by norm_num
  rw [h65, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 5 (by decide) (by decide),
      divisorCorrectionProduct_prime 13 (by decide) (by decide)]; norm_num

theorem divisorCorrectionProduct_seven_eleven_thirteen :
    divisorCorrectionProduct 1001 = (16 : ℝ) / 11 := by
  have h1001 : 1001 = 7 * 11 * 13 := by norm_num
  rw [h1001]
  have h_c7_143 : Nat.Coprime 7 143 := by decide
  rw [divisorCorrectionProduct_mul_of_coprime (by decide) (by decide) h_c7_143,
      divisorCorrectionProduct_prime 7 (by decide) (by decide)]
  have h143 : 143 = 11 * 13 := by norm_num
  rw [h143, divisorCorrectionProduct_mul_of_coprime (by decide) (by decide)
      ((Nat.coprime_primes (by decide) (by decide)).mpr (by decide)),
      divisorCorrectionProduct_prime 11 (by decide) (by decide),
      divisorCorrectionProduct_prime 13 (by decide) (by decide)]; norm_num

/-- **D(65) = D(1001)**: cross-cardinality collision (2 vs 3 odd prime factors). -/
theorem divisorCorrectionProduct_collision_general_3 (k : Nat) (hk : k ≠ 0)
    (hcoprime : Nat.Coprime k 5005) :
    divisorCorrectionProduct (65 * k) = divisorCorrectionProduct (1001 * k) := by
  have h_c65 : Nat.Coprime 65 k := (hcoprime.coprime_dvd_right (by norm_num : 65 ∣ 5005)).symm
  have h_c1001 : Nat.Coprime 1001 k :=
    (hcoprime.coprime_dvd_right (by norm_num : 1001 ∣ 5005)).symm
  rw [divisorCorrectionProduct_mul_of_coprime (by decide) hk h_c65,
      divisorCorrectionProduct_mul_of_coprime (by decide) hk h_c1001,
      divisorCorrectionProduct_five_thirteen,
      divisorCorrectionProduct_seven_eleven_thirteen]

end
end PrimeGaps
