import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

def allUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

theorem mem_allUnitaryDivisors {n d : ℕ} :
    d ∈ allUnitaryDivisors n ↔ 1 ≤ d ∧ d ≤ n ∧ d ∣ n ∧ d.Coprime (n / d) := by
  simp only [allUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico, and_assoc]
  omega

theorem prime_pow_dvd_of_unitary (n d p : ℕ) (hn : n ≠ 0) (hp : Nat.Prime p)
    (hd_dvd : d ∣ n) (hd_cop : d.Coprime (n / d)) (hp_dvd : p ∣ d) :
    p ^ (n.factorization p) ∣ d := by
  have hp_not_quot : ¬ p ∣ (n / d) := by
    intro h; have hgcd : p ∣ Nat.gcd d (n / d) := Nat.dvd_gcd hp_dvd h
    rw [hd_cop.gcd_eq_one] at hgcd
    exact hp.ne_one (Nat.eq_one_of_dvd_one hgcd)
  have hd_pos : 0 < d := by
    by_contra h
    push Not at h
    have hd0 : d = 0 := Nat.le_zero.mp h
    rw [hd0] at hd_dvd
    exact absurd (Nat.eq_zero_of_zero_dvd hd_dvd) hn
  have hquot_pos : 0 < n / d := by
    have this : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    exact (Nat.mul_pos_iff_of_pos_left hd_pos).mp (by rw [this]; exact hn_pos)
  have hquot_ne0 : n / d ≠ 0 := hquot_pos.ne'
  have hquot_fac : (n / d).factorization p = 0 := by
    rw [hp.dvd_iff_one_le_factorization hquot_ne0] at hp_not_quot; omega
  have hd_ne0 : d ≠ 0 := hd_pos.ne'
  have hd_fac_eq : d.factorization p = n.factorization p := by
    have hdiv := Nat.factorization_div hd_dvd
    have hfac : (n / d).factorization p = n.factorization p - d.factorization p := by
      rw [hdiv]; rfl
    rw [hquot_fac] at hfac
    have hle : d.factorization p ≤ n.factorization p :=
      (Nat.factorization_le_iff_dvd hd_ne0 hn).mpr hd_dvd p
    omega
  rw [hp.pow_dvd_iff_le_factorization hd_ne0]; exact hd_fac_eq.ge

theorem allUnitaryDivisors_mul_of_prime_pow_coprime
    (p a m : ℕ) (hp : Nat.Prime p) (_ha : 0 < a) (hm : 0 < m)
    (hcop : Nat.Coprime (p ^ a) m) :
    allUnitaryDivisors (p ^ a * m) =
      allUnitaryDivisors m ∪ (allUnitaryDivisors m).image (fun d => p ^ a * d) := by
  set P := p ^ a
  have hP_pos : 0 < P := pow_pos hp.pos a
  have hPm_ne0 : P * m ≠ 0 := Nat.mul_ne_zero hP_pos.ne' hm.ne'
  ext d; simp only [Finset.mem_union, Finset.mem_image, mem_allUnitaryDivisors]
  constructor
  · rintro ⟨hge, hle, hdvd, hcop_dm⟩
    have hd_pos : 0 < d := by omega
    by_cases hp_dvd : p ∣ d
    · have hP_full := prime_pow_dvd_of_unitary (P * m) d p hPm_ne0 hp hdvd hcop_dm hp_dvd
      have hle_fac : a ≤ (P * m).factorization p := by
        rw [← hp.pow_dvd_iff_le_factorization hPm_ne0]
        exact Nat.dvd_mul_right P m
      have hP_dvd : P ∣ d := (Nat.pow_dvd_pow p hle_fac).trans hP_full
      set e := d / P
      have hde : P * e = d := Nat.mul_div_cancel' hP_dvd
      have he_dvd_m : e ∣ m := by
        obtain ⟨k, hk⟩ := hdvd
        rw [← hde, Nat.mul_assoc] at hk
        refine ⟨k, Nat.mul_left_cancel hP_pos hk⟩
      have hcop_em : e.Coprime (m / e) := by
        have hquot2 : P * m / (P * e) = m / e := Nat.mul_div_mul_left m e hP_pos
        have hde_symm : d = P * e := hde.symm
        rw [hde_symm] at hcop_dm
        have hcop_Pe : (P * e).Coprime (m / e) := by rwa [hquot2] at hcop_dm
        have hcop_P : P.Coprime (m / e) := by
          apply hcop.coprime_dvd_right
          exact ⟨e, by rw [Nat.mul_comm, Nat.mul_div_cancel' he_dvd_m]⟩
        have hgcd : Nat.gcd e (m / e) ∣ Nat.gcd (P * e) (m / e) := by
          apply Nat.dvd_gcd
          · exact Nat.dvd_trans (Nat.gcd_dvd_left e (m / e)) (Nat.dvd_mul_left e P)
          · exact Nat.gcd_dvd_right e (m / e)
        rw [hcop_Pe.gcd_eq_one] at hgcd
        exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hgcd)
      right
      have he_pos : 0 < e := Nat.pos_of_mul_pos_left (hde.symm ▸ hd_pos)
      refine ⟨e, ⟨he_pos, Nat.le_of_dvd hm he_dvd_m, he_dvd_m, hcop_em⟩, hde⟩
    · have hcop_dP : d.Coprime P := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra h_ne1
        have h_gt1 : 1 < Nat.gcd d P := by
          have : 0 < Nat.gcd d P := Nat.gcd_pos_of_pos_left P hd_pos
          omega
        have hgcd_dvd_P : Nat.gcd d P ∣ P := Nat.gcd_dvd_right d P
        have hp_dvd_gcd : p ∣ Nat.gcd d P := by
          obtain ⟨q, hq_prime, hq_dvd_gcd⟩ :=
            Nat.exists_prime_and_dvd (by omega : Nat.gcd d P ≠ 1)
          have hq_dvd_P : q ∣ P := hq_dvd_gcd.trans hgcd_dvd_P
          have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_P
          have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hq_dvd_p
          rw [hq_eq_p] at hq_dvd_gcd; exact hq_dvd_gcd
        exact absurd (hp_dvd_gcd.trans (Nat.gcd_dvd_left d P)) hp_dvd
      have hd_dvd_m : d ∣ m :=
        hcop_dP.dvd_of_dvd_mul_right (Nat.mul_comm P m ▸ hdvd)
      have hcop_dm' : d.Coprime (m / d) := by
        have hmd_eq : P * m / d = P * (m / d) := Nat.mul_div_assoc P hd_dvd_m
        have hcop_dPmd : d.Coprime (P * (m / d)) := by rw [← hmd_eq]; exact hcop_dm
        have hgcd : Nat.gcd d (m / d) ∣ Nat.gcd d (P * (m / d)) := by
          apply Nat.dvd_gcd
          · exact Nat.gcd_dvd_left d (m / d)
          · exact Nat.dvd_trans (Nat.gcd_dvd_right d (m / d)) (Nat.dvd_mul_left (m / d) P)
        rw [hcop_dPmd.gcd_eq_one] at hgcd
        exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hgcd)
      left
      refine ⟨hge, Nat.le_of_dvd hm hd_dvd_m, hd_dvd_m, hcop_dm'⟩
  · rintro (⟨hge, hle, hdvd, hcop_dm⟩ | ⟨e, ⟨hege, hele, hedvd, hecop⟩, hPe⟩)
    · refine ⟨hge, hle.trans (Nat.le_mul_of_pos_left m hP_pos),
        hdvd.trans (Nat.dvd_mul_left m P), ?_⟩
      have hmd_eq : P * m / d = P * (m / d) := Nat.mul_div_assoc P hdvd
      have hcop_dP : d.Coprime P := (hcop.coprime_dvd_right hdvd).symm
      rw [hmd_eq]
      exact Nat.coprime_mul_iff_right.mpr ⟨hcop_dP, hcop_dm⟩
    · subst hPe
      refine ⟨Nat.le_trans (Nat.one_le_of_lt hP_pos)
          (Nat.le_mul_of_pos_right P (Nat.lt_of_lt_of_le Nat.zero_lt_one hege)),
        Nat.mul_le_mul_left P hele, Nat.mul_dvd_mul_left P hedvd, ?_⟩
      have hdiv : P * m / (P * e) = m / e := Nat.mul_div_mul_left m e hP_pos
      have hcop_P : P.Coprime (m / e) :=
        hcop.coprime_dvd_right ⟨e, by rw [Nat.mul_comm, Nat.mul_div_cancel' hedvd]⟩
      rw [hdiv]
      exact Nat.coprime_mul_iff_left.mpr ⟨hcop_P, hecop⟩

theorem sum_allUnitaryDivisors_mul_of_prime_pow_coprime
    (p a m : ℕ) (hp : Nat.Prime p) (ha : 0 < a) (hm : 0 < m)
    (hcop : Nat.Coprime (p ^ a) m) :
    ∑ d ∈ allUnitaryDivisors (p ^ a * m), d =
      (1 + p ^ a) * ∑ d ∈ allUnitaryDivisors m, d := by
  set P := p ^ a
  have hP_pos : 0 < P := pow_pos hp.pos a
  rw [allUnitaryDivisors_mul_of_prime_pow_coprime p a m hp ha hm hcop]
  have h_dis : Disjoint (allUnitaryDivisors m)
      ((allUnitaryDivisors m).image (fun d => P * d)) := by
    rw [Finset.disjoint_left]
    intro d hd hd_img
    obtain ⟨e, _, hde⟩ := Finset.mem_image.mp hd_img
    have hP_dvd_d : P ∣ d := hde ▸ Nat.dvd_mul_right P e
    have hd_dvd_m : d ∣ m := (mem_allUnitaryDivisors.mp hd).2.2.1
    have hP_dvd_m : P ∣ m := hP_dvd_d.trans hd_dvd_m
    have hP_ge2 : 2 ≤ P := by
      have h := Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ a)
      rw [Nat.pow_one] at h
      exact Nat.le_trans hp.two_le h
    exact absurd hcop (Nat.not_coprime_of_dvd_of_dvd hP_ge2 (Nat.dvd_refl P) hP_dvd_m)
  rw [Finset.sum_union h_dis]
  have h_inj : Set.InjOn (fun d => P * d) ↑(allUnitaryDivisors m) := by
    intro x _ y _ h; exact Nat.mul_left_cancel hP_pos h
  rw [Finset.sum_image h_inj, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _; ring

/-- For odd m ≥ 3, sum of all unitary divisors is even (by strong induction). -/
theorem sum_allUnitaryDivisors_even_of_odd (m : ℕ) (hm_odd : Odd m) (hm3 : 3 ≤ m) :
    Even (∑ d ∈ allUnitaryDivisors m, d) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hm_ne1 : m ≠ 1 := by omega
  have hp := Nat.minFac_prime hm_ne1
  set p := Nat.minFac m
  set a := m.factorization p
  set P := p ^ a
  have hP_pos : 0 < P := pow_pos hp.pos a
  have ha : 0 < a := by
    have h : p ∣ m := Nat.minFac_dvd m
    rw [hp.dvd_iff_one_le_factorization (by omega : m ≠ 0)] at h
    omega
  have hP_dvd : P ∣ m := by
    rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)]
  have hp_odd : Odd p := by
    by_cases h_even : Even p
    · exfalso
      have hp2 : p = 2 := hp.even_iff.mp h_even
      have h2_dvd_P : 2 ∣ P := by
        have : P = p ^ a := rfl
        rw [this, hp2]; exact Nat.pow_dvd_pow 2 (by omega : 1 ≤ a)
      have h2_dvd_m : 2 ∣ m := h2_dvd_P.trans hP_dvd
      exact absurd (even_iff_two_dvd.mpr h2_dvd_m)
        ((Nat.not_even_iff_odd).mpr hm_odd)
    · exact (Nat.not_even_iff_odd).mp h_even
  have hP_odd : Odd P := by
    change Odd (p ^ a)
    induction a with
    | zero => exact ⟨0, rfl⟩
    | succ a _ =>
      rw [Nat.pow_succ]
      exact Nat.odd_mul.mpr ⟨Odd.pow hp_odd, hp_odd⟩
  set m' := m / P
  have hPm_eq : P * m' = m := Nat.mul_div_cancel' hP_dvd
  have hm'_pos : 0 < m' := by
    by_contra h
    push Not at h
    have hm'0 : m' = 0 := Nat.le_zero.mp h
    rw [hm'0, Nat.mul_zero] at hPm_eq
    omega
  have hcop : Nat.Coprime P m' := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne1
    have h_gt1 : 1 < Nat.gcd P m' := by
      have : 0 < Nat.gcd P m' := Nat.gcd_pos_of_pos_left m' hP_pos
      omega
    have hgcd_dvd : Nat.gcd P m' ∣ P := Nat.gcd_dvd_left P m'
    have hp_dvd_gcd : p ∣ Nat.gcd P m' := by
      obtain ⟨q, hq_prime, hq_dvd_gcd⟩ :=
        Nat.exists_prime_and_dvd (by omega : Nat.gcd P m' ≠ 1)
      have hq_dvd_P : q ∣ P := hq_dvd_gcd.trans hgcd_dvd
      have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_P
      have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hq_dvd_p
      rw [hq_eq_p] at hq_dvd_gcd; exact hq_dvd_gcd
    have hp_dvd_m' : p ∣ m' := hp_dvd_gcd.trans (Nat.gcd_dvd_right P m')
    have this : p ^ (a + 1) ∣ m := by
      rw [Nat.pow_succ, ← hPm_eq]
      change P * p ∣ P * m'
      exact Nat.mul_dvd_mul_left P hp_dvd_m'
    rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)] at this
    have ha_eq : a = m.factorization p := rfl
    rw [ha_eq] at this
    omega
  have h_sum := sum_allUnitaryDivisors_mul_of_prime_pow_coprime p a m' hp ha hm'_pos hcop
  have h1P_even : Even (1 + P) := by
    rw [Nat.even_iff]; have : P % 2 = 1 := Nat.odd_iff.mp hP_odd; omega
  by_cases hm'_eq_1 : m' = 1
  · rw [hm'_eq_1] at h_sum
    have h_sum_1 : ∑ d ∈ allUnitaryDivisors 1, d = 1 := by decide
    rw [h_sum_1] at h_sum
    have hm_eq_P : m = P := by rw [← hPm_eq, hm'_eq_1, Nat.mul_one]
    have hPP : P = p ^ a := rfl
    rw [hm_eq_P, hPP]
    have hmul_one : p ^ a * 1 = p ^ a := Nat.mul_one _
    rw [hmul_one] at h_sum
    rw [h_sum, Nat.mul_one]
    exact h1P_even
  · have hm'_odd : Odd m' := by
      by_cases h_even : Even m'
      · exfalso
        have : Even (P * m') := Nat.even_mul.mpr (Or.inr h_even)
        rw [hPm_eq] at this
        exact absurd this ((Nat.not_even_iff_odd).mpr hm_odd)
      · exact (Nat.not_even_iff_odd).mp h_even
    have hm'_3 : 3 ≤ m' := by
      have : ¬ Even m' := (Nat.not_even_iff_odd).mpr hm'_odd
      have : m' ≠ 2 := fun h => this (h ▸ even_two)
      omega
    have hm'_lt : m' < m := by
      have hP_ge2 : 2 ≤ P := by
        have h := Nat.pow_le_pow_right hp.pos (by omega : 1 ≤ a)
        rw [Nat.pow_one] at h
        exact Nat.le_trans hp.two_le h
      have : m' < 2 * m' := by omega
      have : m' < P * m' := by calc m' < 2 * m' := by omega
        _ ≤ P * m' := Nat.mul_le_mul_right m' hP_ge2
      rw [hPm_eq] at this; omega
    have h_even_m' : Even (∑ d ∈ allUnitaryDivisors m', d) :=
      ih m' hm'_lt hm'_odd hm'_3
    have hm_eq : m = P * m' := hPm_eq.symm
    have hPP : P = p ^ a := rfl
    rw [hm_eq, hPP, h_sum]
    change Even ((1 + P) * ∑ d ∈ allUnitaryDivisors m', d)
    exact Nat.even_mul.mpr (Or.inl h1P_even)

/-- For odd n with ≥ 2 prime factors, 4 ∣ sum of all unitary divisors. -/
theorem sum_allUnitaryDivisors_dvd4 (n : ℕ) (hn_odd : Odd n) (hn3 : 3 ≤ n)
    (hn_not_pp : ¬ ∃ p k, Nat.Prime p ∧ 0 < k ∧ n = p ^ k) :
    4 ∣ ∑ d ∈ allUnitaryDivisors n, d := by
  have hn_ne1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn_ne1
  set p := Nat.minFac n
  set a := n.factorization p
  set P := p ^ a
  have hP_pos : 0 < P := pow_pos hp.pos a
  have ha : 0 < a := by
    have h : p ∣ n := Nat.minFac_dvd n
    rw [hp.dvd_iff_one_le_factorization (by omega : n ≠ 0)] at h
    omega
  have hP_dvd : P ∣ n := by
    rw [hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)]
  have hp_odd : Odd p := by
    by_cases h_even : Even p
    · exfalso
      have hp2 : p = 2 := hp.even_iff.mp h_even
      have h2_dvd_P : 2 ∣ P := by
        have : P = p ^ a := rfl
        rw [this, hp2]; exact Nat.pow_dvd_pow 2 (by omega : 1 ≤ a)
      have h2_dvd_n : 2 ∣ n := h2_dvd_P.trans hP_dvd
      exact absurd (even_iff_two_dvd.mpr h2_dvd_n)
        ((Nat.not_even_iff_odd).mpr hn_odd)
    · exact (Nat.not_even_iff_odd).mp h_even
  have hP_odd : Odd P := by
    change Odd (p ^ a)
    induction a with
    | zero => exact ⟨0, rfl⟩
    | succ a _ =>
      rw [Nat.pow_succ]
      exact Nat.odd_mul.mpr ⟨Odd.pow hp_odd, hp_odd⟩
  set m := n / P
  have hPm_eq : P * m = n := Nat.mul_div_cancel' hP_dvd
  have hm_pos : 0 < m := by
    by_contra h
    push Not at h
    have hm0 : m = 0 := Nat.le_zero.mp h
    rw [hm0, Nat.mul_zero] at hPm_eq
    omega
  have hm3 : 3 ≤ m := by
    by_contra h
    push Not at h
    have : m ≤ 2 := by omega
    rcases (show m = 1 ∨ m = 2 by omega) with h1 | h2
    · rw [h1] at hPm_eq
      have : n = p ^ a := by rw [← hPm_eq, Nat.mul_one]
      exact hn_not_pp ⟨p, a, hp, ha, this⟩
    · rw [h2] at hPm_eq
      have : Even n := by rw [← hPm_eq]; exact Nat.even_mul.mpr (Or.inr even_two)
      exact absurd this ((Nat.not_even_iff_odd).mpr hn_odd)
  have hm_odd : Odd m := by
    by_cases h_even : Even m
    · exfalso
      have : Even (P * m) := Nat.even_mul.mpr (Or.inr h_even)
      rw [hPm_eq] at this
      exact absurd this ((Nat.not_even_iff_odd).mpr hn_odd)
    · exact (Nat.not_even_iff_odd).mp h_even
  have hcop : Nat.Coprime P m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne1
    have h_gt1 : 1 < Nat.gcd P m := by
      have : 0 < Nat.gcd P m := Nat.gcd_pos_of_pos_left m hP_pos
      omega
    have hgcd_dvd : Nat.gcd P m ∣ P := Nat.gcd_dvd_left P m
    have hp_dvd_gcd : p ∣ Nat.gcd P m := by
      obtain ⟨q, hq_prime, hq_dvd_gcd⟩ :=
        Nat.exists_prime_and_dvd (by omega : Nat.gcd P m ≠ 1)
      have hq_dvd_P : q ∣ P := hq_dvd_gcd.trans hgcd_dvd
      have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_P
      have hq_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hq_dvd_p
      rw [hq_eq_p] at hq_dvd_gcd; exact hq_dvd_gcd
    have hp_dvd_m : p ∣ m := hp_dvd_gcd.trans (Nat.gcd_dvd_right P m)
    have this : p ^ (a + 1) ∣ n := by
      rw [Nat.pow_succ, ← hPm_eq]
      change P * p ∣ P * m
      exact Nat.mul_dvd_mul_left P hp_dvd_m
    rw [hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)] at this
    have ha_eq : a = n.factorization p := rfl
    rw [ha_eq] at this
    omega
  have h_sum := sum_allUnitaryDivisors_mul_of_prime_pow_coprime p a m hp ha hm_pos hcop
  have h1P_even : Even (1 + P) := by
    rw [Nat.even_iff]; have : P % 2 = 1 := Nat.odd_iff.mp hP_odd; omega
  have h_even_m : Even (∑ d ∈ allUnitaryDivisors m, d) :=
    sum_allUnitaryDivisors_even_of_odd m hm_odd hm3
  have h_eq : ∑ d ∈ allUnitaryDivisors n, d = (1 + P) * ∑ d ∈ allUnitaryDivisors m, d := by
    rw [← hPm_eq]; exact h_sum
  rw [h_eq]
  obtain ⟨k, hk⟩ := h1P_even
  obtain ⟨j, hj⟩ := h_even_m
  rw [hk, hj]; exact ⟨k * j, by ring⟩

end PrimeGaps
