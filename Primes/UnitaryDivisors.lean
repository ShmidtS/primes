import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

def allUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

theorem mem_allUnitaryDivisors {n d : ℕ} :
    d ∈ allUnitaryDivisors n ↔ 1 ≤ d ∧ d ≤ n ∧ d ∣ n ∧ d.Coprime (n / d) := by
  simp [allUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico]

theorem prime_pow_dvd_of_unitary (n d p : ℕ) (hn : n ≠ 0) (hp : Nat.Prime p)
    (hd_dvd : d ∣ n) (hd_cop : d.Coprime (n / d)) (hp_dvd : p ∣ d) :
    p ^ (n.factorization p) ∣ d := by
  have hp_not_quot : ¬ p ∣ (n / d) := by
    intro h; have : p ∣ Nat.gcd d (n / d) := Nat.dvd_gcd hp_dvd h
    rw [hd_cop.gcd_eq_one] at this; omega
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h] at hp_dvd; exact absurd hp_dvd hp.not_one)
  have hquot_pos : 0 < n / d := by
    have : d * (n / d) = n := Nat.div_mul_cancel hd_dvd
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    exact (Nat.mul_pos_iff_of_pos_left hd_pos).mp (by rw [this]; exact hn_pos)
  have hquot_ne0 : n / d ≠ 0 := hquot_pos.ne'
  have hquot_fac : (n / d).factorization p = 0 := by
    rw [hp.dvd_iff_one_le_factorization hquot_ne0] at hp_not_quot; omega
  have hd_ne0 : d ≠ 0 := hd_pos.ne'
  have hd_fac_eq : d.factorization p = n.factorization p := by
    have hdiv := Nat.factorization_div hd_dvd
    have : (n / d).factorization p = n.factorization p - d.factorization p := by
      rw [hdiv]; exact Finsupp.sub_apply
    rw [hquot_fac] at this; omega
  rw [hp.pow_dvd_iff_le_factorization hd_ne0]; exact hd_fac_eq.ge

theorem allUnitaryDivisors_mul_of_prime_pow_coprime
    (p a m : ℕ) (hp : Nat.Prime p) (ha : 0 < a) (hm : 0 < m)
    (hcop : Nat.Coprime (p ^ a) m) :
    allUnitaryDivisors (p ^ a * m) =
      allUnitaryDivisors m ∪ (allUnitaryDivisors m).image (fun d => p ^ a * d) := by
  set P := p ^ a
  have hP_pos : 0 < P := Nat.pow_pos hp.pos a
  have hPm_ne0 : P * m ≠ 0 := Nat.mul_ne_zero hP_pos.ne' hm.ne'
  ext d; simp only [Finset.mem_union, Finset.mem_image, mem_allUnitaryDivisors]
  constructor
  · rintro ⟨hge, hle, hdvd, hcop_dm⟩
    by_cases hp_dvd : p ∣ d
    · have hP_dvd := prime_pow_dvd_of_unitary (P * m) d p hPm_ne0 hp hdvd hcop_dm hp_dvd
      set e := d / P
      have hde : P * e = d := Nat.div_mul_cancel hP_dvd
      have he_dvd_m : e ∣ m := Nat.mul_left_cancel hP_pos.ne' (hde ▸ hdvd)
      have hcop_em : e.Coprime (m / e) := by
        have hquot : P * m / d = m / e := by rw [hde, Nat.mul_div_mul_left m e hP_pos]
        have hcop_Pe : (P * e).Coprime (m / e) := by rw [← hquot, ← hde]; exact hcop_dm
        have hcop_P : P.Coprime (m / e) := by
          apply hcop.symm.coprime_dvd_right
          exact ⟨e, by rw [Nat.mul_comm, Nat.div_mul_cancel he_dvd_m]⟩
        have hgcd : Nat.gcd e (m / e) ∣ Nat.gcd (P * e) (m / e) := by
          apply Nat.dvd_gcd
          · exact Nat.dvd_trans (Nat.gcd_dvd_left e (m / e)) (Nat.dvd_mul_right e P)
          · exact Nat.gcd_dvd_right e (m / e)
        rw [hcop_Pe.gcd_eq_one] at hgcd
        exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_one_of_dvd hgcd)
      right; refine ⟨e, ⟨?_, he_dvd_m, hcop_em⟩, hde⟩
      refine ⟨by omega, ?_⟩
      have : e * (m / e) = m := Nat.div_mul_cancel he_dvd_m; omega
    · -- p ∤ d → gcd(d, P) = 1 → d | m (Gauss) → d ∈ allUD(m)
      have hcop_dP : d.Coprime P := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra h_ne1
        have h_gt1 : 1 < Nat.gcd d P := by omega
        have hgcd_dvd_P : Nat.gcd d P ∣ P := Nat.gcd_dvd_right d P
        have hp_dvd_gcd : p ∣ Nat.gcd d P := by
          rcases hp.eq_one_or_self (Nat.gcd d P) hgcd_dvd_P with h1 | hself
          · omega
          · exact hself ▸ Nat.dvd_refl p
        exact absurd (hp_dvd_gcd.trans (Nat.gcd_dvd_left d P)) hp_dvd
      have hd_dvd_m : d ∣ m := hcop_dP.dvd_of_dvd_mul_right hdvd
      have hcop_dm' : d.Coprime (m / d) := by
        have hmd_eq : P * m / d = P * (m / d) := Nat.mul_div_assoc hdvd
        have hcop_dPmd : d.Coprime (P * (m / d)) := by rw [hmd_eq]; exact hcop_dm
        have hgcd : Nat.gcd d (m / d) ∣ Nat.gcd d (P * (m / d)) := by
          apply Nat.dvd_gcd
          · exact Nat.gcd_dvd_left d (m / d)
          · exact Nat.dvd_trans (Nat.gcd_dvd_right d (m / d)) (Nat.dvd_mul_right (m / d) P)
        rw [hcop_dPmd.gcd_eq_one] at hgcd
        exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_one_of_dvd hgcd)
      left
      refine ⟨by omega, ?_, hd_dvd_m, hcop_dm'⟩
      have : d * (m / d) = m := Nat.div_mul_cancel hd_dvd_m; omega
  · rintro (⟨hge, hle, hdvd, hcop⟩ | ⟨e, ⟨hege, hele, hedvd, hecop⟩, rfl⟩)
    · refine ⟨hge, Nat.le_mul_of_pos_left hm, hdvd.trans (Nat.dvd_mul_right P m), ?_⟩
      have hmd_eq : P * m / d = P * (m / d) := Nat.mul_div_assoc hdvd
      rw [hmd_eq]
      have hcop_dP : d.Coprime P := by
        apply hcop.symm.coprime_dvd_right
          (dvd := ⟨d, by rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]⟩)
      exact Nat.coprime_mul_iff_right.mpr ⟨hcop_dP, hcop⟩
    · refine ⟨by omega, Nat.mul_le_mul_left P hele, Nat.mul_dvd_mul_left P hedvd, ?_⟩
      have hdiv : P * m / (P * e) = m / e := Nat.mul_div_mul_left m e hP_pos
      rw [hdiv]
      have hcop_P : P.Coprime (m / e) := by
        apply hcop.symm.coprime_dvd_right
          (dvd := ⟨e, by rw [Nat.mul_comm, Nat.div_mul_cancel hedvd]⟩)
      exact Nat.coprime_mul_iff_left.mpr ⟨hcop_P, hecop⟩

theorem sum_allUnitaryDivisors_mul_of_prime_pow_coprime
    (p a m : ℕ) (hp : Nat.Prime p) (ha : 0 < a) (hm : 0 < m)
    (hcop : Nat.Coprime (p ^ a) m) :
    ∑ d ∈ allUnitaryDivisors (p ^ a * m), d =
      (1 + p ^ a) * ∑ d ∈ allUnitaryDivisors m, d := by
  set P := p ^ a
  have hP_pos : 0 < P := Nat.pow_pos hp.pos a
  rw [allUnitaryDivisors_mul_of_prime_pow_coprime p a m hp ha hm hcop]
  have h_dis : Disjoint (allUnitaryDivisors m) ((allUnitaryDivisors m).image (fun d => P * d)) := by
    rw [Finset.disjoint_left]
    intro d hd hd_img
    obtain ⟨e, _, hde⟩ := hd_img
    have hP_dvd_d : P ∣ d := hde ▸ Nat.dvd_mul_left P e
    have hd_dvd_m : d ∣ m := (mem_allUnitaryDivisors.mp hd).2.1
    have hP_dvd_m : P ∣ m := hP_dvd_d.trans hd_dvd_m
    have hP_ge2 : 2 ≤ P := Nat.le_trans (by omega : 2 ≤ p)
      (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ a))
    exact absurd hcop (Nat.not_coprime_of_dvd_of_dvd hP_ge2 hP_dvd_m (Nat.dvd_refl P))
  rw [Finset.sum_union h_dis]
  have h_inj : Set.InjOn (fun d => P * d) ↑(allUnitaryDivisors m) := by
    intro a_mem _ b_mem h; exact Nat.mul_left_cancel hP_pos.ne' h
  rw [Finset.sum_image h_inj, Finset.mul_sum]; ring

/-- For odd m ≥ 3, sum of all unitary divisors is even (by strong induction). -/
theorem sum_allUnitaryDivisors_even_of_odd (m : ℕ) (hm_odd : Odd m) (hm3 : 3 ≤ m) :
    Even (∑ d ∈ allUnitaryDivisors m, d) := by
  induction m using Nat.strongInductionOn with
  | _ m ih =>
  have hm_ne1 : m ≠ 1 := by omega
  have hp := Nat.minFac_prime hm_ne1
  set p := Nat.minFac m
  set a := m.factorization p
  set P := p ^ a
  have ha : 0 < a := by
    rw [hp.dvd_iff_one_le_factorization (by omega : m ≠ 0)]
    exact Nat.le_of_dvd (by omega) (Nat.minFac_dvd m)
  have hP_dvd : P ∣ m := by
    rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)]; exact le_rfl
  have hp_odd : Odd p := by
    by_cases h_even : Even p
    · exfalso; have : p = 2 := Nat.even_iff.mp h_even
      rw [this] at hP_dvd
      exact absurd (Nat.even_of_dvd (by omega : 2 ≤ p) hP_dvd) ((Nat.not_even_iff_odd).mpr hm_odd)
    · exact (Nat.not_even_iff_odd).mpr h_even
  have hP_odd : Odd P := by
    induction a with
    | zero => omega
    | succ a _ => exact Nat.odd_mul.mpr ⟨hp_odd, by
      have : Odd (p ^ a) := Odd.pow ((Nat.not_even_iff_odd).mpr (fun h =>
        absurd (Nat.even_of_dvd hp.two_le (Nat.dvd_refl p)) ((Nat.not_even_iff_odd).mpr hp_odd)))⟩
  set m' := m / P
  have hPm_eq : P * m' = m := Nat.div_mul_cancel hP_dvd
  have hm'_pos : 0 < m' := by
    rw [Nat.pos_div_iff_eq_zero]; intro h; rw [h] at hPm_eq; simp at hPm_eq
  have hcop : Nat.Coprime P m' := by
    rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)] at hP_dvd
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne1
    have h_gt1 : 1 < Nat.gcd P m' := by omega
    have hgcd_dvd : Nat.gcd P m' ∣ P := Nat.gcd_dvd_right P m'
    have hp_dvd_gcd : p ∣ Nat.gcd P m' := by
      rcases hp.eq_one_or_self (Nat.gcd P m') hgcd_dvd with h1 | hself
      · omega
      · exact hself ▸ Nat.dvd_refl p
    have hp_dvd_m' : p ∣ m' := hp_dvd_gcd.trans (Nat.gcd_dvd_left P m')
    have : p ^ (a + 1) ∣ m := by
      rw [Nat.pow_succ, hPm_eq]; exact Nat.mul_dvd_mul_left p hp_dvd_m'
    rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)] at this
    omega
  have h_sum := sum_allUnitaryDivisors_mul_of_prime_pow_coprime p a m' hp ha hm'_pos hcop
  have h1P_even : Even (1 + P) := by
    rw [Nat.even_iff]; have : P % 2 = 1 := Nat.odd_iff.mp hP_odd; omega
  by_cases hm'_eq_1 : m' = 1
  · rw [hm'_eq_1] at h_sum
    have h_sum_1 : ∑ d ∈ allUnitaryDivisors 1, d = 1 := by
      simp [allUnitaryDivisors, Finset.Ico, Finset.filter]
    rw [h_sum_1] at h_sum; rw [h_sum]; exact h1P_even
  · have hm'_odd : Odd m' := by
      by_cases h_even : Even m'
      · exfalso
        have : Even (P * m') := Nat.even_mul.mpr
          (Or.inr ⟨(Nat.not_even_iff_odd).mpr hP_odd, h_even⟩)
        rw [hPm_eq] at this
        exact absurd this ((Nat.not_even_iff_odd).mpr hm_odd)
      · exact (Nat.not_even_iff_odd).mpr h_even
    have hm'_3 : 3 ≤ m' := by
      have : ¬ Even m' := (Nat.not_even_iff_odd).mpr hm'_odd
      have : m' ≠ 2 := fun h => this (h ▸ Nat.even_two)
      omega
    have hm'_lt : m' < m := by
      have hP_ge2 : 2 ≤ P := Nat.le_trans (by omega : 2 ≤ p)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ a))
      have : m' < 2 * m' := by omega
      have : m' < P * m' := by calc m' < 2 * m' := by omega
        _ ≤ P * m' := Nat.mul_le_mul_right m' hP_ge2
      rw [← hPm_eq] at this; omega
    have h_even_m' : Even (∑ d ∈ allUnitaryDivisors m', d) := ih m' hm'_lt hm'_odd hm'_3
    rw [h_sum]; exact Nat.even_mul.mpr (Or.inl h1P_even)

/-- For odd n with ≥ 2 prime factors, 4 ∣ sum of all unitary divisors. -/
theorem sum_allUnitaryDivisors_dvd4 (n : ℕ) (hn_odd : Odd n) (hn3 : 3 ≤ n)
    (hn_not_pp : ¬ ∃ p k, Nat.Prime p ∧ 0 < k ∧ n = p ^ k) :
    4 ∣ ∑ d ∈ allUnitaryDivisors n, d := by
  have hn_ne1 : n ≠ 1 := by omega
  have hp := Nat.minFac_prime hn_ne1
  set p := Nat.minFac n
  set a := n.factorization p
  set P := p ^ a
  have ha : 0 < a := by
    rw [hp.dvd_iff_one_le_factorization (by omega : n ≠ 0)]
    exact Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)
  have hP_dvd : P ∣ n := by
    rw [hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)]; exact le_rfl
  have hp_odd : Odd p := by
    by_cases h_even : Even p
    · exfalso; have : p = 2 := Nat.even_iff.mp h_even
      rw [this] at hP_dvd
      exact absurd (Nat.even_of_dvd (by omega : 2 ≤ p) hP_dvd) ((Nat.not_even_iff_odd).mpr hn_odd)
    · exact (Nat.not_even_iff_odd).mpr h_even
  have hP_odd : Odd P := by
    induction a with
    | zero => omega
    | succ a _ => exact Nat.odd_mul.mpr ⟨hp_odd, by
      have : Odd (p ^ a) := Odd.pow ((Nat.not_even_iff_odd).mpr (fun h =>
        absurd (Nat.even_of_dvd hp.two_le (Nat.dvd_refl p)) ((Nat.not_even_iff_odd).mpr hp_odd)))⟩
  set m := n / P
  have hPm_eq : P * m = n := Nat.div_mul_cancel hP_dvd
  have hm_pos : 0 < m := by
    rw [Nat.pos_div_iff_eq_zero]; intro h; rw [h] at hPm_eq; simp at hPm_eq
  have hm3 : 3 ≤ m := by
    by_contra h
    have : m ≤ 2 := by omega
    rcases (show m = 1 ∨ m = 2 by omega) with h1 | h2
    · rw [h1] at hPm_eq; exact hn_not_pp ⟨p, a, hp, ha, hPm_eq.symm⟩
    · rw [h2] at hPm_eq
      have : Even n := by rw [hPm_eq]; exact Nat.even_mul.mpr
        (Or.inr ⟨(Nat.not_even_iff_odd).mpr hP_odd, Nat.even_two⟩)
      exact absurd this ((Nat.not_even_iff_odd).mpr hn_odd)
  have hm_odd : Odd m := by
    by_cases h_even : Even m
    · exfalso
      have : Even (P * m) := Nat.even_mul.mpr
        (Or.inr ⟨(Nat.not_even_iff_odd).mpr hP_odd, h_even⟩)
      rw [hPm_eq] at this
      exact absurd this ((Nat.not_even_iff_odd).mpr hn_odd)
    · exact (Nat.not_even_iff_odd).mpr h_even
  have hcop : Nat.Coprime P m := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra h_ne1
    have h_gt1 : 1 < Nat.gcd P m := by omega
    have hgcd_dvd : Nat.gcd P m ∣ P := Nat.gcd_dvd_right P m
    have hp_dvd_gcd : p ∣ Nat.gcd P m := by
      rcases hp.eq_one_or_self (Nat.gcd P m) hgcd_dvd with h1 | hself
      · omega
      · exact hself ▸ Nat.dvd_refl p
    have hp_dvd_m : p ∣ m := hp_dvd_gcd.trans (Nat.gcd_dvd_left P m)
    have : p ^ (a + 1) ∣ n := by
      rw [Nat.pow_succ, hPm_eq]; exact Nat.mul_dvd_mul_left p hp_dvd_m
    rw [hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)] at this
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
