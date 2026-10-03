import Mathlib
import Primes.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

/-! ## Primorial: product of first m primes -/

def primorial (m : Nat) : Nat := (Finset.range m).prod fun i => Nat.nth Nat.Prime i

theorem primorial_succ (m : Nat) :
    primorial (m + 1) = primorial m * Nat.nth Nat.Prime m := by
  simp [primorial, Finset.prod_range_succ]

theorem primorial_pos (m : Nat) : 0 < primorial m := by
  unfold primorial
  exact Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

theorem primorial_even (m : Nat) (hm : 1 ≤ m) : Even (primorial m) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [primorial_succ]
    by_cases hm0 : m = 0
    · subst hm0; rw [Nat.nth_prime_zero_eq_two]; exact even_two
    · exact Nat.even_mul.mpr (Or.inl (ih (by omega)))

theorem primeFactors_primorial (m : Nat) (hm : 0 < m) :
    Nat.primeFactors (primorial m) =
      (Finset.range m).image (fun i => Nat.nth Nat.Prime i) := by
  induction m with
  | zero => exact absurd hm (by simp)
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
      have hp2 : Nat.Prime 2 := by decide
      unfold primorial
      rw [Finset.prod_range_one, hp0, Finset.range_one, Finset.image_singleton, hp0]
      ext q; simp only [Finset.mem_singleton]
      constructor
      · intro hmem; rw [Nat.mem_primeFactors] at hmem
        exact (Nat.prime_dvd_prime_iff_eq hmem.1 hp2).mp hmem.2.1
      · rintro rfl; exact Nat.mem_primeFactors.mpr ⟨hp2, dvd_rfl, hp2.ne_zero⟩
    · have hmpos : 0 < m := by omega
      rw [primorial_succ]
      have hcoprime : Nat.Coprime (primorial m) (Nat.nth Nat.Prime m) := by
        unfold primorial; rw [Nat.coprime_prod_left_iff]
        intro i hi
        have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
        have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
        have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
          (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
        exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)
      rw [Nat.primeFactors_mul (primorial_pos m).ne' (Nat.prime_nth_prime m).pos.ne',
          ih hmpos]
      have hpf_pm : Nat.primeFactors (Nat.nth Nat.Prime m) = {Nat.nth Nat.Prime m} := by
        have hpm := Nat.prime_nth_prime m
        ext q; simp only [Finset.mem_singleton]
        constructor
        · intro hmem; rw [Nat.mem_primeFactors] at hmem
          exact (Nat.prime_dvd_prime_iff_eq hmem.1 hpm).mp hmem.2.1
        · rintro rfl; exact Nat.mem_primeFactors.mpr ⟨hpm, dvd_rfl, hpm.ne_zero⟩
      have hrange : Finset.range (m + 1) = insert m (Finset.range m) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_range]
        constructor
        · intro h; by_cases hx : x = m; · exact Or.inl hx
          · exact Or.inr (by omega)
        · rintro (rfl | h)
          · omega
          · omega
      rw [hpf_pm, hrange, Finset.image_insert]
      exact Finset.union_comm _ _

/-! ## Primorial wheel mean gap = Euler product -/

noncomputable def primorialWheelMeanGap (m : Nat) : ℚ :=
  (primorial m : ℚ) / (Nat.totient (primorial m) : ℚ)

theorem totient_primorial_explicit (m : Nat) :
    Nat.totient (primorial m) = (Finset.range m).prod (fun i => Nat.nth Nat.Prime i - 1) := by
  induction m with
  | zero => simp [primorial, Nat.totient_one]
  | succ m ih =>
    rw [primorial_succ, Nat.totient_mul]
    · rw [ih]
      have hp : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      rw [Nat.totient_prime hp]
      simp [Finset.prod_range_succ, Nat.mul_sub]
    · apply (Nat.coprime_prod_left_iff (t := Finset.range m)
        (s := fun i => Nat.nth Nat.Prime i) (x := Nat.nth Nat.Prime m)).mpr
      intro i hi
      have hpi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
      have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime m :=
        (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mpr (Finset.mem_range.mp hi)
      exact (Nat.coprime_primes hpi hpm).mpr (Nat.ne_of_lt hlt)

theorem primorialWheelMeanGap_eq_euler_product (m : Nat) :
    primorialWheelMeanGap m =
    (Finset.range m).prod (fun i =>
      (Nat.nth Nat.Prime i : ℚ) / ((Nat.nth Nat.Prime i - 1 : ℕ) : ℚ)) := by
  unfold primorialWheelMeanGap
  rw [totient_primorial_explicit]
  unfold primorial
  push_cast
  rw [← Finset.prod_div_distrib]

end
end PrimeGaps
