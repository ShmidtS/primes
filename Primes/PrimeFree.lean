import Mathlib
import Primes.Basic
import Primes.Wheel

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

/-! ## Prime-free intervals from primorial construction -/

def PrimeFreeInterval (a b : Nat) : Prop :=
  ∀ k : Nat, 2 ≤ k → k ≤ b → ¬ Nat.Prime (a + k)

private lemma count_mono (a b : Nat) (hab : a ≤ b) :
    Nat.count Nat.Prime a ≤ Nat.count Nat.Prime b := by
  induction hab with
  | refl => rfl
  | step n ih =>
    unfold Nat.count at ih ⊢
    rw [List.range_succ, List.countP_append, List.countP_singleton] at ⊢
    omega

private lemma count_strict_at_prime (a b : Nat) (hab : a < b) (hb : Nat.Prime b) :
    Nat.count Nat.Prime (a + 1) < Nat.count Nat.Prime (b + 1) := by
  have hle : a + 1 ≤ b := by omega
  have hbase : Nat.count Nat.Prime (a + 1) ≤ Nat.count Nat.Prime b := count_mono (a + 1) b hle
  have hstep : Nat.count Nat.Prime b < Nat.count Nat.Prime (b + 1) := by
    unfold Nat.count; rw [List.range_succ, List.countP_append, List.countP_singleton]; simp [hb]
  omega

private lemma count_succ_inj_on_primes (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime (q + 1)) : p = q := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := count_strict_at_prime p q hlt hq; omega
  · have := count_strict_at_prime q p hgt hp; omega

theorem prime_lt_nth_prime_dvd_primorial (m p : Nat)
    (hp : Nat.Prime p) (hplt : p < Nat.nth Nat.Prime m) : p ∣ primorial m := by
  induction m generalizing p with
  | zero =>
    exfalso; have hp0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
    rw [hp0] at hplt; have h2 : 2 ≤ p := hp.two_le; omega
  | succ m ih =>
    by_cases hlt : p < Nat.nth Nat.Prime m
    · have h := ih p hp hlt
      rw [primorial_succ]; exact h.trans (Nat.dvd_mul_right _ _)
    · have hge : Nat.nth Nat.Prime m ≤ p := by omega
      have hpm : Nat.Prime (Nat.nth Nat.Prime m) := Nat.prime_nth_prime m
      have hcount_pm : Nat.count Nat.Prime (Nat.nth Nat.Prime m + 1) = m + 1 :=
        Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime m
      have hpm1 := Nat.prime_nth_prime (m + 1)
      have hcount_pm1_plus1 : Nat.count Nat.Prime (Nat.nth Nat.Prime (m + 1) + 1) = m + 2 :=
        Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime (m + 1)
      have hcount_p1_le : Nat.count Nat.Prime (p + 1) ≤ m + 1 := by
        have hstrict := count_strict_at_prime p (Nat.nth Nat.Prime (m + 1)) hplt hpm1; omega
      have hcount_p1_ge : Nat.count Nat.Prime (p + 1) ≥ m + 1 := by
        have h := count_mono (Nat.nth Nat.Prime m + 1) (p + 1) (by omega); omega
      have hcount_p1_eq : Nat.count Nat.Prime (p + 1) = m + 1 := by omega
      have heq : p = Nat.nth Nat.Prime m :=
        count_succ_inj_on_primes p (Nat.nth Nat.Prime m) hp hpm
          (hcount_p1_eq.trans hcount_pm.symm)
      rw [heq, primorial_succ]; exact ⟨primorial m, by ring⟩

/-- **Primorial gives prime-free interval**: P_m + k composite for all k in [2, p_m - 1]. -/
theorem primorial_prime_free_interval (m : Nat) (hm : 1 ≤ m) :
    PrimeFreeInterval (primorial m) ((Nat.nth Nat.Prime m) - 1) := by
  intro k hk1 hk2
  have hp_prime : Nat.Prime (Nat.minFac k) := Nat.minFac_prime (by omega : k ≠ 1)
  have hp_dvd : Nat.minFac k ∣ k := Nat.minFac_dvd k
  have hp_le_k : Nat.minFac k ≤ k := Nat.le_of_dvd (by omega) hp_dvd
  have hp_lt : Nat.minFac k < Nat.nth Nat.Prime m := by omega
  have hp_dvd_Pm : Nat.minFac k ∣ primorial m :=
    prime_lt_nth_prime_dvd_primorial m (Nat.minFac k) hp_prime hp_lt
  have hp_dvd_sum : Nat.minFac k ∣ primorial m + k := hp_dvd_Pm.add hp_dvd
  have hgt : Nat.minFac k < primorial m + k := by
    have hPm_pos : 0 < primorial m := primorial_pos m; omega
  intro hprime
  have htwo : 2 ≤ Nat.minFac k := hp_prime.two_le
  have hfac : primorial m + k =
      Nat.minFac k * ((primorial m + k) / (Nat.minFac k)) := by
    have h := Nat.div_mul_cancel hp_dvd_sum; rw [mul_comm] at h; exact h.symm
  obtain h_unit | h_unit := hprime.isUnit_or_isUnit hfac
  · have : Nat.minFac k = 1 := Nat.isUnit_iff.mp h_unit; omega
  · have hq_eq : (primorial m + k) / (Nat.minFac k) = 1 := Nat.isUnit_iff.mp h_unit
    rw [hq_eq, mul_one] at hfac; omega

/-- **Exist consecutive primes with gap >= p_m - 2**. -/
theorem exists_prime_gap_ge_primorial_bound (m : Nat) (hm : 2 ≤ m) :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
      (Nat.nth Nat.Prime m) - 2 ≤ q - p ∧
      ∀ r : Nat, Nat.Prime r → p < r → r < q → False := by
  classical
  have hp_m_ge3 : 3 ≤ Nat.nth Nat.Prime m := by
    have hp1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hge := (Nat.nth_strictMono Nat.infinite_setOf_prime).le_iff_le.mpr (by omega : 1 ≤ m)
    rw [hp1] at hge; omega
  have h_free : PrimeFreeInterval (primorial m) ((Nat.nth Nat.Prime m) - 1) :=
    primorial_prime_free_interval m (by omega)
  set S := (Finset.range (primorial m + 2)).filter Nat.Prime with hS_def
  have S_nonempty : S.Nonempty := by
    have h2mem : 2 ∈ S := by
      show 2 ∈ (Finset.range (primorial m + 2)).filter Nat.Prime
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by linarith [primorial_pos m]), Nat.prime_two⟩
    exact ⟨2, h2mem⟩
  set p := S.max' S_nonempty with hp_def
  have hp_prime : Nat.Prime p := (Finset.mem_filter.mp (Finset.max'_mem S S_nonempty)).2
  have hp_le : p ≤ primorial m + 1 := by
    have hpf := Finset.mem_filter.mp (Finset.max'_mem S S_nonempty)
    rw [Finset.mem_range] at hpf; omega
  have hp_max : ∀ r, p < r → r ≤ primorial m + 1 → ¬ Nat.Prime r := by
    intro r hrp hrle hpr
    have hr_mem : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpr⟩
    have : r ≤ p := S.le_max' r hr_mem; omega
  have h_no_prime : ∀ r, p < r → r ≤ primorial m + (Nat.nth Nat.Prime m) - 1 →
      ¬ Nat.Prime r := by
    intro r hrp hrle
    by_cases hrle2 : r ≤ primorial m + 1
    · exact hp_max r hrp hrle2
    · intro hpr
      have heq : r = primorial m + (r - primorial m) := by omega
      rw [heq] at hpr
      exact absurd hpr (h_free (r - primorial m) (by omega) (by omega))
  have h_exists : ∃ q : Nat, Nat.Prime q ∧ primorial m + (Nat.nth Nat.Prime m) ≤ q := by
    obtain ⟨q, hq_ge, hq_prime⟩ :=
      Nat.exists_infinite_primes (primorial m + Nat.nth Nat.Prime m)
    exact ⟨q, hq_prime, hq_ge⟩
  obtain ⟨q_big, hq_big_prime, hq_big_ge⟩ := h_exists
  set T := (Finset.Icc (primorial m + Nat.nth Nat.Prime m) q_big).filter Nat.Prime with hT_def
  have T_nonempty : T.Nonempty := by
    have hqmem : q_big ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hq_big_ge, le_rfl⟩, hq_big_prime⟩
    exact ⟨q_big, hqmem⟩
  set q := T.min' T_nonempty with hq_def
  have hq_prime : Nat.Prime q := (Finset.mem_filter.mp (T.min'_mem T_nonempty)).2
  have hq_ge : primorial m + Nat.nth Nat.Prime m ≤ q := by
    have hmem := T.min'_mem T_nonempty
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
  have hqbig_mem : q_big ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq_big_ge, le_rfl⟩, hq_big_prime⟩
  have hq_le_qbig : q ≤ q_big := T.min'_le q_big hqbig_mem
  have hq_min : ∀ r, primorial m + Nat.nth Nat.Prime m ≤ r → r < q → ¬ Nat.Prime r := by
    intro r hrge hrlt hpr
    have hr_mem : r ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hrge, by linarith [hrlt, hq_le_qbig]⟩, hpr⟩
    have : q ≤ r := T.min'_le r hr_mem; omega
  have h_consec : ∀ r, Nat.Prime r → p < r → r < q → False := by
    intro r hr_prime hrp hrq
    by_cases hrle1 : r ≤ primorial m + 1
    · exact hp_max r hrp hrle1 hr_prime
    · by_cases hrle2 : r ≤ primorial m + (Nat.nth Nat.Prime m) - 1
      · exact h_no_prime r hrp hrle2 hr_prime
      · have hge : primorial m + Nat.nth Nat.Prime m ≤ r := by
          have h3 : primorial m + (Nat.nth Nat.Prime m) - 1 < r := (not_le).mp hrle2
          have h4 : 1 ≤ primorial m + Nat.nth Nat.Prime m := by
            have := primorial_pos m; have := hp_m_ge3; omega
          omega
        exact hq_min r hge hrq hr_prime
  refine ⟨p, q, hp_prime, hq_prime, ?_, ?_, h_consec⟩
  · have hkey : primorial m + 1 < primorial m + Nat.nth Nat.Prime m := by omega
    omega
  · have hkey : primorial m + Nat.nth Nat.Prime m ≤ q := hq_ge
    omega

end
end PrimeGaps
