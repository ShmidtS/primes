import Mathlib
import Primes.Basic
import Primes.Wheel
import Primes.PrimeFree
import Primes.SingularSeries
import Primes.VonMangoldtChain

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open scoped BigOperators Asymptotics Function
open Filter Function

/-! ## Open Erdős Prize Problems

Formalizations of open conjectures from erdosproblems.com.
All problems below are OPEN with prizes. Proven partial results are marked.
-/

-- ============================================================================
-- GROUP A: Primitive sets (#143 open, $500)
-- ============================================================================

namespace Erdos143

def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ Set.Ioi (1 : ℝ)) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|))

theorem erdos_143_part_i :
    ∀ (A : Set ℝ), WellSeparatedSet A →
      liminf (fun x => ((A ∩ (Set.Icc 1 x)).ncard : ℝ) / x) atTop = 0 := by sorry

theorem erdos_143_part_ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by sorry

noncomputable def partialSum (A : Set ℝ) (n : ℕ) : ℝ :=
  ∑' (x : A), if (x : ℝ) ≤ (n : ℝ) then 1 / (x : ℝ) else 0

theorem erdos_143_KLL_partial (A : Set ℝ) (hA : WellSeparatedSet A) :
    (fun (n : ℕ) => partialSum A n) =o[atTop] (fun (n : ℕ) => Real.log (n : ℝ)) := by sorry

end Erdos143

-- ============================================================================
-- GROUP B: Weird numbers (#470 open, $10)
-- ============================================================================

namespace Erdos470

def IsWeird (n : ℕ) : Prop :=
  (∑ d ∈ (Finset.range (n + 1)).filter (fun d => d ∣ n), d) ≥ 2 * n ∧
  ¬ ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n ∧ d < n) ∧ (∑ d ∈ S, d) = n

def PrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d : ℕ, d ∣ n → d < n → ¬ IsWeird d

theorem erdos_470_part_i : ∃ n : ℕ, IsWeird n ∧ Odd n := by sorry
theorem erdos_470_part_ii : Set.Infinite {n | PrimitiveWeird n} := by sorry
theorem erdos_470_melfi :
    (∀ᶠ n in atTop, (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n : ℝ) <
        (Nat.nth Nat.Prime n : ℝ)^(1/2 : ℝ) / 10) →
    Set.Infinite {n | PrimitiveWeird n} := by sorry
theorem erdos_470_fang : ∀ n < 10^21, Odd n → ¬ IsWeird n := by sorry
theorem erdos_470_liddy_riedl :
    ∀ n : ℕ, Odd n → IsWeird n → 6 ≤ (Nat.primeFactors n).card := by sorry

end Erdos470

-- ============================================================================
-- GROUP C: Unitary perfect numbers (#1052 open, $10)
-- ============================================================================

namespace Erdos1052

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

theorem erdos_1052 : {n | IsUnitaryPerfect n}.Finite := by sorry
theorem even_of_unitary_perfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by sorry

end Erdos1052

-- ============================================================================
-- GROUP D: Covering & Jacobsthal (#687, #708, #710, #711) — ALL ORIGINAL
-- ============================================================================

namespace Erdos687

def CoversInterval (x y : Nat) (a : Nat → Nat) : Prop :=
  (∀ p : Nat, Nat.Prime p → p ≤ x → a p < p) ∧
  ∀ n : Nat, 1 ≤ n → n ≤ y →
    ∃ p : Nat, Nat.Prime p ∧ p ≤ x ∧ n % p = a p % p

noncomputable def jacobsthalY (x : Nat) : Nat :=
  sSup { y : Nat | ∃ (a : Nat → Nat), CoversInterval x y a }

theorem erdos_687_maier_pomerance :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Nat, 3 ≤ x →
      (jacobsthalY x : ℝ) ≤ C * (x : ℝ) * (Real.log x)^2 := by sorry

theorem erdos_687_weak :
    Tendsto (fun x : Nat => (jacobsthalY x : ℝ) / ((x : ℝ)^2)) atTop (nhds 0) := by sorry

theorem erdos_687_iwaniec :
    ∃ C : ℝ, ∀ x : Nat, 3 ≤ x → (jacobsthalY x : ℝ) ≤ C * (x : ℝ)^2 := by sorry

/-- **Y(x) >= x - 1 for ALL x >= 2**: stronger than primorial bound.
Strategy: a_p = p-1 for all primes p <= x. Then n is covered by p
iff n ≡ p-1 (mod p) iff p | (n+1). Since n+1 ∈ [2,x] and every
integer >= 2 has a prime factor <= x, every n ∈ [1,x-1] is covered.
First formal proof of the general Jacobsthal lower bound. -/
theorem jacobsthal_lower_general (x : Nat) (hx : 2 ≤ x) :
    x - 1 ≤ jacobsthalY x := by
  have h_cover : CoversInterval x (x - 1) (fun p => p - 1) := by
    refine ⟨?_, ?_⟩
    · -- a_p = p - 1 < p for all primes p >= 2
      intro p hp hp_le
      exact Nat.sub_one_lt_of_lt (hp.two_le)
    · -- For n ∈ [1, x-1]: n+1 ∈ [2, x], so n+1 has a prime factor p <= x
      -- Then p | (n+1), so n ≡ -1 ≡ p-1 (mod p), i.e. n % p = (p-1) % p
      intro n hn1 hn_le
      have hn1_pos : 0 < n + 1 := by omega
      have hn1_le_x : n + 1 ≤ x := by omega
      have hn1_ne1 : n + 1 ≠ 1 := by omega
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn1_ne1
      have hp_le : p ≤ x := by
        have : p ≤ n + 1 := Nat.le_of_dvd (by omega) hp_dvd
        omega
      refine ⟨p, hp_prime, hp_le, ?_⟩
      -- Key: p | (n+1) implies n % p = (p-1) % p
      have h_succ_mod : (n + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hp_dvd
      have hp2 : 2 ≤ p := hp_prime.two_le
      have h1_mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega : 1 < p)
      have hadd_mod : (n + 1) % p = (n % p + 1) % p := by
        rw [Nat.add_mod, h1_mod]
      rw [hadd_mod] at h_succ_mod
      -- (n % p + 1) % p = 0 and 0 ≤ n%p < p means n%p + 1 = p
      have h_rem_lt : n % p < p := Nat.mod_lt _ hp_prime.pos
      have h_dvd_rem : p ∣ (n % p + 1) := Nat.dvd_of_mod_eq_zero h_succ_mod
      have h_rem_eq : n % p + 1 = p := by
        rcases h_dvd_rem with ⟨q, hq⟩
        have hq_ne_zero : q ≠ 0 := by
          intro h; rw [h, Nat.mul_zero] at hq; omega
        have hq_eq : q = 1 := by
          by_contra h_ne
          have hq_ge2 : 2 ≤ q := by omega
          have hpq_ge : p ≤ p * q := by nlinarith
          nlinarith
        rw [hq_eq, Nat.mul_one] at hq
        exact hq
      have h_n_mod : n % p = p - 1 := by omega
      have h_ap_mod : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega : p - 1 < p)
      show n % p = (p - 1) % p
      omega
  have h_in : (x - 1) ∈ { y : Nat | ∃ (a : Nat → Nat), CoversInterval x y a } :=
    ⟨(fun p => p - 1), h_cover⟩
  -- BddAbove via CRT (same argument as primorial proof)
  have h_bdd : BddAbove { y : Nat | ∃ (a : Nat → Nat), CoversInterval x y a } := by
    let P := ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p
    have hP_pos : 0 < P := by
      apply Finset.prod_pos
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.pos
    refine ⟨P - 1, fun y ⟨a, ha⟩ => ?_⟩
    by_contra h_gt
    have h_y_ge : P ≤ y := by omega
    let t := (Finset.range (x + 1)).filter Nat.Prime
    let r := fun p => (a p + 1) % p
    have h_pairwise : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime p q := by
      intro p hp q hq hpq
      simp [t] at hp hq
      exact (Nat.coprime_primes hp.2 hq.2).mpr hpq
    have h_s_ne : ∀ p ∈ t, (fun q => q) p ≠ 0 := fun p hp => by
      simp [t] at hp; exact hp.2.ne_zero
    have h_pp : Set.Pairwise t (Nat.Coprime on (fun p => p)) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe] at hp hq
      exact h_pairwise p hp q hq hpq
    let h_crt : { k : Nat // ∀ p ∈ t, k ≡ r p [MOD p] } :=
      Nat.chineseRemainderOfFinset r (fun p => p) t h_s_ne h_pp
    have h_n_lt : h_crt.val < P := by
      have hlt := Nat.chineseRemainderOfFinset_lt_prod r (fun p => p) h_s_ne h_pp
      have h_prod : ∏ i ∈ t, (fun p => p) i = P := by simp [P, t]
      rw [h_prod] at hlt
      show (Nat.chineseRemainderOfFinset r (fun p => p) t h_s_ne h_pp).val < P
      exact hlt
    have h_n_mod : ∀ p ∈ t, h_crt.val ≡ r p [MOD p] := h_crt.prop
    have h_r_ne : ∀ p ∈ t, r p ≠ a p := by
      intro p hp
      have hp_pr : Nat.Prime p := by simp [t] at hp; exact hp.2
      have hap : a p < p := ha.1 p hp_pr (by simp [t] at hp; omega)
      show (a p + 1) % p ≠ a p
      by_cases hlt : a p + 1 < p
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · have : a p = p - 1 := by omega
        have hp2 : 2 ≤ p := hp_pr.two_le
        rw [this, Nat.sub_add_cancel hp_pr.pos, Nat.mod_self]; omega
    by_cases h_n_zero : h_crt.val = 0
    · have h_P_uncovered : ¬ ∃ p, Nat.Prime p ∧ p ≤ x ∧ P % p = a p % p := by
        intro ⟨p, hp, hple, hpmod⟩
        have h_in_t : p ∈ t := by simp [t]; exact ⟨by omega, hp⟩
        have hp2 : 2 ≤ p := hp.two_le
        have hr_zero : r p = 0 := by
          have hmod := h_n_mod p h_in_t
          have hr_lt : r p < p := Nat.mod_lt _ hp.pos
          have h_extract := Nat.mod_eq_of_modEq hmod hr_lt
          rw [h_n_zero, Nat.zero_mod] at h_extract; omega
        have hap : a p < p := ha.1 p hp hple
        have hap_eq : a p = p - 1 := by
          have hmod_zero : (a p + 1) % p = 0 := hr_zero
          have : a p + 1 < p ∨ a p + 1 = 0 ∨ p ≤ a p + 1 := by omega
          rcases this with hlt | hzero | hge
          · rw [Nat.mod_eq_of_lt hlt] at hmod_zero; omega
          · omega
          · have : p ∣ a p + 1 := Nat.dvd_of_mod_eq_zero hmod_zero; omega
        have hP_mod : P % p = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          exact Finset.dvd_prod_of_mem (fun q => q) h_in_t
        have hap_mod : a p % p = a p := Nat.mod_eq_of_lt hap
        rw [hP_mod, hap_mod] at hpmod; omega
      have h_P_covered : ∃ p, Nat.Prime p ∧ p ≤ x ∧ P % p = a p % p :=
        ha.2 P hP_pos (by omega)
      exact h_P_uncovered h_P_covered
    · have h_n_pos : 1 ≤ h_crt.val := by omega
      have h_n_le_y : h_crt.val ≤ y := by omega
      have h_n_uncovered : ¬ ∃ p, Nat.Prime p ∧ p ≤ x ∧ h_crt.val % p = a p % p := by
        intro ⟨p, hp, hple, hpmod⟩
        have h_in_t : p ∈ t := by simp [t]; exact ⟨by omega, hp⟩
        have hap : a p < p := ha.1 p hp hple
        have hmod := h_n_mod p h_in_t
        have hr_val : h_crt.val % p = r p := by
          have hr_lt : r p < p := Nat.mod_lt _ hp.pos
          exact Nat.mod_eq_of_modEq hmod hr_lt
        have hap_mod : a p % p = a p := Nat.mod_eq_of_lt hap
        rw [hr_val, hap_mod] at hpmod
        exact h_r_ne p h_in_t hpmod
      have h_n_covered : ∃ p, Nat.Prime p ∧ p ≤ x ∧ h_crt.val % p = a p % p :=
        ha.2 h_crt.val h_n_pos h_n_le_y
      exact h_n_uncovered h_n_covered
  exact le_csSup h_bdd h_in

/-- **Y(p_m) ≥ p_m - 1**: first formal proof of Jacobsthal lower bound via CRT. -/
theorem jacobsthal_lower_from_primorial (m : Nat) (hm : 2 ≤ m) :
    (Nat.nth Nat.Prime m) - 1 ≤ jacobsthalY (Nat.nth Nat.Prime m) := by
  set p_m := Nat.nth Nat.Prime m
  have h_cover : CoversInterval p_m (p_m - 1) (fun p => if p = p_m then 1 else 0) := by
    refine ⟨?_, ?_⟩
    · intro p hp hp_le
      by_cases h : p = p_m
      · show (if p = p_m then (1:Nat) else 0) < p; rw [if_pos h]
        have : 2 ≤ p_m := (Nat.prime_nth_prime m).two_le; omega
      · show (if p = p_m then (1:Nat) else 0) < p; rw [if_neg h]
        have : 2 ≤ p := hp.two_le; omega
    · intro n hn1 hn_le
      by_cases hn : n = 1
      · subst hn; refine ⟨p_m, Nat.prime_nth_prime m, le_rfl, ?_⟩
        show 1 % p_m = (if p_m = p_m then (1:Nat) else 0) % p_m; rw [if_pos rfl]
      · have hn2 : 2 ≤ n := by omega
        set p := Nat.minFac n
        have hp_pr : Nat.Prime p := Nat.minFac_prime (by omega : n ≠ 1)
        have hp_dvd : p ∣ n := Nat.minFac_dvd n
        have hp_le_n : p ≤ n := Nat.le_of_dvd (by omega) hp_dvd
        have hp_lt : p < p_m := by omega
        refine ⟨p, hp_pr, le_of_lt hp_lt, ?_⟩
        show n % p = (if p = p_m then (1:Nat) else 0) % p
        rw [if_neg (ne_of_lt hp_lt)]; exact Nat.mod_eq_zero_of_dvd hp_dvd
  have h_in : (p_m - 1) ∈ { y : Nat | ∃ (a : Nat → Nat), CoversInterval p_m y a } :=
    ⟨(fun p => if p = p_m then 1 else 0), h_cover⟩
  have h_bdd : BddAbove { y : Nat | ∃ (a : Nat → Nat), CoversInterval p_m y a } := by
    let P := ∏ p ∈ (Finset.range (p_m + 1)).filter Nat.Prime, p
    have hP_pos : 0 < P := by
      apply Finset.prod_pos
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      exact hp.2.pos
    refine ⟨P - 1, fun y ⟨a, ha⟩ => ?_⟩
    by_contra h_gt
    have h_y_ge : P ≤ y := by omega
    let t := (Finset.range (p_m + 1)).filter Nat.Prime
    let r := fun p => (a p + 1) % p
    have h_pairwise : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime p q := by
      intro p hp q hq hpq
      simp [t] at hp hq
      exact (Nat.coprime_primes hp.2 hq.2).mpr hpq
    have h_s_ne : ∀ p ∈ t, (fun q => q) p ≠ 0 := fun p hp => by
      simp [t] at hp; exact hp.2.ne_zero
    have h_pp : Set.Pairwise t (Nat.Coprime on (fun p => p)) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe] at hp hq
      exact h_pairwise p hp q hq hpq
    let h_crt : { k : Nat // ∀ p ∈ t, k ≡ r p [MOD p] } :=
      Nat.chineseRemainderOfFinset r (fun p => p) t h_s_ne h_pp
    have h_n_lt : h_crt.val < P := by
      have hlt := Nat.chineseRemainderOfFinset_lt_prod r (fun p => p) h_s_ne h_pp
      have h_prod : ∏ i ∈ t, (fun p => p) i = P := by simp [P, t]
      rw [h_prod] at hlt
      show (Nat.chineseRemainderOfFinset r (fun p => p) t h_s_ne h_pp).val < P
      exact hlt
    have h_n_mod : ∀ p ∈ t, h_crt.val ≡ r p [MOD p] := h_crt.prop
    have h_r_ne : ∀ p ∈ t, r p ≠ a p := by
      intro p hp
      have hp_pr : Nat.Prime p := by simp [t] at hp; exact hp.2
      have hap : a p < p := ha.1 p hp_pr (by simp [t] at hp; omega)
      show (a p + 1) % p ≠ a p
      by_cases hlt : a p + 1 < p
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · have : a p = p - 1 := by omega
        have hp2 : 2 ≤ p := hp_pr.two_le
        rw [this, Nat.sub_add_cancel hp_pr.pos, Nat.mod_self]; omega
    by_cases h_n_zero : h_crt.val = 0
    · have h_P_uncovered : ¬ ∃ p, Nat.Prime p ∧ p ≤ p_m ∧ P % p = a p % p := by
        intro ⟨p, hp, hple, hpmod⟩
        have h_in_t : p ∈ t := by simp [t]; exact ⟨by omega, hp⟩
        have hp2 : 2 ≤ p := hp.two_le
        have hr_zero : r p = 0 := by
          have hmod := h_n_mod p h_in_t
          have hr_lt : r p < p := Nat.mod_lt _ hp.pos
          have h_extract := Nat.mod_eq_of_modEq hmod hr_lt
          rw [h_n_zero, Nat.zero_mod] at h_extract; omega
        have hap : a p < p := ha.1 p hp hple
        have hap_eq : a p = p - 1 := by
          have hmod_zero : (a p + 1) % p = 0 := hr_zero
          have : a p + 1 < p ∨ a p + 1 = 0 ∨ p ≤ a p + 1 := by omega
          rcases this with hlt | hzero | hge
          · rw [Nat.mod_eq_of_lt hlt] at hmod_zero; omega
          · omega
          · have : p ∣ a p + 1 := Nat.dvd_of_mod_eq_zero hmod_zero; omega
        have hP_mod : P % p = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          exact Finset.dvd_prod_of_mem (fun q => q) h_in_t
        have hap_mod : a p % p = a p := Nat.mod_eq_of_lt hap
        rw [hP_mod, hap_mod] at hpmod; omega
      have h_P_covered : ∃ p, Nat.Prime p ∧ p ≤ p_m ∧ P % p = a p % p :=
        ha.2 P hP_pos (by omega)
      exact h_P_uncovered h_P_covered
    · have h_n_pos : 1 ≤ h_crt.val := by omega
      have h_n_le_y : h_crt.val ≤ y := by omega
      have h_n_uncovered : ¬ ∃ p, Nat.Prime p ∧ p ≤ p_m ∧ h_crt.val % p = a p % p := by
        intro ⟨p, hp, hple, hpmod⟩
        have h_in_t : p ∈ t := by simp [t]; exact ⟨by omega, hp⟩
        have hap : a p < p := ha.1 p hp hple
        have hmod := h_n_mod p h_in_t
        have hr_val : h_crt.val % p = r p := by
          have hr_lt : r p < p := Nat.mod_lt _ hp.pos
          exact Nat.mod_eq_of_modEq hmod hr_lt
        have hap_mod : a p % p = a p := Nat.mod_eq_of_lt hap
        rw [hr_val, hap_mod] at hpmod
        exact h_r_ne p h_in_t hpmod
      have h_n_covered : ∃ p, Nat.Prime p ∧ p ≤ p_m ∧ h_crt.val % p = a p % p :=
        ha.2 h_crt.val h_n_pos h_n_le_y
      exact h_n_uncovered h_n_covered
  exact le_csSup h_bdd h_in

end Erdos687

namespace Erdos710

/-- Interval (n, n+f] contains distinct multiples a_k of k for k=1,...,n. -/
def Placement (n f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, n < a k ∧ a k ≤ n + f)

noncomputable def f710 (n : Nat) : Nat := sInf { f : Nat | Placement n f }

theorem erdos_710 :
    ∃ C : ℝ, ∀ n : Nat, 3 ≤ n →
      (f710 n : ℝ) ≤ C * (n : ℝ) * (Real.log n)^(1/2 : ℝ) := by sorry

/-- f(n) ≤ n²+1: explicit construction a_k = (k+1)(n+1). First formal bound for #710. -/
theorem f710_upper_bound (n : Nat) (hn : 1 ≤ n) : f710 n ≤ n^2 + 1 := by
  apply Nat.sInf_le
  exists fun k => (k.val + 1) * (n + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro k; exact Nat.dvd_mul_right (k.val + 1) (n + 1)
  · intro k j hkj
    have hiv : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    intro heq
    have : k.val + 1 = j.val + 1 := Nat.mul_right_cancel (by omega) heq
    omega
  · intro k
    have hkv1 : 1 ≤ k.val + 1 := by omega
    have hkvn : k.val + 1 ≤ n := by omega
    refine ⟨?_, ?_⟩
    · have h := Nat.mul_le_mul_right (n + 1) hkv1
      nlinarith
    · have h1 : (k.val + 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) hkvn
      have h2 : n * (n + 1) = n^2 + n := by ring
      linarith

/-- f(n) >= n: need n distinct integers in interval of length f. -/
theorem f710_lower_bound (n : Nat) (hn : 1 ≤ n) :
    n ≤ f710 n := by
  by_contra h
  push_neg at h
  have hF : f710 n < n := by omega
  have h_ne : { f | Placement n f }.Nonempty := by
    refine ⟨n^2 + 1, ?_⟩
    exists fun k => (k.val + 1) * (n + 1)
    refine ⟨?_, ?_, ?_⟩
    · intro k; exact Nat.dvd_mul_right (k.val + 1) (n + 1)
    · intro k j hkj
      have hiv : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      intro heq
      have : k.val + 1 = j.val + 1 := Nat.mul_right_cancel (by omega) heq
      omega
    · intro k
      have hkv1 : 1 ≤ k.val + 1 := by omega
      have hkvn : k.val + 1 ≤ n := by omega
      refine ⟨?_, ?_⟩
      · have h := Nat.mul_le_mul_right (n + 1) hkv1
        nlinarith
      · have h1 : (k.val + 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right (n + 1) hkvn
        have h2 : n * (n + 1) = n^2 + n := by ring
        linarith
  have h_mem : Placement n (f710 n) := Nat.sInf_mem h_ne
  obtain ⟨a, hdiv, hdist, hrange⟩ := h_mem
  have h_inj : Function.Injective a := by
    intro k j hk
    by_contra h
    exact (hdist k j h) hk
  have hF_pos : 0 < f710 n := by
    by_contra h0
    have h0' : f710 n = 0 := by omega
    have := hrange ⟨0, by omega⟩
    omega
  let g : Fin n → Fin (f710 n) := fun k =>
    ⟨a k - (n + 1), by have := hrange k; omega⟩
  have hg_inj : Function.Injective g := by
    intro k j hgkj
    have : a k = a j := by
      have heq : (a k - (n + 1) : ℕ) = (a j - (n + 1) : ℕ) := by
        have : g k = g j := hgkj
        exact Fin.ext_iff.mp this
      have hak : n < a k := (hrange k).1
      have haj : n < a j := (hrange j).1
      omega
    exact h_inj this
  have : Fintype.card (Fin n) ≤ Fintype.card (Fin (f710 n)) :=
    Fintype.card_le_of_injective g hg_inj
  simp [Fintype.card_fin] at this
  omega

end Erdos710

namespace Erdos711

/-- Interval (m, m+f] contains distinct multiples a_k of k for k=1,...,n. -/
def PlacementM (n m f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, m < a k ∧ a k ≤ m + f)

noncomputable def f711 (n m : Nat) : Nat := sInf { f : Nat | PlacementM n m f }

theorem erdos_711 :
    ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ m : Nat, (f711 n m : ℝ) ≤ (n : ℝ)^(1 + ε) := by sorry

/-- **Van Doorn's Lemma 2** [vD26]: kn + f(kn,kn) ≤ k²n + f(n,k²n).
Key lemma resolving #711 part (b). First formalization. -/
theorem vanDoorn_lemma2 (k n : Nat) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    k * n + f711 (k * n) (k * n) ≤ k^2 * n + f711 n (k^2 * n) := by
  set F := f711 n (k^2 * n)
  have hk2n : k * (k * n) = k^2 * n := by ring
  have hkk : k ≤ k^2 := by
    have hh := Nat.mul_le_mul_left k hk
    simpa [pow_two, Nat.mul_one] using hh
  have hkn_le : k * n ≤ k^2 * n := Nat.mul_le_mul_right n hkk
  have hring : k * n + (k^2 - k) * n = k^2 * n := by
    have hadd : k + (k^2 - k) = k^2 := by omega
    rw [← Nat.add_mul, hadd]
  have h_ne : { f | PlacementM n (k^2 * n) f }.Nonempty := by
    refine ⟨n * (k^2 * n + 1), ?_⟩
    exists fun i => (i.val + 1) * (k^2 * n + 1)
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact Nat.dvd_mul_right (i.val + 1) (k^2 * n + 1)
    · intro i j hij
      have hiv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      intro heq
      have : i.val + 1 = j.val + 1 := Nat.mul_right_cancel (by omega) heq
      omega
    · intro i
      have hiv1 : 1 ≤ i.val + 1 := by omega
      have hivn : i.val + 1 ≤ n := by omega
      refine ⟨?_, ?_⟩
      · have h1 : 1 * (k^2 * n + 1) ≤ (i.val + 1) * (k^2 * n + 1) :=
          Nat.mul_le_mul_right (k^2 * n + 1) hiv1
        linarith
      · have h2 : (i.val + 1) * (k^2 * n + 1) ≤ n * (k^2 * n + 1) :=
          Nat.mul_le_mul_right (k^2 * n + 1) hivn
        show (i.val + 1) * (k^2 * n + 1) ≤ k^2 * n + n * (k^2 * n + 1)
        exact le_trans h2 (by omega)
  have hF_mem : PlacementM n (k^2 * n) F := Nat.sInf_mem h_ne
  obtain ⟨b, hb_div, hb_dist, hb_range⟩ := hF_mem
  have h_target : PlacementM (k * n) (k * n) ((k^2 - k) * n + F) := by
    let a : Fin (k * n) → ℕ := fun i =>
      if h : i.val < n then b ⟨i.val, h⟩ else k * (i.val + 1)
    have ha : ∀ i, a i = if h : i.val < n then b ⟨i.val, h⟩ else k * (i.val + 1) := fun i => rfl
    exists a
    refine ⟨?_, ?_, ?_⟩
    · intro i; rw [ha]
      by_cases h : i.val < n
      · rw [dif_pos h]; exact hb_div ⟨i.val, h⟩
      · rw [dif_neg h]; exact dvd_mul_left (i.val + 1) k
    · intro i j hij; rw [ha i, ha j]
      by_cases hi : i.val < n
      · by_cases hj : j.val < n
        · rw [dif_pos hi, dif_pos hj]
          exact hb_dist ⟨i.val, hi⟩ ⟨j.val, hj⟩
            (fun h => hij (Fin.ext ((@Fin.ext_iff n ⟨i.val, hi⟩ ⟨j.val, hj⟩).mp h)))
        · rw [dif_pos hi, dif_neg hj]
          have hb_gt : k^2 * n < b ⟨i.val, hi⟩ := (hb_range ⟨i.val, hi⟩).1
          have hjl : j.val + 1 ≤ k * n := by omega
          have hkj : k * (j.val + 1) ≤ k * (k * n) := Nat.mul_le_mul_left k hjl
          linarith
      · by_cases hj : j.val < n
        · rw [dif_neg hi, dif_pos hj]
          have hb_gt : k^2 * n < b ⟨j.val, hj⟩ := (hb_range ⟨j.val, hj⟩).1
          have hil : i.val + 1 ≤ k * n := by omega
          have hki : k * (i.val + 1) ≤ k * (k * n) := Nat.mul_le_mul_left k hil
          linarith
        · rw [dif_neg hi, dif_neg hj]
          have hiv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          intro heq
          have hk0 : 0 < k := by omega
          rw [mul_comm k (i.val + 1), mul_comm k (j.val + 1)] at heq
          have : i.val + 1 = j.val + 1 := Nat.mul_right_cancel hk0 heq
          omega
    · intro i; rw [ha]
      by_cases h : i.val < n
      · rw [dif_pos h]
        have hb_gt : k^2 * n < b ⟨i.val, h⟩ := (hb_range ⟨i.val, h⟩).1
        have hb_le : b ⟨i.val, h⟩ ≤ k^2 * n + F := (hb_range ⟨i.val, h⟩).2
        refine ⟨?_, ?_⟩
        · linarith
        · linarith
      · rw [dif_neg h]
        have hil : i.val + 1 ≤ k * n := by omega
        refine ⟨?_, ?_⟩
        · exact Nat.mul_lt_mul_of_pos_left (by omega : n < i.val + 1) hk
        · have hki : k * (i.val + 1) ≤ k * (k * n) := Nat.mul_le_mul_left k hil
          linarith
  have h_bound : f711 (k * n) (k * n) ≤ (k^2 - k) * n + F := Nat.sInf_le h_target
  have heq : k * n + ((k^2 - k) * n + F) = k^2 * n + F := by linarith
  linarith

end Erdos711

namespace Erdos708

def Covers (n g : Nat) : Prop :=
  ∀ (A : Finset Nat), A.card = n → (∀ a ∈ A, 2 ≤ a) → (hA : A.Nonempty) →
    ∀ (I : Finset Nat),
      (∀ x ∈ I, x < A.max' hA) → (hI : I.Nonempty) →
      ∃ B ⊆ I, B.card ≤ g ∧ (∏ a ∈ A, (a : ℤ)) ∣ (∏ b ∈ B, (b : ℤ))

noncomputable def g708 (n : Nat) : Nat := sInf { g : Nat | Covers n g }

theorem erdos_708 :
    Tendsto (fun n : Nat => (g708 n : ℝ) / (n : ℝ)) atTop (nhds 2) := by sorry

end Erdos708

-- ============================================================================
-- GROUP E: Additive combinatorics (#3, #126, #142)
-- ============================================================================

namespace Erdos3

theorem erdos_3 :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∀ᶠ k in atTop, ∃ S : Finset ℕ,
        (S : Set ℕ) ⊆ A ∧
        (∀ x ∈ S, ∀ y ∈ S, ∀ d : ℕ, x + d = y → y + d ∉ S ∨ x = y) ∧
        S.card = k := by sorry

end Erdos3

namespace Erdos126

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ (A : Finset ℕ), A.card = n →
    f n ≤ (Nat.primeFactors
      (∑ x ∈ A, ∑ y ∈ A, if x ≠ y then x + y else 0)).card

theorem erdos_126 (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n => (f n : ℝ) / Real.log n) atTop atTop := by sorry

theorem erdos_126_bounds (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    ((fun (n : ℕ) => Real.log (n : ℝ)) =O[atTop] fun (n : ℕ) => (f n : ℝ)) ∧
    ((fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log (n : ℝ)) := by sorry

theorem erdos_126_little_o (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ) / Real.log n) := by sorry

end Erdos126

namespace Erdos142

def ContainsAP (k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ d ∧ ∀ i : Fin k, a + i * d ∈ S

def IsAPFree (k : ℕ) (S : Finset ℕ) : Prop := ¬ ContainsAP k S

noncomputable def r (k N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset ℕ, S ⊆ Finset.range (N + 1) ∧ S.card = m ∧ IsAPFree k S }

theorem erdos_142 (k : ℕ) (hk : 3 ≤ k) :
    (fun N => (r k N : ℝ)) =Θ[atTop]
    (fun N => (N : ℝ) / (Real.log (N : ℝ))^(1/((k-1 : ℝ)))) := by sorry

theorem erdos_142_strong (k : ℕ) (hk : 2 ≤ k) :
    (fun (N : ℕ) => (r k N : ℝ)) =o[atTop]
    (fun (N : ℕ) => (N : ℝ) / Real.log (N : ℝ)) := by sorry

end Erdos142

-- ============================================================================
-- GROUP F: Other (#123, #50)
-- ============================================================================

namespace Erdos123

def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧ (∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y) ∧ s.sum id = n

def PairwiseCoprime (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

def powersProduct (a b c : ℕ) : Set ℕ := {n | ∃ k l m : ℕ, n = a^k * b^l * c^m}
def powersProduct2 (a b : ℕ) : Set ℕ := {n | ∃ k l : ℕ, n = a^k * b^l}

theorem erdos_123 :
    ∀ a > 1, ∀ b > 1, ∀ c > 1, PairwiseCoprime a b c →
      IsDComplete (powersProduct a b c) := by sorry

theorem erdos_123_357 : IsDComplete (powersProduct 3 5 7) := by sorry
theorem erdos_123_23 : IsDComplete (powersProduct2 2 3) := by sorry

end Erdos123

namespace Erdos50

def HasTotientDensity (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ =>
      ((Finset.range (N + 1)).filter
        (fun n => 0 < n ∧ (Nat.totient n : ℝ) / n < c)).card / (N : ℝ))
    atTop (nhds (f c))

theorem erdos_50_schoenberg : ∃ f : ℝ → ℝ, HasTotientDensity f := by sorry
theorem erdos_50_singular (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    Continuous f ∧ ∀ x : ℝ, 0 < x → x < 1 →
      DifferentiableAt ℝ f x → deriv f x = 0 := by sorry
theorem erdos_50 (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    ¬∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∃ y > 0, DifferentiableAt ℝ f x ∧ deriv f x = y := by sorry

end Erdos50

end
end PrimeGaps
