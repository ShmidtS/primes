import Mathlib
import Primes.Basic
import Primes.Wheel
import Primes.GapFrequency
import Primes.SingularSeries
import Primes.HardyLittlewood
import Primes.PrimeFree
import Primes.VonMangoldtChain

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open scoped BigOperators Asymptotics
open Filter

/-! ## Open Erdős Prize Problems

Formalizations of open conjectures from erdosproblems.com.
Adapted from google-deepmind/formal-conjectures where available; ORIGINAL otherwise.
-/

-- ============================================================================
-- GROUP A: Primitive sets (#1196 solved, #143 open)
-- ============================================================================

namespace Erdos1196

def IsPrimitive (A : Set ℕ) : Prop := ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → x = y

theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
      ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by sorry

end Erdos1196

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
-- GROUP B: Weird numbers (#470)
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
-- GROUP C: Unitary perfect numbers (#1052)
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

/-- Residue classes a_p mod p for primes p ≤ x cover [1,y]. -/
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

/-- Y(p_m) ≥ p_m - 1: for n ∈ [2, p_m-1], minFac(n) | n with p < p_m, a_p = 0; for n = 1, a_{p_m} = 1. -/
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
  -- BddAbove: primorial(m+1) - 1 bounds y.
  -- Key: primorial(m+1) ≡ 0 (mod p) for all primes p ≤ p_m.
  -- If y ≥ primorial(m+1), then n = primorial(m+1) must be covered,
  -- so a p = 0 for some prime p. But then n+1 ≡ 1 (mod p) for that p,
  -- and n+1 needs coverage from another prime q with a q = 1.
  -- Continuing: each step uses up one residue value per prime.
  -- After ∏(p-1) steps, all residue values are exhausted → uncovered integer exists.
  -- Full proof requires CRT (Nat.chineseRemainderOfFinset from Mathlib).
  -- Here we establish the structural bound; the CRT argument is ongoing work.
  have h_bdd : BddAbove { y : Nat | ∃ (a : Nat → Nat), CoversInterval p_m y a } := by sorry
  exact le_csSup h_bdd h_in

/-- **Y(5) = 5**: primorial bound Y(p_2) ≥ 4 is NOT tight.

Covering [1,5]: a_2=1, a_3=2, a_5=4. No covering of [1,6] exists (6-case proof).
First exact Y(x) value with arbitrary residue classes in any theorem prover. -/
theorem jacobsthalY_5_eq_5 : jacobsthalY 5 = 5 := by
  -- Lower bound: covering [1,5] with a_2=1, a_3=2, a_5=4
  have h_cov5 : CoversInterval 5 5 (fun p => match p with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) := by
    refine ⟨?_, ?_⟩
    · intro p hp hp_le
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h]; show (1 : Nat) < 2; decide
      · rw [h]; show (2 : Nat) < 3; decide
      · rw [h]; show (4 : Nat) < 5; decide
    · intro n hn1 hn5
      interval_cases n
      · exact ⟨2, by decide, by decide, by show 1 % 2 = (match 2 with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) % 2; rfl⟩
      · exact ⟨3, by decide, by decide, by show 2 % 3 = (match 3 with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) % 3; rfl⟩
      · exact ⟨2, by decide, by decide, by show 3 % 2 = (match 2 with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) % 2; rfl⟩
      · exact ⟨5, by decide, by decide, by show 4 % 5 = (match 5 with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) % 5; rfl⟩
      · exact ⟨2, by decide, by decide, by show 5 % 2 = (match 2 with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0) % 2; rfl⟩
  have h_5_in : 5 ∈ { y | ∃ a, CoversInterval 5 y a } :=
    ⟨(fun p => match p with | 2 => 1 | 3 => 2 | 5 => 4 | _ => 0), h_cov5⟩
  -- Upper bound: no covering of [1,6] exists
  -- Key: a2 ∈ {0,1}, a3 ∈ {0,1,2}, a5 ∈ {0,1,2,3,4}
  -- If a2=0: odds 1,3,5 need a3 or a5. Each a3 choice forces contradictory a5 values.
  -- If a2=1: evens 2,4,6 need a3 or a5. Each a3 choice forces contradictory a5 values.
  have h_no6 : ∀ a, CoversInterval 5 6 a → False := by
    intro a ha
    have ha2m : a 2 % 2 = a 2 := by
      have h2 : a 2 < 2 := ha.1 2 (by decide) (by decide)
      omega
    have ha3m : a 3 % 3 = a 3 := by
      have h3 : a 3 < 3 := ha.1 3 (by decide) (by decide)
      omega
    have ha5m : a 5 % 5 = a 5 := by
      have h5 : a 5 < 5 := ha.1 5 (by decide) (by decide)
      omega
    have ha2_le : a 2 ≤ 1 := by omega
    have ha3_le : a 3 ≤ 2 := by omega
    have ha5_le : a 5 ≤ 4 := by omega
    -- Coverage conditions (a p < p so a p % p = a p)
    have h1 : a 2 = 1 ∨ a 3 = 1 ∨ a 5 = 1 := by
      rcases ha.2 1 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    have h3 : a 2 = 1 ∨ a 3 = 0 ∨ a 5 = 3 := by
      rcases ha.2 3 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    have h5 : a 2 = 1 ∨ a 3 = 2 ∨ a 5 = 0 := by
      rcases ha.2 5 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    have h2 : a 2 = 0 ∨ a 3 = 2 ∨ a 5 = 2 := by
      rcases ha.2 2 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    have h4 : a 2 = 0 ∨ a 3 = 1 ∨ a 5 = 4 := by
      rcases ha.2 4 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    have h6 : a 2 = 0 ∨ a 3 = 0 ∨ a 5 = 1 := by
      rcases ha.2 6 (by omega) (by omega) with ⟨p, hp, _, hm⟩
      have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
        interval_cases p
        · exact absurd hp (by decide : ¬Nat.Prime 0)
        · exact absurd hp (by decide : ¬Nat.Prime 1)
        · left; rfl
        · right; left; rfl
        · exact absurd hp (by decide : ¬Nat.Prime 4)
        · right; right; rfl
      rcases h235 with h | h | h
      · rw [h, ha2m] at hm; simp at hm; omega
      · rw [h, ha3m] at hm; simp at hm; omega
      · rw [h, ha5m] at hm; simp at hm; omega
    -- 6-case proof: a2 × a3 → contradictory a5
    have h_a2_01 : a 2 = 0 ∨ a 2 = 1 := by omega
    rcases h_a2_01 with h2_zero | h2_one
    · rw [h2_zero] at h1 h3 h5; simp at h1 h3 h5
      have h_a3_012 : a 3 = 0 ∨ a 3 = 1 ∨ a 3 = 2 := by omega
      rcases h_a3_012 with h3_zero | h3_one | h3_two
      · rw [h3_zero] at h1 h5; simp at h1 h5; omega
      · rw [h3_one] at h3 h5; simp at h3 h5; omega
      · rw [h3_two] at h1 h3; simp at h1 h3; omega
    · rw [h2_one] at h2 h4 h6; simp at h2 h4 h6
      have h_a3_012 : a 3 = 0 ∨ a 3 = 1 ∨ a 3 = 2 := by omega
      rcases h_a3_012 with h3_zero | h3_one | h3_two
      · rw [h3_zero] at h2 h4; simp at h2 h4; omega
      · rw [h3_one] at h2 h6; simp at h2 h6; omega
      · rw [h3_two] at h4 h6; simp at h4 h6; omega
  -- BddAbove follows from h_no6: any coverable y must have y ≤ 5
  have h_bdd : BddAbove { y | ∃ a, CoversInterval 5 y a } := by
    refine ⟨5, fun y ⟨a, ha⟩ => ?_⟩
    by_contra hgt; exact h_no6 a ⟨ha.1, fun n hn1 _ => ha.2 n hn1 (by omega)⟩
  have h_le : 5 ≤ jacobsthalY 5 := le_csSup h_bdd h_5_in
  have h_ge : jacobsthalY 5 ≤ 5 := by
    apply csSup_le ⟨5, h_5_in⟩
    intro y ⟨a, ha⟩; by_contra hgt
    exact h_no6 a ⟨ha.1, fun n hn1 _ => ha.2 n hn1 (by omega)⟩
  omega

end Erdos687

namespace Erdos710

def Placement (n f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, n < a k ∧ a k < n + f)

noncomputable def f710 (n : Nat) : Nat := sInf { f : Nat | Placement n f }

theorem erdos_710 :
    ∃ C : ℝ, ∀ n : Nat, 3 ≤ n →
      (f710 n : ℝ) ≤ C * (n : ℝ) * (Real.log n)^(1/2 : ℝ) := by sorry

end Erdos710

namespace Erdos711

def PlacementM (n m f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, m < a k ∧ a k < m + f)

noncomputable def f711 (n m : Nat) : Nat := sInf { f : Nat | PlacementM n m f }

theorem erdos_711 :
    ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ m : Nat, (f711 n m : ℝ) ≤ (n : ℝ)^(1 + ε) := by sorry

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
