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
Focus: novel statements and structural infrastructure, not computational verification.
-/

-- ============================================================================
-- GROUP A: Primitive sets (#1196 solved, #143 open)
-- ============================================================================

/-! ### #1196 (Solved 2026) — Primitive set sum ≤ 1 + o(1)

Solved by Tao et al. via von Mangoldt chains (arXiv:2605.00301).
Key identity ∑_{q|n} Λ(q) = log n avoids e^γ loss from Mertens chain. -/

namespace Erdos1196

def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → x = y

theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
      ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by
  sorry

end Erdos1196

/-! ### #143 (Prize: $500) — Well-separated set convergence

Open: ∑ 1/(x log x) < ∞. Partial (KLL25): ∑ 1/x = o(log n). -/

namespace Erdos143

def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ Set.Ioi (1 : ℝ)) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|))

theorem erdos_143_part_i :
    ∀ (A : Set ℝ), WellSeparatedSet A →
      liminf (fun x => ((A ∩ (Set.Icc 1 x)).ncard : ℝ) / x) atTop = 0 := by
  sorry

theorem erdos_143_part_ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by
  sorry

noncomputable def partialSum (A : Set ℝ) (n : ℕ) : ℝ :=
  ∑' (x : A), if (x : ℝ) ≤ (n : ℝ) then 1 / (x : ℝ) else 0

/-- KLL25: ∑_{x∈A, x≤n} 1/x = o(log n). -/
theorem erdos_143_KLL_partial (A : Set ℝ) (hA : WellSeparatedSet A) :
    (fun (n : ℕ) => partialSum A n) =o[atTop]
    (fun (n : ℕ) => Real.log (n : ℝ)) := by
  sorry

end Erdos143

-- ============================================================================
-- GROUP B: Weird numbers (#470)
-- ============================================================================

/-! ### #470 (Prize: $10) — Weird numbers

Open: odd weird numbers? Infinitely many primitive weird?
Melfi: prime gap bound ⟹ infinite primitive weird. -/

namespace Erdos470

def IsWeird (n : ℕ) : Prop :=
  (∑ d ∈ (Finset.range (n + 1)).filter (fun d => d ∣ n), d) ≥ 2 * n ∧
  ¬ ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n ∧ d < n) ∧ (∑ d ∈ S, d) = n

def PrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d : ℕ, d ∣ n → d < n → ¬ IsWeird d

/-- Open: odd weird numbers exist? -/
theorem erdos_470_part_i : ∃ n : ℕ, IsWeird n ∧ Odd n := by sorry

/-- Open: infinitely many primitive weird numbers? -/
theorem erdos_470_part_ii : Set.Infinite {n | PrimitiveWeird n} := by sorry

/-- Melfi: prime gap bound ⟹ infinite primitive weird numbers. -/
theorem erdos_470_melfi :
    (∀ᶠ n in atTop,
      (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n : ℝ) <
        (Nat.nth Nat.Prime n : ℝ)^(1/2 : ℝ) / 10) →
    Set.Infinite {n | PrimitiveWeird n} := by sorry

/-- Fang: no odd weird numbers below 10^21. -/
theorem erdos_470_fang : ∀ n < 10^21, Odd n → ¬ IsWeird n := by sorry

/-- Liddy–Riedl: odd weird ⟹ ≥ 6 prime divisors. -/
theorem erdos_470_liddy_riedl :
    ∀ n : ℕ, Odd n → IsWeird n → 6 ≤ (Nat.primeFactors n).card := by sorry

end Erdos470

-- ============================================================================
-- GROUP C: Unitary perfect numbers (#1052)
-- ============================================================================

/-! ### #1052 (Prize: $10) — Unitary perfect numbers

Known: 6, 60, 90, 87360, 146361946186458562560000. All even (AlphaProof).
Open: finitely many? -/

namespace Erdos1052

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- Open: only finitely many unitary perfect numbers? -/
theorem erdos_1052 : {n | IsUnitaryPerfect n}.Finite := by sorry

/-- AlphaProof: all unitary perfect numbers are even. -/
theorem even_of_unitary_perfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by sorry

end Erdos1052

-- ============================================================================
-- GROUP D: Covering & Jacobsthal (#687, #708, #710, #711) — ALL ORIGINAL
-- ============================================================================

/-! ### #687 (Prize: $1000) — Jacobsthal function — ORIGINAL

Y(x) = max y s.t. residue classes a_p mod p (primes p ≤ x) cover [1,y].
Iwaniec: Y(x) ≪ x². Maier-Pomerance: Y(x) ≪ x(log x)².
Erdős: '$1000 and ½ my total savings'. -/

namespace Erdos687

/-- Residue classes a_p mod p for primes p ≤ x cover [1,y]. -/
def CoversInterval (x y : Nat) (a : Nat → Nat) : Prop :=
  (∀ p : Nat, Nat.Prime p → p ≤ x → a p < p) ∧
  ∀ n : Nat, 1 ≤ n → n ≤ y →
    ∃ p : Nat, Nat.Prime p ∧ p ≤ x ∧ n % p = a p % p

noncomputable def jacobsthalY (x : Nat) : Nat :=
  sSup { y : Nat | ∃ (a : Nat → Nat), CoversInterval x y a }

/-- Maier–Pomerance: Y(x) ≤ C·x·(log x)². -/
theorem erdos_687_maier_pomerance :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Nat, 3 ≤ x →
      (jacobsthalY x : ℝ) ≤ C * (x : ℝ) * (Real.log x)^2 := by sorry

/-- Weak: Y(x) = o(x²). -/
theorem erdos_687_weak :
    Tendsto (fun x : Nat => (jacobsthalY x : ℝ) / ((x : ℝ)^2)) atTop (nhds 0) := by sorry

/-- Iwaniec: Y(x) ≪ x². -/
theorem erdos_687_iwaniec :
    ∃ C : ℝ, ∀ x : Nat, 3 ≤ x → (jacobsthalY x : ℝ) ≤ C * (x : ℝ)^2 := by sorry

/-- Y(p_m) ≥ p_m - 1.

For each n ∈ [2, p_m-1], minFac(n) is prime p < p_m with p | n, so a_p = 0 covers n.
For n = 1, use a_{p_m} = 1. -/
theorem jacobsthal_lower_from_primorial (m : Nat) (hm : 2 ≤ m) :
    (Nat.nth Nat.Prime m) - 1 ≤ jacobsthalY (Nat.nth Nat.Prime m) := by
  set p_m := Nat.nth Nat.Prime m
  have h_cover : CoversInterval p_m (p_m - 1) (fun p => if p = p_m then 1 else 0) := by
    refine ⟨?_, ?_⟩
    · intro p hp hp_le
      by_cases h : p = p_m
      · show (if p = p_m then (1:Nat) else 0) < p
        rw [if_pos h]; have : 2 ≤ p_m := (Nat.prime_nth_prime m).two_le; omega
      · show (if p = p_m then (1:Nat) else 0) < p
        rw [if_neg h]; have : 2 ≤ p := hp.two_le; omega
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
  -- BddAbove: primorial(m+1) bounds y. Key: primorial(m+1) ≡ 0 mod p for all p ≤ p_m.
  -- If y ≥ primorial(m+1), then [1, primorial(m+1)] must be covered.
  -- n = primorial(m+1) ≡ 0 (mod p) for all primes p ≤ p_m.
  -- Case 1: a_p ≠ 0 for all p ≤ p_m → n = primorial(m+1) uncovered → contradiction.
  -- Case 2: a_p = 0 for some p → n covered, but n+1 ≡ 1 (mod p) for all p | primorial(m+1).
  --   If a_p ≠ 1 for all p → n+1 uncovered → contradiction.
  --   If a_p = 1 for some p → continue... This terminates because ∏(p-1) ≥ 1 uncovered residues exist.
  -- For a complete proof, we use the simpler bound: n = primorial(m+1) itself provides
  -- the contradiction in Case 1, and in Case 2 we use n+1, etc.
  -- The full argument requires CRT; here we establish the bound structurally.
  have h_bdd : BddAbove { y : Nat | ∃ (a : Nat → Nat), CoversInterval p_m y a } := by
    refine ⟨primorial (m + 1), fun y ⟨a, ha⟩ => ?_⟩
    by_contra h_ge
    have h_y_ge_P : primorial (m + 1) ≤ y := by omega
    -- primorial(m+1) = primorial(m) * p_m, divisible by all primes ≤ p_m
    have h_P_eq : primorial (m + 1) = primorial m * p_m := primorial_succ m
    have h_P_pos : 0 < primorial (m + 1) := primorial_pos (m + 1)
    have h_P_dvd : ∀ p, Nat.Prime p → p ≤ p_m → p ∣ primorial (m + 1) := by
      intro p hp hp_le
      rw [h_P_eq]
      by_cases h_eq : p = p_m
      · rw [h_eq, Nat.mul_comm]; exact Nat.dvd_mul_right p_m (primorial m)
      · have h_lt : p < p_m := by omega
        have hd : p ∣ primorial m := prime_lt_nth_prime_dvd_primorial m p hp h_lt
        exact hd.trans (Nat.dvd_mul_right (primorial m) p_m)
    -- n = primorial(m+1): covered by ha since y ≥ primorial(m+1)
    have h_n_covered : ∃ p, Nat.Prime p ∧ p ≤ p_m ∧
      primorial (m + 1) % p = a p % p :=
      ha.2 (primorial (m + 1)) (by exact h_P_pos) (by omega)
    -- But primorial(m+1) % p = 0 for all p | primorial(m+1), so a p % p = 0, i.e. a p ≡ 0
    obtain ⟨p, hp_pr, hp_le, hp_mod⟩ := h_n_covered
    have hp_dvd_P : p ∣ primorial (m + 1) := h_P_dvd p hp_pr hp_le
    have h_P_mod : primorial (m + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hp_dvd_P
    have ha_mod : a p % p = 0 := by omega
    have ha_pp : a p < p := ha.1 p hp_pr hp_le
    have ha_zero : a p = 0 := by
      have : p * (a p / p) + a p % p = a p := Nat.div_add_mod (a p) p
      rw [ha_mod] at this
      have : a p = p * (a p / p) := by omega
      omega
    -- Now consider n = primorial(m+1) + 1: n % p = 1 for all p | primorial(m+1)
    -- If a q ≠ 1 for all q ≤ p_m with q | primorial(m+1), then n is uncovered → contradiction
    -- But some a q might equal 1. We need to iterate...
    -- The key: for each prime q ≤ p_m, a q < q, so a q can equal 0, 1, ..., q-1.
    -- After using up values 0, 1, ..., j-1 for each prime, we reach j = p-1 and
    -- a q = p-1 is the last option. After that, no more coverage possible.
    -- Total covered in one period: at most primorial(m+1) - ∏(p-1) < primorial(m+1).
    -- So some n ∈ [1, primorial(m+1)] is always uncovered.
    -- This requires the full CRT counting argument which is non-trivial in Lean.
    -- We leave this as a sorry for now — the covering construction (h_cover) is the
    -- main contribution; BddAbove is a standard analytic fact.
    sorry
  exact le_csSup h_bdd h_in

end Erdos687

/-! ### #710 (Prize: ₹2000) — ORIGINAL

f(n) = min f s.t. (n, n+f) contains distinct a_k with k | a_k.
Erdős-Pomerance: (2/√e+o(1))·n·(log n/loglog n)^{1/2} ≤ f(n) ≤ (1.7398+o(1))·n·√(log n). -/

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

/-! ### #711 (Prize: ₹1000) — ORIGINAL

f(n,m) = min f s.t. (m, m+f) contains distinct a_k with k | a_k.
van Doorn [vD26]: max_m (f(n,m)-f(n,n)) → ∞. Erdős-Pomerance: max_m f ≪ n^{3/2}. -/

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

/-! ### #708 (Prize: $100) — ORIGINAL

g(n) = min g s.t. for any A ⊂ [2,∞), |A|=n, and any I of max(A) consecutive integers,
∃ B ⊆ I, |B| ≤ g, ∏A | ∏B. Erdős-Suranyi: g(n) ≥ (2-o(1))n, g(3)=4. -/

namespace Erdos708

def Covers (n g : Nat) : Prop :=
  ∀ (A : Finset Nat), A.card = n → (∀ a ∈ A, 2 ≤ a) → (hA : A.Nonempty) →
    ∀ (I : Finset Nat),
      (∀ x ∈ I, x < A.max' hA) → (hI : I.Nonempty) →
      ∃ B ⊆ I, B.card ≤ g ∧
        (∏ a ∈ A, (a : ℤ)) ∣ (∏ b ∈ B, (b : ℤ))

noncomputable def g708 (n : Nat) : Nat := sInf { g : Nat | Covers n g }

theorem erdos_708 :
    Tendsto (fun n : Nat => (g708 n : ℝ) / (n : ℝ)) atTop (nhds 2) := by sorry

end Erdos708

-- ============================================================================
-- GROUP E: Additive combinatorics (#3, #126, #142)
-- ============================================================================

/-! ### #3 (Prize: $5000) — APs from divergent reciprocal sum

Erdős: "only way to approach Green-Tao". Bloom-Sisask: k=3. -/

namespace Erdos3

theorem erdos_3 :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∀ᶠ k in atTop, ∃ S : Finset ℕ,
        (S : Set ℕ) ⊆ A ∧
        (∀ x ∈ S, ∀ y ∈ S, ∀ d : ℕ, x + d = y → y + d ∉ S ∨ x = y) ∧
        S.card = k := by sorry

end Erdos3

/-! ### #126 (Prize: $250) — Prime factors of sums

f(n) = max m s.t. for all A with |A|=n, ∏_{a≠b}(a+b) has ≥ m prime factors.
Erdős-Turán: log n ≪ f(n) ≪ n/log n. Open: f(n)/log n → ∞. -/

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

/-- f(n) = o(n/log n) — never proved. -/
theorem erdos_126_little_o (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ) / Real.log n) := by sorry

end Erdos126

/-! ### #142 (Prize: $10000) — Asymptotic for r_k(N)

Erdős: "probably enormously difficult".
Best: Kelley-Meka (k=3), Green-Tao (k=4), Leng-Sah-Sawhney (k≥5). -/

namespace Erdos142

def ContainsAP (k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 1 ≤ d ∧ ∀ i : Fin k, a + i * d ∈ S

def IsAPFree (k : ℕ) (S : Finset ℕ) : Prop := ¬ ContainsAP k S

/-- r_k(N) = max size of k-AP-free subset of {0,...,N}. -/
noncomputable def r (k N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset ℕ, S ⊆ Finset.range (N + 1) ∧ S.card = m ∧ IsAPFree k S }

/-- Conjecture: r_k(N) ~ C_k · N / (log N)^{1/(k-1)} for k ≥ 3. -/
theorem erdos_142 (k : ℕ) (hk : 3 ≤ k) :
    (fun N => (r k N : ℝ)) =Θ[atTop]
    (fun N => (N : ℝ) / (Real.log (N : ℝ))^(1/((k-1 : ℝ)))) := by sorry

/-- Open: r_k(N) = o(N / log N). Stronger than Szemerédi (r_k(N) = o(N)). -/
theorem erdos_142_strong (k : ℕ) (hk : 2 ≤ k) :
    (fun (N : ℕ) => (r k N : ℝ)) =o[atTop]
    (fun (N : ℕ) => (N : ℝ) / Real.log (N : ℝ)) := by sorry

end Erdos142

-- ============================================================================
-- GROUP F: Other (#123, #50)
-- ============================================================================

/-! ### #123 (Prize: $250) — d-completeness

Erdős-Lewin: {3^k 5^l 7^m} is d-complete. {2^k 3^l} d-complete (Jansen). -/

namespace Erdos123

def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧
    (∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y) ∧
    s.sum id = n

def PairwiseCoprime (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

def powersProduct (a b c : ℕ) : Set ℕ :=
  {n | ∃ k l m : ℕ, n = a^k * b^l * c^m}

def powersProduct2 (a b : ℕ) : Set ℕ := {n | ∃ k l : ℕ, n = a^k * b^l}

theorem erdos_123 :
    ∀ a > 1, ∀ b > 1, ∀ c > 1, PairwiseCoprime a b c →
      IsDComplete (powersProduct a b c) := by sorry

theorem erdos_123_357 : IsDComplete (powersProduct 3 5 7) := by sorry

theorem erdos_123_23 : IsDComplete (powersProduct2 2 3) := by sorry

end Erdos123

/-! ### #50 (Prize: $250) — Totient distribution singularity

Schoenberg: density f(c) exists. Erdős: f purely singular.
Open: f' = 0 everywhere it exists. -/

namespace Erdos50

def HasTotientDensity (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ =>
      ((Finset.range (N + 1)).filter
        (fun n => 0 < n ∧ (Nat.totient n : ℝ) / n < c)).card / (N : ℝ))
    atTop (nhds (f c))

theorem erdos_50_schoenberg : ∃ f : ℝ → ℝ, HasTotientDensity f := by sorry

theorem erdos_50_singular (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    Continuous f ∧
    ∀ x : ℝ, 0 < x → x < 1 →
      DifferentiableAt ℝ f x → deriv f x = 0 := by sorry

theorem erdos_50 (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    ¬∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∃ y > 0, DifferentiableAt ℝ f x ∧ deriv f x = y := by sorry

end Erdos50

end
end PrimeGaps
