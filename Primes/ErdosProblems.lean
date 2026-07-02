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

/-! ## Open Erdős Prize Problems — Formalized

Adapted from google-deepmind/formal-conjectures with hints from erdosproblems.com.
Problems not in DeepMind repo marked **ORIGINAL FORMALIZATION**.
-/

/-! ### Problem #1196 (Solved 2026) — Primitive set sum ≤ 1 + o(1)

**Solved** by Tao et al. (2026) using von Mangoldt chains.
DeepMind formalization: formal-conjectures/ErdosProblems/1196.lean

Hints from erdosproblems.com:
- Previous best: e^γ · π/4 + o(1) ≈ 1.399 (Lichtman)
- Lower bound from k-almost primes: ∑ ≥ 1 + O(k^{-1/2+o(1)})
- AI proof used von Mangoldt chain avoiding e^γ loss
- Key identity: ∑_{q|n} Λ(q) = log n
- Entrance mass B_x = 1 + O_δ(1/log x) for 0 < δ < log 2
-/

namespace Erdos1196

def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → x = y

theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
      ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by
  sorry

end Erdos1196

/-! ### Problem #143 (Prize: $500) — Well-separated set convergence

Hints from erdosproblems.com:
- If A is integers, condition implies A is primitive set
- Erdős [Er35] proved ∑ 1/(n log n) converges for primitive sets
- Behrend [Be35]: ∑_{x<n, x∈A} 1/x ≪ log(x)/√(loglog x)
- Erdős-Sárközy-Szemerédi [ESS67]: improved to o(·)
- **Partially resolved**: Koukoulopoulos-Lamzouri-Lichtman [KLL25] proved
  ∑ 1/x = o(log n)
- Haight: lim |A∩[1,x]|/x = 0 if elements are Q-independent
- Erdős offered $500 in [Er97c]
-/

namespace Erdos143

def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ Set.Ioi (1 : ℝ)) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |(k : ℝ) * x - y|))

/-- Part i: liminf |A ∩ [1,x]| / x = 0. -/
theorem erdos_143_part_i :
    ∀ (A : Set ℝ), WellSeparatedSet A →
      liminf (fun x => ((A ∩ (Set.Icc 1 x)).ncard : ℝ) / x) atTop = 0 := by
  sorry

/-- Part ii: ∑ 1/(x log x) is summable. -/
theorem erdos_143_part_ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by
  sorry

/-- **Partial result (KLL25)**: ∑_{x<n, x∈A} 1/x = o(log n). -/
theorem erdos_143_KLL_partial (A : Set ℝ) (hA : WellSeparatedSet A) :
    ∃ C : ℝ, ∀ (n : ℕ),
      (if 1 ≤ n then 1 / (Real.log (n : ℝ)) else 0) ≤ C := by
  sorry

end Erdos143

/-! ### Problem #470 (Prize: $10) — Weird numbers

Hints from erdosproblems.com:
- Smallest weird number: 70
- Melfi [Me15]: infinitely many primitive weird numbers, conditional on
  p_{n+1} - p_n < (1/10)√(p_n) for large n
- Fang [Fa22]: no odd weird numbers below 10^21
- Liddy-Riedl [LiRi18]: odd weird number must have ≥ 6 prime divisors
- Benkoski-Erdős [BeEr74]: weird numbers have positive density
-/

namespace Erdos470

/-- n is weird: abundant (σ(n) ≥ 2n) and not pseudoperfect. -/
def IsWeird (n : ℕ) : Prop :=
  (∑ d ∈ n.divisors, d) ≥ 2 * n ∧
  ¬ ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n ∧ d < n) ∧ (∑ d ∈ S, d) = n

def PrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d : ℕ, d ∣ n → d < n → ¬ IsWeird d

def AbundancyIndex (n : ℕ) : ℚ := (∑ d ∈ n.divisors, d) / n

/-- Part i: are there odd weird numbers? -/
theorem erdos_470_part_i : ∃ n : ℕ, IsWeird n ∧ Odd n := by
  sorry

/-- Part ii: infinitely many primitive weird numbers? -/
theorem erdos_470_part_ii : Set.Infinite {n | PrimitiveWeird n} := by
  sorry

/-- Smallest weird number is 70. -/
theorem erdos_470_smallest : (∀ n < 70, ¬ IsWeird n) ∧ IsWeird 70 := by
  sorry

/-- Melfi: prime gap bound ⟹ infinite primitive weird numbers. -/
theorem erdos_470_melfi :
    (∀ᶠ n in atTop,
      (Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n : ℝ) <
        (Nat.nth Nat.Prime n : ℝ)^(1/2 : ℝ) / 10) →
    Set.Infinite {n | PrimitiveWeird n} := by
  sorry

/-- No odd weird numbers below 10^21 (Fang). -/
theorem erdos_470_fang : ∀ n < 10^21, Odd n → ¬ IsWeird n := by
  sorry

/-- Odd weird ⟹ ≥ 6 prime divisors (Liddy–Riedl). -/
theorem erdos_470_liddy_riedl :
    ∀ n : ℕ, Odd n → IsWeird n →
      6 ≤ (Nat.primeFactors n).card := by
  sorry

end Erdos470

/-! ### Problem #1052 (Prize: $10) — Unitary perfect numbers

Hints from erdosproblems.com:
- Known: 6, 60, 90, 87360, 146361946186458562560000
- All unitary perfect numbers are even (AlphaProof formal proof exists)
- No odd unitary perfect numbers known
-/

namespace Erdos1052

def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- Are there only finitely many? -/
theorem erdos_1052 : {n | IsUnitaryPerfect n}.Finite := by
  sorry

/-- All unitary perfect numbers are even (AlphaProof). -/
theorem even_of_unitary_perfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  sorry

theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  unfold IsUnitaryPerfect properUnitaryDivisors; decide

theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  unfold IsUnitaryPerfect properUnitaryDivisors; decide

theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  unfold IsUnitaryPerfect properUnitaryDivisors; decide

end Erdos1052

/-! ### Problem #126 (Prize: $250) — Prime factors of sums

Hints from erdosproblems.com:
- Erdős-Turán [ErTu34]: log n ≪ f(n) ≪ n/log n (first joint paper)
- f(n) = o(n/log n) has never been proved
-/

namespace Erdos126

/-- f(n) = max m such that for all A with |A|=n,
  ∏_{a≠b}(a+b) has ≥ m prime factors. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ (A : Finset ℕ), A.card = n →
    f n ≤ (Nat.primeFactors
      (∑ x ∈ A, ∑ y ∈ A, if x ≠ y then x + y else 0)).card

/-- **Conjecture**: f(n)/log n → ∞. -/
theorem erdos_126 (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n => (f n : ℝ) / Real.log n) atTop atTop := by
  sorry

/-- Erdős-Turán: log n ≪ f(n) ≪ n/log n. -/
theorem erdos_126_bounds (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    ((fun (n : ℕ) => Real.log (n : ℝ)) =O[atTop] fun (n : ℕ) => (f n : ℝ)) ∧
    ((fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log (n : ℝ)) := by
  sorry

/-- f(n) = o(n/log n) — never proved. -/
theorem erdos_126_little_o (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ) / Real.log n) := by
  sorry

end Erdos126

/-! ### Problem #123 (Prize: $250) — d-completeness

Hints from erdosproblems.com:
- Erdős-Lewin [ErLe96] proved for (3,5,7)
- {2^k 3^l} is d-complete (proven by Jansen)
- Stronger: for 2^k 3^l 5^j, summands can be "snug" (ratio < 1+ε)
-/

namespace Erdos123

def IsDComplete (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ A ∧
    (∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y) ∧
    s.sum id = n

def PairwiseCoprime (a b c : ℕ) : Prop :=
  Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

def powers (a : ℕ) : Set ℕ := {n | ∃ k : ℕ, n = a^k}

/-- Product set {a^k · b^l · c^m : k,l,m ≥ 0}. -/
def powersProduct (a b c : ℕ) : Set ℕ :=
  {n | ∃ k l m : ℕ, n = a^k * b^l * c^m}

/-- **Conjecture**: {a^k b^l c^m} d-complete for coprime a,b,c > 1. -/
theorem erdos_123 :
    ∀ a > 1, ∀ b > 1, ∀ c > 1, PairwiseCoprime a b c →
      IsDComplete (powersProduct a b c) := by
  sorry

/-- Erdős-Lewin: {3^k 5^l 7^m} is d-complete. -/
theorem erdos_123_357 : IsDComplete (powersProduct 3 5 7) := by
  sorry

/-- {2^k 3^l} is d-complete. -/
def powersProduct2 (a b : ℕ) : Set ℕ := {n | ∃ k l : ℕ, n = a^k * b^l}
theorem erdos_123_23 : IsDComplete (powersProduct2 2 3) := by
  sorry

end Erdos123

/-! ### Problem #50 (Prize: $250) — Totient distribution singularity

Hints from erdosproblems.com:
- Schoenberg [Sch38] proved distribution function exists
- Erdős [Er95] proved it is purely singular
- Open: no point where f' exists and is positive
-/

namespace Erdos50

/-- Distribution function of φ(n)/n exists (Schoenberg). -/
def HasTotientDensity (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
    Tendsto (fun N : ℕ =>
      ((Finset.range (N + 1)).filter
        (fun n => 0 < n ∧ (Nat.totient n : ℝ) / n < c)).card / (N : ℝ))
    atTop (nhds (f c))

/-- **Schoenberg**: distribution function exists. -/
theorem erdos_50_schoenberg : ∃ f : ℝ → ℝ, HasTotientDensity f := by
  sorry

/-- **Erdős**: distribution is purely singular (continuous, f'=0 a.e.). -/
theorem erdos_50_singular (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    Continuous f ∧
    ∀ x : ℝ, 0 < x → x < 1 →
      DifferentiableAt ℝ f x → deriv f x = 0 := by
  sorry

/-- **Conjecture**: no x where f' exists and is positive. -/
theorem erdos_50 (f : ℝ → ℝ) (hf : HasTotientDensity f) :
    ¬∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∃ y > 0, DifferentiableAt ℝ f x ∧ deriv f x = y := by
  sorry

end Erdos50

/-! ### Problem #3 (Prize: $5000) — APs from divergent reciprocal sum

Hints from erdosproblems.com:
- Erdős thought this was the 'only way to approach' Green-Tao theorem
- Bloom-Sisask proved k=3 case
- Kelley-Meka gave better r_3(N) bounds
-/

namespace Erdos3

theorem erdos_3 :
    ∀ A : Set ℕ, (¬ Summable fun a : A ↦ 1 / (a : ℝ)) →
      ∀ᶠ k in atTop, ∃ S : Finset ℕ,
        (S : Set ℕ) ⊆ A ∧
        (∀ x ∈ S, ∀ y ∈ S, ∀ d : ℕ, x + d = y → y + d ∉ S ∨ x = y) ∧
        S.card = k := by
  sorry

end Erdos3

/-! ### Problem #142 (Prize: $10000) — Asymptotic for r_k(N)

Hints from erdosproblems.com:
- Erdős: 'probably unattackable at present', 'probably enormously difficult'
- Best bounds: Kelley-Meka (k=3), Green-Tao (k=4), Leng-Sah-Sawhney (k≥5)
- Asymptotic formula far out of reach, even for k=3
- Unknown whether r_k(n)/r_{k+1}(n) → 0 for any k ≥ 3
- Related to #3 and #139
-/

namespace Erdos142

/-- r_k(N) = max size of k-AP-free subset of {1,...,N}. -/
noncomputable def r (k N : ℕ) : ℕ := sorry

/-- **Conjecture**: asymptotic formula for r_k(N). -/
theorem erdos_142 (k : ℕ) :
    (fun (N : ℕ) => (r k N : ℝ)) =Θ[atTop] (sorry : ℕ → ℝ) := by
  sorry

/-- r_k(N) = o_k(N / log N). -/
theorem erdos_142_lower (k : ℕ) (hk : 1 < k) :
    (fun (N : ℕ) => (r k N : ℝ)) =o[atTop] (fun (N : ℕ) => (N : ℝ) / Real.log (N : ℝ)) := by
  sorry

end Erdos142

/-! ### Problem #687 (Prize: $1000) — Jacobsthal function — ORIGINAL

Hints from erdosproblems.com:
- Closely related to prime gaps (see #4)
- Best upper bound: Y(x) ≪ x² (Iwaniec [Iw78])
- Best lower bound: Y(x) ≫ x·log(x)·logloglog(x)/loglog(x)
  (Ford-Green-Konyagin-Maynard-Tao [FGKMT18])
- Maier-Pomerance conjectured: Y(x) ≪ x·(log x)^{2+o(1)}
- Erdős offered '$1000 and 1/2 my total savings'
- Not yet formalized in DeepMind formal-conjectures
-/

namespace Erdos687

/-- Covering: classes a_p mod p for primes p ≤ x cover [1,y]. -/
def CoversInterval (x y : Nat) (a : Nat → Nat) : Prop :=
  (∀ p : Nat, Nat.Prime p → p ≤ x → a p < p) ∧
  ∀ n : Nat, 1 ≤ n → n ≤ y →
    ∃ p : Nat, Nat.Prime p ∧ p ≤ x ∧ n % p = a p % p

/-- Y(x) = max y such that covering exists. -/
noncomputable def jacobsthalY (x : Nat) : Nat := sorry

/-- **Maier–Pomerance conjecture**: Y(x) ≤ C·x·(log x)². -/
theorem erdos_687_maier_pomerance :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : Nat, 3 ≤ x →
        (jacobsthalY x : ℝ) ≤ C * (x : ℝ) * (Real.log x)^2 := by
  sorry

/-- **Weak conjecture**: Y(x) = o(x²). -/
theorem erdos_687_weak :
    Tendsto (fun x : Nat => (jacobsthalY x : ℝ) / ((x : ℝ)^2)) atTop (nhds 0) := by
  sorry

/-- **Lower bound from primorial**: Y(p_m) ≥ p_m - 1.

Follows from `primorial_prime_free_interval`:
[P_m + 2, P_m + p_m - 1] has no primes, every number in it
is covered by some p_i ≤ p_{m-1} mod p_i. -/
theorem jacobsthal_lower_from_primorial (m : Nat) (hm : 2 ≤ m) :
    (Nat.nth Nat.Prime m) - 1 ≤ jacobsthalY (Nat.nth Nat.Prime m) := by
  sorry

/-- **Iwaniec upper bound**: Y(x) ≪ x². -/
theorem erdos_687_iwaniec :
    ∃ C : ℝ, ∀ x : Nat, 3 ≤ x →
      (jacobsthalY x : ℝ) ≤ C * (x : ℝ)^2 := by
  sorry

end Erdos687

/-! ### Problem #710 (Prize: ₹2000) — ORIGINAL

Hints from erdosproblems.com:
- Erdős-Pomerance: (2/√e + o(1))·n·(log n / loglog n)^{1/2} ≤ f(n)
  ≤ (1.7398+o(1))·n·√(log n)
-/

namespace Erdos710

def Placement (n f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, n < a k ∧ a k < n + f)

noncomputable def f710 (n : Nat) : Nat := sorry

theorem erdos_710 :
    ∃ C : ℝ, ∀ n : Nat, 3 ≤ n →
      (f710 n : ℝ) ≤ C * (n : ℝ) * (Real.log n)^(1/2 : ℝ) := by
  sorry

end Erdos710

/-! ### Problem #711 (Prize: ₹1000) — ORIGINAL

Hints from erdosproblems.com:
- van Doorn [vD26] answered second question affirmatively
- Erdős-Pomerance proved max_m f(n,m) ≪ n^{3/2}
-/

namespace Erdos711

def PlacementM (n m f : Nat) : Prop :=
  ∃ (a : Fin n → ℕ),
    (∀ k : Fin n, (k.val + 1) ∣ a k) ∧
    (∀ k j : Fin n, k ≠ j → a k ≠ a j) ∧
    (∀ k : Fin n, m < a k ∧ a k < m + f)

noncomputable def f711 (n m : Nat) : Nat := sorry

theorem erdos_711 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ m : Nat, (f711 n m : ℝ) ≤ (n : ℝ)^(1 + ε) := by
  sorry

end Erdos711

/-! ### Problem #708 (Prize: $100) — ORIGINAL

Hints from erdosproblems.com:
- Erdős-Suranyi proved g(n) ≥ (2-o(1))n and g(3)=4
- Erdős offered '$100 or 1000 rupees' in [Er92c]
-/

namespace Erdos708

def Covers (n g : Nat) : Prop :=
  ∀ (A : Finset Nat), A.card = n → (∀ a ∈ A, 2 ≤ a) → (hA : A.Nonempty) →
    ∀ (I : Finset Nat),
      (∀ x ∈ I, x < A.max' hA) → (hI : I.Nonempty) →
      ∃ B ⊆ I, B.card ≤ g ∧
        (∏ a ∈ A, (a : ℤ)) ∣ (∏ b ∈ B, (b : ℤ))

noncomputable def g708 (n : Nat) : Nat := sorry

theorem erdos_708 :
    Tendsto (fun n : Nat => (g708 n : ℝ) / (n : ℝ)) atTop (nhds 2) := by
  sorry

end Erdos708

end
end PrimeGaps
