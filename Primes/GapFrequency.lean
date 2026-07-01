import Mathlib
import Primes.Basic

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open scoped BigOperators
open Filter

/-! ## Definitions: indicators and gap frequency -/

def natIndicator (P : Prop) [Decidable P] : Nat := if P then 1 else 0
def primeIndicator (n : Nat) : Nat := natIndicator (Nat.Prime n)

/-- `n` and `n + g` are consecutive primes with right endpoint ≤ x. -/
def ConsecutivePrimeStart (g x n : Nat) : Prop :=
  0 < g ∧ Nat.Prime n ∧ Nat.Prime (n + g) ∧ n + g ≤ x ∧
    ∀ h : Nat, h ∈ Finset.Icc 1 (g - 1) → ¬ Nat.Prime (n + h)

def primeGapTerm (g x n : Nat) : Nat :=
  natIndicator (0 < g) * primeIndicator n * primeIndicator (n + g) *
    natIndicator (n + g ≤ x) *
      (Finset.Icc 1 (g - 1)).prod (fun h => 1 - primeIndicator (n + h))

def primeGapFrequencyExact (g x : Nat) : Nat :=
  (Finset.range (x + 1)).sum (fun n => primeGapTerm g x n)

def primeCountingExact (x : Nat) : Nat :=
  ((Finset.range (x + 1)).filter Nat.Prime).card

def primeGapRelativeFrequency (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) / (primeCountingExact x : ℝ)

def pairCorrelationMainTerm (A : Nat → ℝ) (g x : Nat) : ℝ :=
  A g * (primeCountingExact x : ℝ) / (x : ℝ)

def pairCorrelationError (A : Nat → ℝ) (g x : Nat) : ℝ :=
  (primeGapFrequencyExact g x : ℝ) - pairCorrelationMainTerm A g x

/-! ## Sieve infrastructure -/

def gapPatternShifts (g : Nat) : Finset Nat :=
  insert 0 (insert g (Finset.Icc 1 (g - 1)))

def primeDividesPatternAt (g n p : Nat) : Prop :=
  Nat.Prime p ∧ ∃ h : Nat, h ∈ gapPatternShifts g ∧ p ∣ n + h

def survivesFiniteEratosthenesLayer (g n y : Nat) : Prop :=
  ∀ p : Nat, Nat.Prime p → p ≤ y → ¬ primeDividesPatternAt g n p

def arithmeticProgressionSieveCount (g x y : Nat) : Nat := by
  classical
  exact ((Finset.range (x + 1)).filter fun n =>
    0 < g ∧ n + g ≤ x ∧ survivesFiniteEratosthenesLayer g n y).card

def endpointForbiddenResidueCount (g p : Nat) : Nat :=
  if p ∣ g then 1 else 2

theorem endpointForbiddenResidueCount_prime_power (g p : Nat) (k : Nat)
    (_hp : Nat.Prime p) (hk : 0 < k) (hg : g = p ^ k) :
    endpointForbiddenResidueCount g p = 1 := by
  have hdvd : p ∣ g := by
    subst hg; refine ⟨p ^ (k - 1), ?_⟩; rw [← Nat.pow_succ']; congr 1; omega
  simp [endpointForbiddenResidueCount, hdvd]

/-! ## Mangoldt identity -/

def realPrimeIndicator (n : Nat) : ℝ := if n.Prime then 1 else 0

def normalizedMangoldtPrime (n : Nat) : ℝ :=
  if n.Prime then _root_.ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) else 0

theorem normalizedMangoldtPrime_eq_realPrimeIndicator (n : Nat) :
    normalizedMangoldtPrime n = realPrimeIndicator n := by
  unfold normalizedMangoldtPrime realPrimeIndicator
  by_cases hn : n.Prime
  · rw [if_pos hn, _root_.ArithmeticFunction.vonMangoldt_apply_prime hn, if_pos hn]
    exact div_self (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
  · simp [hn]

def normalizedMangoldtEndpointWeight (g n : Nat) : ℝ :=
  normalizedMangoldtPrime n * normalizedMangoldtPrime (n + g)

/-! ## Exact frequency: equivalence and parity -/

theorem primeGapFrequencyExact_eq_count (g x : Nat) :
    primeGapFrequencyExact g x =
      (by classical
        exact ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card) := by
  classical
  trans (Finset.range (x + 1)).sum (fun n => if ConsecutivePrimeStart g x n then 1 else 0)
  · unfold primeGapFrequencyExact
    apply Finset.sum_congr rfl
    intro n _
    unfold primeGapTerm primeIndicator natIndicator ConsecutivePrimeStart
    have hprod :
        (Finset.Icc 1 (g - 1)).prod (fun h => 1 - if Nat.Prime (n + h) then 1 else 0) =
          if (∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)) then 1 else 0 := by
      by_cases hall : ∀ h ∈ Finset.Icc 1 (g - 1), ¬ Nat.Prime (n + h)
      · rw [if_pos hall]
        exact Finset.prod_eq_one (fun h hh => by simp [hall h hh])
      · rw [if_neg hall]
        have hex : ∃ h ∈ Finset.Icc 1 (g - 1), Nat.Prime (n + h) := by
          by_contra hc; apply hall; intro h hh hp; exact hc ⟨h, hh, hp⟩
        obtain ⟨h, hh, hp⟩ := hex
        exact Finset.prod_eq_zero hh (by simp [hp])
    by_cases hgpos : 0 < g <;>
      by_cases hnprime : Nat.Prime n <;>
      by_cases hngprime : Nat.Prime (n + g) <;>
      by_cases hle : n + g ≤ x <;>
      simp [hgpos, hnprime, hngprime, hle, hprod]
  · exact Finset.sum_boole (fun n => ConsecutivePrimeStart g x n) (Finset.range (x + 1))

theorem primeGapFrequencyExact_zero_for_odd_g_gt_one (g x : Nat) (hg : Odd g) (hg1 : 1 < g) :
    primeGapFrequencyExact g x = 0 := by
  rw [primeGapFrequencyExact_eq_count]
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro n _ ⟨hgpos, hnprime, hngprime, hle, hbetween⟩
  rcases Nat.even_or_odd n with hneven | hnodd
  · have hn2 : n = 2 := hnprime.eq_two_or_odd'.resolve_right (by simpa using hneven)
    exact hbetween 1 (Finset.mem_Icc.mpr (by omega)) (by simpa [hn2] using Nat.prime_three)
  · have heven : Even (n + g) := hnodd.add_odd hg
    rcases hngprime.eq_two_or_odd' with htwo | hodd
    · have hn2 : 2 ≤ n := hnprime.two_le; omega
    · exact (by simpa using heven : ¬ Odd (n + g)) hodd

/-! ## Structural theorems: injectivity, uniqueness, sum bound -/

theorem ConsecutivePrimeStart_left_injective
    {g₁ g₂ n₁ n₂ x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n₁)
    (h2 : ConsecutivePrimeStart g₂ x n₂)
    (heq : n₁ + g₁ = n₂ + g₂) : n₁ = n₂ := by
  by_cases hlt : n₁ < n₂
  · have h2pos := h2.1
    have hmem : n₂ - n₁ ∈ Finset.Icc 1 (g₁ - 1) := Finset.mem_Icc.mpr (by omega)
    have hforbidden := h1.2.2.2.2 _ hmem
    rw [show n₁ + (n₂ - n₁) = n₂ from by omega] at hforbidden
    exact absurd h2.2.1 hforbidden
  · by_cases hgt : n₂ < n₁
    · have h1pos := h1.1
      have hmem : n₁ - n₂ ∈ Finset.Icc 1 (g₂ - 1) := Finset.mem_Icc.mpr (by omega)
      have hforbidden := h2.2.2.2.2 _ hmem
      rw [show n₂ + (n₁ - n₂) = n₁ from by omega] at hforbidden
      exact absurd h1.2.1 hforbidden
    · omega

theorem ConsecutivePrimeStart_gap_unique_for_left
    {g₁ g₂ n x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n)
    (h2 : ConsecutivePrimeStart g₂ x n) : g₁ = g₂ := by
  by_cases hlt : g₁ < g₂
  · have h1pos := h1.1
    have hmem : g₁ ∈ Finset.Icc 1 (g₂ - 1) := Finset.mem_Icc.mpr (by omega)
    exact absurd h1.2.2.1 (h2.2.2.2.2 g₁ hmem)
  · by_cases hgt : g₂ < g₁
    · have h2pos := h2.1
      have hmem : g₂ ∈ Finset.Icc 1 (g₁ - 1) := Finset.mem_Icc.mpr (by omega)
      exact absurd h2.2.2.1 (h1.2.2.2.2 g₂ hmem)
    · omega

theorem primeGapFrequencyExact_sum_le_primeCountingExact (x : Nat) :
    (Finset.range (x + 1)).sum (fun g => primeGapFrequencyExact g x) ≤
      primeCountingExact x := by
  classical
  have h_eq : ∀ g, primeGapFrequencyExact g x =
      ((Finset.range (x + 1)).filter (fun n => ConsecutivePrimeStart g x n)).card :=
    fun g => primeGapFrequencyExact_eq_count g x
  have hkey : ∀ n ∈ Finset.range (x + 1),
      (Finset.range (x + 1)).sum (fun g =>
        (if ConsecutivePrimeStart g x n then (1 : Nat) else 0)) ≤
        (if Nat.Prime n then 1 else 0) := by
    intro n _
    by_cases h : ∃ g, g ∈ Finset.range (x + 1) ∧ ConsecutivePrimeStart g x n
    · obtain ⟨g, hg, hcp⟩ := h
      have huniq : ∀ g' ∈ Finset.range (x + 1),
          ConsecutivePrimeStart g' x n → g' = g := fun g' _ hcp' =>
            (ConsecutivePrimeStart_gap_unique_for_left hcp hcp').symm
      have h_filter : (Finset.range (x + 1)).filter
          (fun g' => ConsecutivePrimeStart g' x n) = {g} := by
        ext g'; simp only [Finset.mem_filter, Finset.mem_singleton]
        refine ⟨fun ⟨hg', hcp'⟩ => huniq g' hg' hcp', ?_⟩
        rintro rfl; exact ⟨hg, hcp⟩
      rw [Finset.sum_boole, h_filter, Finset.card_singleton]
      simp [hcp.2.1]
    · have h_filter : (Finset.range (x + 1)).filter
          (fun g' => ConsecutivePrimeStart g' x n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro g' hg' hcp'; exact h ⟨g', hg', hcp'⟩
      rw [Finset.sum_boole, h_filter]
      by_cases hp : Nat.Prime n <;> simp [hp]
  simp only [h_eq, primeCountingExact, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum hkey

/-- Для каждого простого `q ≥ 3` существует предшествующее простое `p < q`
без простых в интервале `(p, q)`. -/
theorem exists_predecessor_prime (q : Nat) (_hq : Nat.Prime q) (hq3 : 3 ≤ q) :
    ∃ p : Nat, Nat.Prime p ∧ p < q ∧
      ∀ r : Nat, Nat.Prime r → p < r → r < q → False := by
  have hne : ((Finset.range q).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by decide⟩⟩
  set s := (Finset.range q).filter Nat.Prime
  have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
  refine ⟨s.max' hne, (Finset.mem_filter.mp hmax_mem).2,
          Finset.mem_range.mp (Finset.mem_filter.mp hmax_mem).1, ?_⟩
  intro r hr_pr hr_p hr_q
  have hr_mem : r ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    exact ⟨hr_q, hr_pr⟩
  have : r ≤ s.max' hne := s.le_max' r hr_mem
  omega

/-- Каждое простое `q ∈ [3, x]` даёт ровно одну пару `ConsecutivePrimeStart`. -/
theorem ConsecutivePrimeStart_exists_for_right_endpoint (x : Nat) (q : Nat)
    (hq : Nat.Prime q) (hq3 : 3 ≤ q) (hqx : q ≤ x) :
    ∃ g n, g ∈ Finset.range (x + 1) ∧ n ∈ Finset.range (x + 1) ∧
      ConsecutivePrimeStart g x n ∧ n + g = q := by
  obtain ⟨p, hp_prime, hp_lt, hp_no_between⟩ := exists_predecessor_prime q hq hq3
  refine ⟨q - p, p, Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega), ?_, by omega⟩
  · unfold ConsecutivePrimeStart; rw [← show p + (q - p) = q from by omega] at hq hqx
    refine ⟨by omega, hp_prime, hq, hqx, ?_⟩
    intro h hh hprime
    obtain ⟨hge, hle⟩ := Finset.mem_Icc.mp hh
    exact hp_no_between (p + h) hprime (by omega) (by omega)

/-- Правый конец пары `ConsecutivePrimeStart` — простое число `≥ 3`. -/
theorem ConsecutivePrimeStart_right_endpoint_ge_three {g x n : Nat}
    (h : ConsecutivePrimeStart g x n) : 3 ≤ n + g := by
  have hg := h.1; have hn := h.2.1.two_le; omega

/-- Единственность пары по правому концу: если две пары имеют одинаковый
  правый конец `q = n₁ + g₁ = n₂ + g₂`, то `n₁ = n₂` (и `g₁ = g₂`). -/
theorem ConsecutivePrimeStart_right_endpoint_injective
    {g₁ g₂ n₁ n₂ x : Nat}
    (h1 : ConsecutivePrimeStart g₁ x n₁)
    (h2 : ConsecutivePrimeStart g₂ x n₂)
    (heq : n₁ + g₁ = n₂ + g₂) : n₁ = n₂ ∧ g₁ = g₂ := by
  have hn : n₁ = n₂ := ConsecutivePrimeStart_left_injective h1 h2 heq
  have hg : g₁ = g₂ := by omega
  exact ⟨hn, hg⟩

/-! ## Conjectures -/

def mobiusPairKernel (mu : Nat → Int) (g x n : Nat) : Int :=
  (Finset.range (x + 1)).sum (fun d =>
    (Finset.range (x + 1)).sum (fun e =>
      if d * d ∣ n ∧ e * e ∣ n + g then mu d * mu e else 0))

def MobiusPairGapFormulaConjecture (mu : Nat → Int) : Prop :=
  ∀ g x : Nat,
    (primeGapFrequencyExact g x : Int) =
      (Finset.range (x + 1)).sum (fun n => mobiusPairKernel mu g x n)

def primesInArithmeticProgression (a q x : Nat) : Nat :=
  ((Finset.range (x + 1)).filter (fun n => Nat.Prime n ∧ n % q = a % q)).card

def DirichletUniformityConjecture : Prop :=
  ∀ a q : Nat, Nat.Coprime a q → 0 < q →
    Tendsto (fun x : Nat =>
      (primesInArithmeticProgression a q x : ℝ) /
        ((primeCountingExact x : ℝ) / (Nat.totient q : ℝ))) atTop (nhds 1)

def PrimeGapPseudorandomnessConjecture (A normalization : Nat → ℝ) : Prop :=
  ∀ g : Nat,
    Tendsto (fun x : Nat => pairCorrelationError A g x / normalization x) atTop (nhds 0)

end
end PrimeGaps
