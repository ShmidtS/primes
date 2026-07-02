import Mathlib
import Primes.Basic
import Primes.PrimeFree

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

open scoped BigOperators

/-! ## Von Mangoldt chain infrastructure

Based on Tao et al. (2026), arXiv:2605.00301.
Key identity: `ArithmeticFunction.vonMangoldt_sum` (∑_{q|n} Λ(q) = log n) from Mathlib.
-/

/-- Primitive set: no element divides another (Finset version). -/
def IsPrimitiveSet (A : Finset Nat) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- Erdős weight 1/(n log n). -/
noncomputable def erdosWeight (n : Nat) : ℝ := 1 / ((n : ℝ) * Real.log n)

/-- Erdős sum ∑_{n≥2 ∈ A} 1/(n log n). -/
noncomputable def erdosSum (A : Finset Nat) : ℝ :=
  ∑ n ∈ A.filter (fun n => 2 ≤ n), erdosWeight n

/-- Transition probability P(n → n/q) = Λ(q)/log n. -/
noncomputable def vonMangoldtTransition (n q : Nat) : ℝ :=
  if n ≤ 1 then 0 else (ArithmeticFunction.vonMangoldt q : ℝ) / Real.log n

/-- Divisibility chain: totally ordered subset of (N, |). -/
structure DivisibilityChain where
  seq : List Nat
  chain_nonempty : seq ≠ []
  chain_prop : ∀ i j : Nat, (hij : i < j) → (hj : j < seq.length) →
    (seq.get ⟨i, Nat.lt_trans hij hj⟩) ∣ (seq.get ⟨j, hj⟩)

/-- Entrance mass b_x(n) from Tao et al. proof. -/
noncomputable def entranceMass (x Y : Nat) (δ : ℝ) (n : Nat) : ℝ :=
  1 / ((n : ℝ) * Real.log n * (Real.log n - δ)) *
    ∑ q ∈ (Nat.divisors n).filter (fun q =>
      q < Y ∨ (Y ≤ q ∧ n / q < x)),
      (ArithmeticFunction.vonMangoldt q : ℝ)

/-- Erdős weight W(n) = 1/(n log n) is strictly decreasing for n ≥ 3.

Fundamental for primitive set bounds: W decreasing implies
∑_{a∈A} W(a) ≤ ∑_{primes p ≥ x} W(p) for primitive A ⊂ [x,∞). -/
theorem erdosWeight_strictAnti (n : Nat) (hn : 3 ≤ n) :
    erdosWeight (n + 1) < erdosWeight n := by
  unfold erdosWeight
  have h0n : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h0n1 : (0 : ℝ) < n + 1 := by exact_mod_cast (by omega : 0 < n + 1)
  have h1n : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have h1n1 : (1 : ℝ) < n + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hln : 0 < Real.log n := Real.log_pos h1n
  have hln1 : 0 < Real.log (n + 1) := Real.log_pos h1n1
  have h_nn1 : (n : ℝ) < n + 1 := by exact_mod_cast (by omega : n < n + 1)
  have h_log_lt : Real.log n < Real.log (n + 1) := Real.log_lt_log h0n h_nn1
  have h_f_lt : (n : ℝ) * Real.log n < (n + 1 : ℝ) * Real.log (n + 1) := by
    have : (n + 1 : ℝ) * Real.log (n + 1) = (n : ℝ) * Real.log (n + 1) + Real.log (n + 1) := by ring
    rw [this]
    have step1 : (n : ℝ) * Real.log n < (n : ℝ) * Real.log (n + 1) := by
      have : (n : ℝ) * Real.log (n + 1) - (n : ℝ) * Real.log n = (n : ℝ) * (Real.log (n + 1) - Real.log n) := by ring
      have hdiff : 0 < (n : ℝ) * (Real.log (n + 1) - Real.log n) := by
        have : 0 < Real.log (n + 1) - Real.log n := by linarith
        exact mul_pos h0n this
      linarith
    have step2 : 0 < Real.log (n + 1) := hln1
    linarith
  have h_dn : 0 < (n : ℝ) * Real.log n := mul_pos h0n hln
  have h_dn1 : 0 < (n + 1 : ℝ) * Real.log (n + 1) := mul_pos h0n1 hln1
  have h_goal : 1 / ((n + 1 : ℝ) * Real.log (n + 1)) < 1 / ((n : ℝ) * Real.log n) :=
    (one_div_lt_one_div h_dn1 h_dn).mpr h_f_lt
  norm_cast at h_goal ⊢

/-- Probabilities sum to 1 for n ≥ 2 (uses `ArithmeticFunction.vonMangoldt_sum`). -/
theorem vonMangoldtTransition_sums_to_one (n : Nat) (hn : 2 ≤ n) :
    ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
      vonMangoldtTransition n q = 1 := by
  have hn_not_le_1 : ¬(n ≤ 1) := by omega
  have h_trans : ∀ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
      vonMangoldtTransition n q = (ArithmeticFunction.vonMangoldt q : ℝ) / Real.log n := by
    intro q hq
    rw [vonMangoldtTransition, if_neg hn_not_le_1]
  rw [Finset.sum_congr rfl h_trans, ← Finset.sum_div]
  have h_sum : ∑ q ∈ Nat.divisors n, (ArithmeticFunction.vonMangoldt q : ℝ) = Real.log n :=
    ArithmeticFunction.vonMangoldt_sum
  have h_Λ1 : (ArithmeticFunction.vonMangoldt (1 : Nat) : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_apply_one
  have h_eq : ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
        (ArithmeticFunction.vonMangoldt q : ℝ) = Real.log n := by
    have h_split := Finset.sum_filter_add_sum_filter_not
      (s := Nat.divisors n) (f := fun q => (ArithmeticFunction.vonMangoldt q : ℝ))
        (p := fun q => 1 < q)
    have h_comp : (Nat.divisors n).filter (fun q => ¬ 1 < q) = ({1} : Finset Nat) := by
      ext q
      constructor
      · intro h
        rcases Finset.mem_filter.mp h with ⟨hd, hnle⟩
        have hq : q = 1 := by
          by_cases hq0 : q = 0
          · -- 0 is not a divisor of n ≥ 2
            rw [hq0] at hd
            rw [Nat.mem_divisors] at hd
            omega
          · omega
        simp [hq]
      · intro h
        simp only [Finset.mem_singleton] at h
        refine Finset.mem_filter.mpr ⟨by
          rw [h, Nat.mem_divisors]
          exact ⟨Nat.one_dvd n, by omega⟩, ?_⟩
        omega
    rw [h_comp, Finset.sum_singleton, h_Λ1, add_zero] at h_split
    linarith [h_sum]
  rw [h_eq]
  have h_log_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact div_self (Ne.symm (ne_of_lt h_log_pos))

/-- Chain ∩ antichain ≤ 1 point.

A divisibility chain is totally ordered by ∣, and a primitive set is an antichain:
two distinct shared elements a, b would have a∣b or b∣a, forcing a = b. -/
theorem chain_antichain_at_most_one
    (C : DivisibilityChain) (A : Finset Nat) (hA : IsPrimitiveSet A) :
    (A.filter (fun a => a ∈ C.seq)).card ≤ 1 := by
  -- Auxiliary: any two distinct elements of C.seq are comparable by ∣
  have h_comparable : ∀ (a b : Nat), a ∈ C.seq → b ∈ C.seq → a ≠ b → a ∣ b ∨ b ∣ a := by
    intro a b ha hb habne
    obtain ⟨ia, hia_eq⟩ :=
      List.exists_mem_iff_get.mp ⟨a, ⟨ha, rfl⟩⟩
    obtain ⟨ib, hib_eq⟩ :=
      List.exists_mem_iff_get.mp ⟨b, ⟨hb, rfl⟩⟩
    have hia_ne_ib : (ia : Nat) ≠ (ib : Nat) := by
      intro h
      have h_eq : ia = ib := Fin.ext h
      rw [h_eq] at hia_eq
      exact habne (hia_eq.trans hib_eq.symm)
    rcases Nat.lt_or_gt_of_ne hia_ne_ib with hlt | hgt
    · have h_dvd := C.chain_prop ia.val ib.val hlt ib.isLt
      rw [← hia_eq, ← hib_eq] at h_dvd
      exact Or.inl h_dvd
    · have h_dvd := C.chain_prop ib.val ia.val hgt ia.isLt
      rw [← hib_eq, ← hia_eq] at h_dvd
      exact Or.inr h_dvd
  by_contra h_gt
  push_neg at h_gt
  obtain ⟨a, ha_in, b, hb_in, habne⟩ := Finset.one_lt_card.mp h_gt
  rw [Finset.mem_filter] at ha_in hb_in
  obtain ⟨ha_A, ha_seq⟩ := ha_in
  obtain ⟨hb_A, hb_seq⟩ := hb_in
  rcases h_comparable a b ha_seq hb_seq habne with h_dvd | h_dvd
  · exact habne (hA a ha_A b hb_A h_dvd)
  · exact habne.symm (hA b hb_A a ha_A h_dvd)

/-- Sub-invariance: W(n) ≤ ∑ W(n/q)·P(n→n/q) for composite n.
False for primes (W(1)=0 makes RHS=0). Key inequality for Tao et al. #1196 proof. -/
theorem erdosWeight_sub_invariant (n : Nat) (hn : 2 ≤ n) (hn_comp : ¬ Nat.Prime n) :
    erdosWeight n ≤ ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
      erdosWeight (n / q) * vonMangoldtTransition n q := by
  have hn4 : 4 ≤ n := by
    by_contra h; push_neg at h
    rcases (show n = 2 ∨ n = 3 by omega) with h2 | h3
    · exact absurd (h2 ▸ Nat.prime_two) hn_comp
    · exact absurd (h3 ▸ Nat.prime_three) hn_comp
  have hn1 : 1 < n := by omega
  have hn_gt_1 : ¬(n ≤ 1) := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlogn : 0 < Real.log n := Real.log_pos (Nat.one_lt_cast.mpr hn1)
  have hnnlog : 0 < (n : ℝ) * Real.log n := mul_pos hnpos hlogn
  have hn2_le : 2 ≤ n / 2 := by omega
  have hlogn2 : 0 < Real.log (n / 2) := by
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have hn_gt_2 : (2 : ℝ) < n := Nat.cast_lt.mpr (by omega : 2 < n)
    exact Real.log_pos ((one_lt_div h2_pos).mpr hn_gt_2)
  -- Λ(n) ≤ log(n)/2 for composite n
  have hΛn : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n / 2 := by
    by_cases hpp : IsPrimePow n
    · rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
      obtain ⟨p, k, hp, hk_pos, hn_eq⟩ := (isPrimePow_nat_iff n).mp hpp
      have hk2 : 2 ≤ k := by
        by_contra h; push_neg at h; have hk1 : k = 1 := by omega
        rw [hk1, Nat.pow_one] at hn_eq; exact hn_comp (hn_eq ▸ hp)
      have hminFac : n.minFac = p := by
        have hmf_prime : n.minFac.Prime := Nat.minFac_prime (fun h => by omega)
        have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
        have hmf_dvd_pk : n.minFac ∣ p^k := hn_eq ▸ hmf_dvd
        exact Nat.prime_eq_prime_of_dvd_pow hmf_prime hp hmf_dvd_pk
      have hlogn_eq : Real.log n = k * Real.log p := by
        have hn_cast : (n : ℝ) = (p^k : ℝ) := by
          rw [hn_eq.symm, Nat.cast_pow]
        rw [hn_cast, Real.log_pow]
      have hp2 := hp.two_le
      have hp_log : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < p))
      rw [hminFac, hlogn_eq]
      have h2le : 2 * Real.log p ≤ k * Real.log p := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk2) hp_log.le
      linarith
    · rw [ArithmeticFunction.vonMangoldt_apply, if_neg hpp]; positivity
  -- Reuse vonMangoldtTransition_sums_to_one to get ∑ Λ(q) = log(n)
  have hsum_Λ : ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
      (ArithmeticFunction.vonMangoldt q : ℝ) = Real.log n := by
    have h := vonMangoldtTransition_sums_to_one n hn
    have h_trans : ∀ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
        vonMangoldtTransition n q = (ArithmeticFunction.vonMangoldt q : ℝ) / Real.log n := by
      intro q hq; rw [vonMangoldtTransition, if_neg hn_gt_1]
    have h_eq : ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
        (ArithmeticFunction.vonMangoldt q : ℝ) / Real.log n = 1 := by
      rw [← Finset.sum_congr rfl h_trans]; exact h
    rw [← Finset.sum_div] at h_eq
    exact (div_eq_one_iff_eq (ne_of_gt hlogn)).mp h_eq
  -- ∑_{q|n, 1<q<n} Λ(q) = log(n) - Λ(n)
  have hfilter_proper : ((Nat.divisors n).filter (fun q => 1 < q ∧ q < n)) =
      ((Nat.divisors n).filter (fun q => 1 < q)) \ {n} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, ne_of_lt h3⟩
    · intro ⟨⟨h1, h2⟩, h3⟩
      have hqle : q ≤ n := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp h1).1
      exact ⟨h1, h2, lt_of_le_of_ne hqle h3⟩
  have hsum_Λ_proper : ∑ q ∈ ((Nat.divisors n).filter (fun q => 1 < q ∧ q < n)),
      (ArithmeticFunction.vonMangoldt q : ℝ) = Real.log n - (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [hfilter_proper]
    have h_subset : ({n} : Finset Nat) ⊆ ((Nat.divisors n).filter (fun q => 1 < q)) := by
      intro x hx; simp only [Finset.mem_singleton] at hx
      rw [hx]
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_refl n, fun h => by omega⟩, hn1⟩
    have h_sd := Finset.sum_sdiff (f := fun q => (ArithmeticFunction.vonMangoldt q : ℝ)) h_subset
    simp only [Finset.sum_singleton] at h_sd
    linarith [h_sd, hsum_Λ]
  have hΛ_nonneg : ∀ q, 0 ≤ (ArithmeticFunction.vonMangoldt q : ℝ) := by
    intro q; rw [ArithmeticFunction.vonMangoldt_apply]; split_ifs <;> positivity
  -- Key bound: S = ∑_{1<q<n} q*Λ(q)/log(n/q) ≥ 1
  -- Proof: each q ≥ 2, log(n/q) ≤ log(n/2), so q/log(n/q) ≥ 2/log(n/2)
  -- Then S ≥ (2/log(n/2)) * ∑ Λ(q) = (2/log(n/2)) * (log(n) - Λ(n))
  -- ≥ (2/log(n/2)) * (log(n)/2) = log(n)/log(n/2) ≥ 1
  -- (cast issues with Nat vs Real division remain to be resolved)
  have h_S_ge_1 : 1 ≤ ∑ q ∈ ((Nat.divisors n).filter (fun q => 1 < q ∧ q < n)),
      (q : ℝ) * (ArithmeticFunction.vonMangoldt q : ℝ) / Real.log (n / q) := by sorry
  -- Connect: multiply both sides by n * log n > 0
  -- W(n) = 1/(n*log n) ≤ (1/(n*log n)) * S ≤ RHS
  -- (final connection requires sum manipulation with W(1)=0 handling)
  sorry

/-- **Erdős #1196** (solved Tao et al. 2026):
∑_{a∈A} 1/(a log a) ≤ 1 + o(1) for primitive A ⊂ [x,∞). -/
theorem erdos_1196_finite_bound (x : Nat) (A : Finset Nat)
    (hA_prim : IsPrimitiveSet A) (hA_range : ∀ n ∈ A, x ≤ n) (hx : 3 ≤ x) :
    erdosSum A ≤ 1 + 1 / Real.log x := by
  sorry

/-- **Erdős #164**: ∑_{n∈A} 1/(n log n) ≤ ∑_p 1/(p log p). -/
theorem erdos_primitive_set_bound_finite (A : Finset Nat)
    (hA_prim : IsPrimitiveSet A) (hA_pos : ∀ n ∈ A, 2 ≤ n)
    (hA_nonempty : A.Nonempty) :
    erdosSum A ≤ ∑ p ∈ (Finset.range (A.max' hA_nonempty + 1)).filter Nat.Prime,
      erdosWeight p := by
  sorry

/-- Largest prime factor of n (0 if n ≤ 1). -/
noncomputable def largestPrimeFactor (n : Nat) : Nat :=
  (Nat.primeFactors n).sup (fun p => p)

/-- Mertens chain bound with e^γ loss. -/
theorem mertens_chain_bound (A : Finset Nat) (hA_prim : IsPrimitiveSet A)
    (hA_pos : ∀ n ∈ A, 2 ≤ n) :
    erdosSum A ≤ Real.exp Real.eulerMascheroniConstant *
      ∑ n ∈ A, 1 / ((n : ℝ) * Real.log (largestPrimeFactor n)) := by
  sorry

/-- B_x = 1 + O_δ(1/log x). -/
theorem entranceMass_total (x Y : Nat) (δ : ℝ) (hx : 3 ≤ x) :
    ∑ n ∈ (Finset.range (2 * x)).filter (fun n => x ≤ n),
      entranceMass x Y δ n = 1 + 1 / Real.log x := by
  sorry

end
end PrimeGaps
