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

/-- Sub-invariance: W(n) ≤ ∑ W(n/q)·P(n→n/q). Avoids e^γ loss. -/
theorem erdosWeight_sub_invariant (n : Nat) (hn : 2 ≤ n) :
    erdosWeight n ≤ ∑ q ∈ (Nat.divisors n).filter (fun q => 1 < q),
      erdosWeight (n / q) * vonMangoldtTransition n q := by
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
