/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.BitAlloc

/-!
# BitAllocTermination — the greedy exchange loop
TERMINATES

`BitAlloc.two_layer_equalize` proved balancing never hurts,
and `imbalance_yields_gain` proved a factor-2 violation
strictly improves — but the module's own docstring flagged
the missing piece: "the greedy exchange loop converging to
the balanced split (termination is existential via,
not a construction)".

The termination argument does not need a potential function
on the reals: with a FIXED total budget B, the space of
allocations is FINITE (every entry ≤ B, so allocations live
in (Fin (B+1))^n), and a strictly-improving chain is
injective into a finite set — impossible.

* `error_chain_descends` — strictly improving chains have
strictly decreasing errors at ANY two ordered times;
* `improving_chain_injective` — such a chain never repeats
an allocation;
* `no_infinite_improving_chain` — THE TERMINATION RESULT:
there is no infinite strictly-improving sequence of
fixed-budget allocations; any greedy loop that only makes
strictly improving transfers must stop, and at the stop
point `stable_factor_two` certifies factor-2 balance.
-/

open scoped BigOperators

namespace Hagi.Budget

/-- With total budget B, every entry of the allocation is
at most B (a single layer cannot hold more than the whole
budget). -/
theorem alloc_entry_le {n : ℕ} (f : Fin n → ℕ) (B : ℕ)
    (hsum : ∑ i, f i = B) (i : Fin n) : f i ≤ B := by
  have := Finset.single_le_sum (f := f)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hsum] at this
  exact this

/-- **Errors descend along the whole chain**: strict
per-step descent composes to strict descent between any two
ordered times. -/
theorem error_chain_descends {n : ℕ} (c : Fin n → ℝ)
    (seq : ℕ → (Fin n → ℕ))
    (hdec : ∀ t, totalError c (seq (t + 1)) < totalError c (seq t))
    (m k : ℕ) (hmk : m < k) :
    totalError c (seq k) < totalError c (seq m) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge m k with hlt | hge
      · have hk := hdec k
        linarith [ih hlt]
      · have heq : m = k := by omega
        rw [heq]
        exact hdec k

/-- **A strictly improving chain never repeats an
allocation**: strictly decreasing errors separate every two
distinct times (equal allocations would have equal error). -/
theorem improving_chain_injective {n : ℕ} (c : Fin n → ℝ)
    (seq : ℕ → (Fin n → ℕ))
    (hdec : ∀ t, totalError c (seq (t + 1)) < totalError c (seq t)) :
    Function.Injective seq := by
  intro t t' h
  by_contra hne
  rcases lt_trichotomy t t' with hlt | heq | hlt
  · have h1 := error_chain_descends c seq hdec t t' hlt
    rw [h] at h1
    exact lt_irrefl _ h1
  · exact hne heq
  · have h1 := error_chain_descends c seq hdec t' t hlt
    rw [← h] at h1
    exact lt_irrefl _ h1

/-- **THE TERMINATION RESULT**: there is no infinite
strictly-improving sequence of fixed-budget bit allocations.
Any greedy loop that only performs strictly improving
transfers must reach a no-gain point — where
`stable_factor_two` certifies factor-2 balance.

Proof: every allocation maps into the finite type
(Fin (B+1))^n (entries bounded by the budget), an improving
chain is injective, and the first N+1 images are pairwise
distinct — N+1 distinct elements of a finite type of size
(B+1)^n, contradiction for N ≥ (B+1)^n.
-/
theorem no_infinite_improving_chain {n : ℕ} (c : Fin n → ℝ)
    (B : ℕ) (seq : ℕ → (Fin n → ℕ))
    (hsum : ∀ t, ∑ i, seq t i = B)
    (hdec : ∀ t, totalError c (seq (t + 1)) < totalError c (seq t)) :
    False := by
  -- encode each allocation into the finite pi type
  -- (entries bounded by the budget via alloc_entry_le)
  have henc : ∀ t : ℕ, ∀ i : Fin n,
      (⟨seq t i, Nat.lt_succ_of_le
        (alloc_entry_le (seq t) B (hsum t) i)⟩ : Fin (B + 1))
      = (⟨seq t i, Nat.lt_succ_of_le
        (alloc_entry_le (seq t) B (hsum t) i)⟩ : Fin (B + 1)) :=
    fun t i => rfl
  -- the encoded chain is injective: equal encodings give
  -- equal entries (Fin.ext), and the raw chain is injective
  have hcodeinj : ∀ t t' : ℕ,
      (∀ i : Fin n,
        (⟨seq t i, Nat.lt_succ_of_le
          (alloc_entry_le (seq t) B (hsum t) i)⟩ : Fin (B + 1))
        = (⟨seq t' i, Nat.lt_succ_of_le
          (alloc_entry_le (seq t') B (hsum t') i)⟩ : Fin (B + 1)))
      → seq t = seq t' := by
    intro t t' hall
    funext i
    exact congrArg Fin.val (hall i)
  -- injective ℕ-chain into the Fintype is impossible
  set g : ℕ → (Fin n → Fin (B + 1)) := fun t i =>
    ⟨seq t i, Nat.lt_succ_of_le
      (alloc_entry_le (seq t) B (hsum t) i)⟩ with hg
  have hinj : Function.Injective g := by
    intro t t' h
    by_contra hne
    have hinj' := improving_chain_injective c seq hdec
    exact hne (hinj' (hcodeinj t t' (funext_iff.mp h)))
  let N := Fintype.card (Fin n → Fin (B + 1))
  have hset : ((Finset.range (N + 1)).image g).card = N + 1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a _ b _ hab
      exact hinj hab
  have hle : ((Finset.range (N + 1)).image g).card
      ≤ Fintype.card (Fin n → Fin (B + 1)) :=
    Finset.card_le_univ _
  omega


end Hagi.Budget
