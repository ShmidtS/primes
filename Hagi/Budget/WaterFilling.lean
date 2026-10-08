/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.BitAlloc

set_option linter.style.header false

/-!
# WaterFilling: the balanced allocation EXISTS (R177)

The existence closure of R176 (`BitAlloc`): the factor-2
water-filling invariant was certified at any stable point —
but does a stable point exist? Yes: on the FINITE set of
budget-feasible bit allocations the total error attains its
minimum, and at the minimum no strictly improving transfer
can exist (it would stay inside the budget set, contradicting
minimality), so `imbalance_yields_gain` contrapositive gives
the factor-2 balance. HONEST BOUNDARY: this is an EXISTENCE
proof (via `Finset.min'`), not a construction, and the
TERMINATION OF THE GREEDY REALLOCATION LOOP is not formalized
(a strictly-improving walk on a finite set must terminate,
but that meta-argument is not a theorem here).

**Result.** `exists_balanced_allocation`: for any layer
sensitivities and any bit budget `B`, there EXISTS an
allocation f with `Σ f l ≤ B` such that every layer's error
is within a factor 2 of every other layer holding a bit:

`∀ j k, f k ≠ 0 → layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)`.

**Method.** Finite-minimum existence: allocations live in the
finite type `Fin m → Fin (B+1)` (a layer never needs more
than the whole budget), the budget slice is a filtered Finset,
nonempty (the all-zero allocation); `Finset.min'` picks the
minimizer of the total error; any improving transfer of R176
preserves the budget, so minimality forbids it — the R176
contrapositive closes the factor-2 balance.
-/

namespace Hagi.Budget

open Finset

/-- The total error of an allocation read off truncated bit
widths. -/
noncomputable def totalErrorFin (c : Fin m → ℝ) (f : Fin m → Fin (B + 1)) : ℝ :=
  ∑ l, layerError (c l) (f l)

/-- Sum decomposition at two points (the counting twin of
`totalError_two_point`). -/
theorem sum_two_point {m : ℕ} (F : Fin m → ℕ) (j k : Fin m) (hjk : j ≠ k) :
    ∑ l, F l
      = F j + F k + ∑ l ∈ (Finset.univ.erase j).erase k, F l := by
  have h1 : ∑ l ∈ Finset.univ.erase j, F l + F j = ∑ l, F l :=
    Finset.sum_erase_add Finset.univ (fun l => F l) (Finset.mem_univ j)
  have h2 : ∑ l ∈ (Finset.univ.erase j).erase k, F l + F k
      = ∑ l ∈ Finset.univ.erase j, F l :=
    Finset.sum_erase_add (Finset.univ.erase j) (fun l => F l)
      (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)
  rw [← h1, ← h2]
  ring

theorem exists_balanced_allocation {m : ℕ} (c : Fin m → ℝ) (B : ℕ)
    (hc : ∀ l, 0 ≤ c l) :
    ∃ f : Fin m → ℕ,
      (∑ l, f l ≤ B) ∧
      (∀ j k : Fin m, f k ≠ 0 →
        layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)) := by
  classical
  -- the finite budget-feasible set, in truncated bit widths
  set S : Finset (Fin m → Fin (B + 1)) :=
    Finset.univ.filter (fun f => ∑ l, (f l : ℕ) ≤ B) with hS
  have hSne : S.Nonempty :=
    ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  -- the minimizer of the total error
  obtain ⟨fstar, hfS, hmin⟩ :=
    Finset.exists_min_image S (fun f => totalErrorFin c f) hSne
  have hbudget : ∑ l, (fstar l : ℕ) ≤ B := by
    rw [hS, Finset.mem_filter] at hfS
    exact hfS.2
  refine ⟨fun l => (fstar l : ℕ), hbudget, ?_⟩
  intro j k hk
  by_contra hgt
  have himb : 2 * layerError (c k) ((fstar k : ℕ))
      < layerError (c j) ((fstar j : ℕ)) := not_le.mp hgt
  by_cases hjk : j = k
  · subst hjk
    have hnn : 0 ≤ layerError (c j) ((fstar j : ℕ)) := by
      unfold layerError
      exact div_nonneg (hc j) (by positivity)
    linarith
  -- the improving transfer, as a truncated allocation
  have hglt : totalError c
      (fun l => if l = j then (fstar j : ℕ) + 1
        else if l = k then (fstar k : ℕ) - 1 else (fstar l : ℕ))
      < totalError c (fun l => (fstar l : ℕ)) :=
    imbalance_yields_gain c (fun l => (fstar l : ℕ)) j k hjk
      (Nat.pos_iff_ne_zero.mpr hk) himb
  set gNat : Fin m → ℕ :=
    fun l => if l = j then (fstar j : ℕ) + 1
      else if l = k then (fstar k : ℕ) - 1 else (fstar l : ℕ) with hgNat
  -- budget preservation
  have hgsum : ∑ l, gNat l = ∑ l, ((fstar l : ℕ)) := by
    have hrest : ∀ l ∈ (Finset.univ.erase j).erase k,
        gNat l = (fstar l : ℕ) := by
      intro l hl
      obtain ⟨hk2, hmem⟩ := Finset.mem_erase.mp hl
      obtain ⟨hj2, _⟩ := Finset.mem_erase.mp hmem
      simp only [hgNat, hj2, hk2, ite_false, ite_false]
    have hj' : gNat j = (fstar j : ℕ) + 1 := by simp [hgNat]
    have hk' : gNat k = (fstar k : ℕ) - 1 := by
      simp [hgNat, show k ≠ j from Ne.symm hjk]
    have hkpos : (1:ℕ) ≤ (fstar k : ℕ) := Nat.pos_iff_ne_zero.mpr hk
    have hsumG : ∑ l, gNat l
        = gNat j + gNat k + ∑ l ∈ (Finset.univ.erase j).erase k, gNat l :=
        sum_two_point gNat j k hjk
    have hsumF : ∑ l, ((fstar l : ℕ))
        = (fstar j : ℕ) + (fstar k : ℕ)
          + ∑ l ∈ (Finset.univ.erase j).erase k, (fstar l : ℕ) :=
        sum_two_point (fun l => (fstar l : ℕ)) j k hjk
    have hrest2 : ∑ l ∈ (Finset.univ.erase j).erase k, gNat l
        = ∑ l ∈ (Finset.univ.erase j).erase k, (fstar l : ℕ) :=
        Finset.sum_congr rfl (fun l hl => hrest l hl)
    rw [hsumG, hsumF, hrest2, hj', hk']
    omega
  -- the transfer stays inside the truncated feasible set
  have hgle : ∀ l, gNat l ≤ B := by
    intro l
    refine le_trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))
      (le_trans (le_of_eq hgsum) hbudget)
  set gFin : Fin m → Fin (B + 1) :=
    fun l => ⟨gNat l, Nat.lt_succ_of_le (hgle l)⟩ with hgFin
  have hgcoe : ∀ l, (gFin l : ℕ) = gNat l := fun _ => rfl
  have hginS : gFin ∈ S := by
    rw [hS]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [hgcoe]
    rw [hgsum]
    exact hbudget
  have hstar : totalErrorFin c fstar ≤ totalErrorFin c gFin := hmin gFin hginS
  have hcoe : totalErrorFin c gFin = totalError c gNat :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  have hcoe2 : totalErrorFin c fstar
      = totalError c (fun l => (fstar l : ℕ)) :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hcoe, hcoe2] at hstar
  linarith

end Hagi.Budget
