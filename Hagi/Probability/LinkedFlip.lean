/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Batteries.Data.BitVec.Lemmas
import Mathlib.Data.LawfulXor.Equiv
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
Finite linked-XOR channels on raw Boolean planes. Optional no-op and
anchor-linked masks define genuine atomic events. A normalized mask PMF
maps each input through these events. Preservation of the uniform law
does not assert that empirical data is uniform or that the chain mixes.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.LinkedFlip

/-- A raw Boolean family; its finite index supplies any chosen geometry. -/
abbrev Plane (I : Type*) := I → Bool

-- Mathlib has no automatic Bool or pointwise Xor instances here.
local instance : XorOp Bool := ⟨Bool.xor⟩
local instance : Zero Bool := ⟨false⟩
local instance : LawfulXor Bool where
  xor_assoc := Bool.xor_assoc
  xor_self := Bool.xor_self
  xor_zero := Bool.xor_false
  xor_comm := Bool.xor_comm

local instance {I : Type*} : XorOp (I → Bool) := ⟨fun x y i => x i ^^^ y i⟩
local instance {I : Type*} : LawfulXor (I → Bool) where
  xor_assoc x y z := funext fun i => Bool.xor_assoc (x i) (y i) (z i)
  xor_self x := funext fun i => Bool.xor_self (x i)
  xor_zero x := funext fun i => Bool.xor_false (x i)
  xor_comm x y := funext fun i => Bool.xor_comm (x i) (y i)

/-- Pointwise Boolean XOR on a raw plane. -/
def flip {I : Type*} (x m : Plane I) : Plane I := fun i => Bool.xor (x i) (m i)

theorem flip_comm {I : Type*} (x m : Plane I) : flip x m = flip m x := by
  exact xor_comm x m

/-- Applying the same mask twice restores the input. -/
theorem flip_flip {I : Type*} (x m : Plane I) : flip (flip x m) m = x := by
  funext i
  simp [flip]

/-- The identity mask is an explicit no-op event. -/
def zeroMask (I : Type*) : Plane I := fun _ => false

theorem flip_zero {I : Type*} (x : Plane I) : flip x (zeroMask I) = x := by
  funext i
  simp [flip, zeroMask]

section Support

variable {I : Type*} [Fintype I]

/-- The finite support of a Boolean mask. -/
noncomputable def support (m : Plane I) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => m i)

/-- The finite number of coordinates differing between two planes. -/
noncomputable def changedCount (x y : Plane I) : ℕ :=
  (Finset.univ.filter (fun i => x i != y i)).card

/-- Changed coordinates under a mask are exactly its support. -/
theorem changedCount_flip (x m : Plane I) :
    changedCount x (flip x m) = (support m).card := by
  unfold changedCount support flip
  congr 1
  ext i
  cases hx : x i <;> cases hm : m i <;> simp [hm]

/-- Outside the support, the atomic event leaves the input bit fixed. -/
theorem flip_outside_support (x m : Plane I) {i : I} (hi : i ∉ support m) :
    flip x m i = x i := by
  cases hm : m i
  · simp [flip, hm]
  · exfalso
    exact hi (by simp [support, hm])

/-- A mask containing an anchor and its supplied linked neighbors. -/
noncomputable def linkedMask {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) (a : I) : Plane I :=
  fun i => decide (i = a ∨ i ∈ neighbors a)

/-- Optional no-op, or one genuine anchor-linked event. -/
noncomputable def eventMask {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) (event : Option I) : Plane I :=
  match event with
  | none => zeroMask I
  | some a => linkedMask neighbors a

theorem linkedMask_anchor {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) (a : I) : linkedMask neighbors a a = true := by
  simp [linkedMask]

theorem linkedMask_neighbor {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) {a i : I}
    (hi : i ∈ neighbors a) : linkedMask neighbors a i = true := by
  simp [linkedMask, hi]

/-- Every anchor-linked event changes its anchor, for either input bit. -/
theorem flip_linkedMask_anchor_ne {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) (x : Plane I) (a : I) :
    flip x (linkedMask neighbors a) a ≠ x a := by
  cases hx : x a <;> simp [flip, linkedMask, hx]

/-- Every supplied linked coordinate changes in the same atomic event. -/
theorem flip_linkedMask_neighbor_ne {I : Type*} [DecidableEq I]
    (neighbors : I → Finset I) (x : Plane I) {a i : I}
    (hi : i ∈ neighbors a) : flip x (linkedMask neighbors a) i ≠ x i := by
  cases hx : x i <;> simp [flip, linkedMask, hi, hx]

/-- Linked-mask support is exactly anchor union neighbors; duplicates
are naturally coalesced by the finite set. -/
theorem support_linkedMask {I : Type*} [Fintype I] [DecidableEq I]
    (neighbors : I → Finset I) (a : I) :
    support (linkedMask neighbors a) = {a} ∪ neighbors a := by
  ext i
  simp [support, linkedMask]

theorem support_linkedMask_card_le {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (neighbors : I → Finset I)
    (hbound : ∀ a, (neighbors a).card ≤ k) (a : I) :
    (support (linkedMask neighbors a)).card ≤ k + 1 := by
  rw [support_linkedMask]
  calc
    ({a} ∪ neighbors a).card ≤ ({a} : Finset I).card + (neighbors a).card :=
      Finset.card_union_le _ _
    _ = 1 + (neighbors a).card := by simp
    _ ≤ 1 + k := Nat.add_le_add_left (hbound a) 1
    _ = k + 1 := Nat.add_comm _ _

theorem changedCount_linkedMask_le {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (neighbors : I → Finset I)
    (hbound : ∀ a, (neighbors a).card ≤ k) (x : Plane I) (a : I) :
    changedCount x (flip x (linkedMask neighbors a)) ≤ k + 1 := by
  rw [changedCount_flip]
  exact support_linkedMask_card_le neighbors hbound a

/-- Including the explicit no-op, each event changes at most k+1 bits. -/
theorem changedCount_eventMask_le {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (neighbors : I → Finset I)
    (hbound : ∀ a, (neighbors a).card ≤ k) (x : Plane I) (event : Option I) :
    changedCount x (flip x (eventMask neighbors event)) ≤ k + 1 := by
  cases event with
  | none =>
      simp [eventMask, zeroMask, changedCount, flip]
  | some a =>
      exact changedCount_linkedMask_le neighbors hbound x a

/-- General finite Boolean plane cardinality; empty indices have one state. -/
theorem card_plane (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card (Plane I) = 2 ^ Fintype.card I := by
  simp only [Plane, Fintype.card_fun, Fintype.card_bool]

end Support

section ByteView

/-- An exactly bounded row of raw bytes, not an assertion about native tensors. -/
abbrev ByteRows (T : ℕ) := Fin T → BitVec 8

/-- Bit-indexed Boolean version of a bounded byte row. -/
abbrev BytePlane (T : ℕ) := Fin T → Fin 8 → Bool

/-- Convert each eight-bit Boolean row into a byte with zero-information loss. -/
def encodeBytePlane {T : ℕ} (p : BytePlane T) : ByteRows T :=
  fun t => BitVec.ofFnLE (p t)

/-- Expose each byte as its eight indexed Boolean bits. -/
def decodeByteRows {T : ℕ} (bytes : ByteRows T) : BytePlane T :=
  fun t b => (bytes t).getLsb b

theorem decodeByteRows_encodeBytePlane {T : ℕ} (p : BytePlane T) :
    decodeByteRows (encodeBytePlane p) = p := by
  funext t b
  simp [decodeByteRows, encodeBytePlane]

theorem encodeBytePlane_decodeByteRows {T : ℕ} (bytes : ByteRows T) :
    encodeBytePlane (decodeByteRows bytes) = bytes := by
  funext t
  ext b
  simp [decodeByteRows, encodeBytePlane]

/-- Logical cardinal of the bounded raw bit representation. -/
theorem card_bytePlane (T : ℕ) : Fintype.card (BytePlane T) = 2 ^ (8 * T) := by
  simp only [BytePlane, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, ← Nat.pow_mul]

end ByteView

section Channel

variable {I : Type*} [DecidableEq I]

/-- A normalized finite linked-noise channel. The general event law is
first pushed forward to an ordinary mask law; this is not independent
bit-independent corruption. -/
noncomputable def linkedChannel (neighbors : I → Finset I)
    (ν : PMF (Option I)) (x : Plane I) : PMF (Plane I) :=
  (ν.map (eventMask neighbors)).map (flip x)

/-- Exact entry of the stochastic linked-flip kernel. -/
theorem linkedChannel_apply (neighbors : I → Finset I)
    (ν : PMF (Option I)) (x y : Plane I) :
    linkedChannel neighbors ν x y =
      (ν.map (eventMask neighbors)) (x ^^^ y) := by
  classical
  rw [linkedChannel, PMF.map_apply]
  calc
    (∑' m, if y = x ^^^ m then (ν.map (eventMask neighbors)) m else 0) =
        (if y = x ^^^ (x ^^^ y) then (ν.map (eventMask neighbors)) (x ^^^ y)
          else 0) := by
      apply tsum_eq_single
      intro m hm
      have hne : y ≠ x ^^^ m := by
        intro heq
        apply hm
        have h := congrArg (fun z => x ^^^ z) heq
        simpa using h.symm
      simp [hne]
    _ = (ν.map (eventMask neighbors)) (x ^^^ y) := by simp

/-- Kernel symmetry needs no symmetry hypothesis for the neighbor relation. -/
theorem linkedChannel_comm (neighbors : I → Finset I)
    (ν : PMF (Option I)) (x y : Plane I) :
    linkedChannel neighbors ν x y = linkedChannel neighbors ν y x := by
  rw [linkedChannel_apply, linkedChannel_apply, xor_comm x y]

/-- The no-op event chosen with probability one is the identity channel. -/
theorem linkedChannel_pure_none (neighbors : I → Finset I) (x : Plane I) :
    linkedChannel neighbors (PMF.pure none) x = PMF.pure x := by
  simp only [linkedChannel, eventMask, PMF.pure_map, flip_zero]

/-- A point-mass anchor event gives exactly that atomic linked flip. -/
theorem linkedChannel_pure_some (neighbors : I → Finset I) (x : Plane I) (a : I) :
    linkedChannel neighbors (PMF.pure (some a)) x =
      PMF.pure (flip x (linkedMask neighbors a)) := by
  simp only [linkedChannel, eventMask, PMF.pure_map]

end Channel

section Uniform

/-- Uniform probability over a finite nonempty carrier. -/
noncomputable def uniformPlane (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ => (Fintype.card α : ENNReal)⁻¹) (by
    have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos).ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hcard (by simp))

/-- Every uniform finite plane remains uniform after linked-XOR noise.
This is stationarity only, not reaching uniformity from arbitrary data. -/
theorem uniformPlane_bind {I : Type*} [Fintype I] [DecidableEq I]
    (neighbors : I → Finset I) (ν : PMF (Option I)) :
    (uniformPlane (Plane I)).bind (linkedChannel neighbors ν) = uniformPlane (Plane I) := by
  classical
  apply PMF.ext
  intro y
  have hsum : ∑ m, (ν.map (eventMask neighbors)) m = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe (ν.map (eventMask neighbors))
  rw [PMF.bind_apply, tsum_fintype]
  simp only [uniformPlane, PMF.ofFintype_apply, linkedChannel_apply]
  rw [← Finset.mul_sum]
  calc
    (Fintype.card (Plane I) : ENNReal)⁻¹ *
        ∑ x, (ν.map (eventMask neighbors)) (x ^^^ y) =
      (Fintype.card (Plane I) : ENNReal)⁻¹ *
        ∑ m, (ν.map (eventMask neighbors)) m := by
        congr 1
        apply Fintype.sum_equiv (Equiv.xor y)
        intro x
        rw [Equiv.xor_apply, xor_comm x y]
    _ = (Fintype.card (Plane I) : ENNReal)⁻¹ := by
      rw [hsum, mul_one]

end Uniform

end Hagi.Probability.LinkedFlip
