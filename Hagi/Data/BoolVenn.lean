import Mathlib.Tactic

/-!
# Boolean Venn lattice: the 16 two-variable boolean functions

Track B7 (master plan v3 addendum A4), C242. Every `Bool → Bool → Bool`
function is a Venn mask: a lookup `Fin 4 → Bool` indexed by the atom
(active conjunction) of its input (`.vennBool`, `.venn_universal`).
All 16 functions carry the structure of the four-atom boolean lattice:
rank histogram `1-4-6-4-1` by number of active atoms (`.rank_histogram`),
complement-mask De Morgan involution on the SAME inputs
(`.de_morgan`, `.de_morgan_involution` — the negated-inputs variant is
FALSE: the atom index of negated inputs is `3 - k`, not `k`), and
exactly 32 ORIENTED Hasse cover edges (Hamming distance 1 AND strictly
increasing rank, `.hasse_edges`; the naive un-oriented count is 64).

Everything here is `decide`-level on the Bool carrier. The ReLU-neuron
realization of the same lattice and its certified-exact head live in
`Hagi.Model.Logic.VennHead`.
-/

namespace Hagi.Data.BoolVenn

/-- Atom index of a Bool input pair (order: `tt,tt`=0, `tt,ff`=1,
`ff,tt`=2, `ff,ff`=3). -/
def atomIdx (a b : Bool) : Fin 4 :=
  if a then (if b then 0 else 1) else (if b then 2 else 3)

/-- Venn evaluation: a mask is a truth table, evaluation is lookup at
the atom index. -/
def vennBool (m : Fin 4 → Bool) (a b : Bool) : Bool := m (atomIdx a b)

/-- Universality: every two-variable Bool function IS a Venn mask
(16 functions × 4 inputs = 64 cases, constructor-level). -/
theorem venn_universal (f : Bool → Bool → Bool) :
    ∃ m : Fin 4 → Bool, ∀ a b, vennBool m a b = f a b := by
  refine ⟨![f true true, f true false, f false true, f false false], ?_⟩
  intro a b
  cases a <;> cases b <;> rfl

/-- Rank of a mask: number of active atoms. -/
def maskRank (m : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k)).card

/-- Rank histogram `1-4-6-4-1`: the binomial counts `C(4,r)` of the
sixteen masks by rank (all 16 masks enumerated). -/
theorem rank_histogram (r : Fin 5) :
    (Finset.univ.filter (fun m : Fin 4 → Bool => maskRank m = (r : ℕ))).card
      = ![1, 4, 6, 4, 1] r := by
  fin_cases r <;> decide

/-- Mask complement (flip every atom). -/
def mcomp (m : Fin 4 → Bool) : Fin 4 → Bool := fun k => !m k

/-- De Morgan: complementing the mask negates the function on the SAME
inputs (the lattice involution; NOT the negated-inputs variant, which
is false — the atom index of negated inputs is `3 - k`). -/
theorem de_morgan :
    ∀ (m : Fin 4 → Bool) (a b : Bool),
      vennBool (mcomp m) a b = !(vennBool m a b) := by
  decide

/-- De Morgan involution: double complement is identity. -/
theorem de_morgan_involution :
    ∀ m : Fin 4 → Bool, mcomp (mcomp m) = m := by
  decide

/-- Hamming distance between masks. -/
def hamming (m m' : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k ≠ m' k)).card

/-- Exactly 32 Hasse cover edges: ordered mask pairs at Hamming
distance 1 with strictly increasing rank (orientation is essential —
the un-oriented Hamming-1 count is 64). -/
theorem hasse_edges :
    (Finset.univ.filter (fun p : (Fin 4 → Bool) × (Fin 4 → Bool) =>
      hamming p.1 p.2 = 1 ∧ maskRank p.1 < maskRank p.2)).card
      = 32 := by
  decide

end Hagi.Data.BoolVenn
