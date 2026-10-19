/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open scoped Classical

set_option linter.style.header false

/-!
# Site percolation on a finite square grid (Layers 1–2)

A control system for the HAGI threshold question (audit §5): a
CONCRETE random micro-dynamics from which the macro property
(crossing) emerges. Everything here is finite and exact — no
asymptotic claim is pretended.

* Layer 1 (geometry): the `L × L` grid `V = Fin L × Fin L`, the
  cell adjacency `cellAdj`, and the open-cell subgraph
  `openGraph S` (edges only between open cells).
* Layer 2 (randomness): a shared random seed `ω : V → Fin M`
  (one independent uniform level per cell), and the threshold
  filtration `openAt qv ω c = (ω c).val < qv`. Larger thresholds
  open MORE cells on the SAME seed — the standard coupling, so
  nestedness is structural.
* Crossing `crossing T B qv ω`: some cell of the top set `T` and
  some cell of the bottom set `B` are connected through open
  cells (T/B are parameters: left–right, top–bottom, or any
  boundary coupling is covered).

Theorems (audit statements 1–3, all exact):

* `crossing_mono` — opening extra cells never destroys an
  existing crossing path (statement 1): a larger threshold yields
  a supergraph of the open graph on the same seed;
* `R_monotone` — the crossing probability `R`, defined as the
  EXACT finite sum of the crossing indicator over all seed
  configurations under the uniform measure (statement 3: exact
  enumeration is definitional), is nondecreasing in the threshold
  on the same seed (statement 2) — by pointwise nestedness, no
  measure theory;
* `card_Ω` — the seed space has exactly `M ^ (L*L)` states, so
  `R` is the uniform average of the crossing indicator.

Honest boundary (audit statement 4): the lattice threshold
`p_c ≈ 0.5927` for the infinite square site percolation is NOT
derived here — no asymptotics is pretended. The bridge to HAGI
takeoff (a threshold law DERIVED from micro-dynamics rather than
assumed by a certificate) is the Layer-4 gap from the audit; this
module makes that gap concrete instead of analogical.
-/

namespace Hagi.Percolation

variable {L M : ℕ}

/-- Grid vertices. -/
abbrev V (L : ℕ) := Fin L × Fin L

/-- One adjacency step in a fixed direction (ranks). -/
def step (x y : ℕ) : Prop := x + 1 = y ∨ y + 1 = x

/-- Cell adjacency: same row or same column, one step apart. -/
def cellAdj (a b : V L) : Prop :=
  (a.1 = b.1 ∧ step a.2.val b.2.val) ∨
  (a.2 = b.2 ∧ step a.1.val b.1.val)

theorem cellAdj_symm (a b : V L) (hab : cellAdj a b) : cellAdj b a := by
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1.symm, ?_⟩
    rcases h2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · refine Or.inr ⟨h1.symm, ?_⟩
    rcases h2 with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem cellAdj_loopless (a : V L) : ¬ cellAdj a a := by
  intro hab
  rcases hab with ⟨_, h⟩ | ⟨_, h⟩
  · rcases h with h | h <;> omega
  · rcases h with h | h <;> omega

/-- The (unoriented) grid graph on all cells. -/
def cellGraph : SimpleGraph (V L) where
  Adj := cellAdj
  symm := ⟨fun a b hab => cellAdj_symm a b hab⟩
  loopless := ⟨fun a hab => cellAdj_loopless a hab⟩

/-- The open-cell subgraph: an edge exists only between two OPEN
cells of the configuration `S`. -/
def openGraph (S : V L → Prop) : SimpleGraph (V L) where
  Adj a b := cellAdj a b ∧ S a ∧ S b
  symm := ⟨fun a b hab => ⟨cellAdj_symm a b hab.1, hab.2.2, hab.2.1⟩⟩
  loopless := ⟨fun a hab => cellAdj_loopless a hab.1⟩

/-- The open cells at threshold `qv` on seed `ω`: cell `c` is open
iff its independent uniform level is below the threshold. -/
def openAt (qv : ℕ) (ω : V L → Fin M) (c : V L) : Prop :=
  (ω c).val < qv

/-- **Crossing event**: some cell of the top set `T` and some cell
of the bottom set `B` are connected through open cells. -/
def crossing (T B : V L → Prop) (qv : ℕ) (ω : V L → Fin M) : Prop :=
  ∃ a b, T a ∧ B b ∧ (openGraph (openAt qv ω)).Reachable a b

/-- **Statement 1 (audit)**: opening additional cells never
destroys an existing crossing path. Structurally: a larger
threshold yields a SUPERGRAPH of the open graph on the same
seed, and reachability is monotone under supergraphs. -/
theorem crossing_mono (T B : V L → Prop) (ω : V L → Fin M)
    {qv qv' : ℕ} (hqq : qv ≤ qv') (hc : crossing T B qv ω) :
    crossing T B qv' ω := by
  classical
  obtain ⟨a, b, hT', hB', hreach⟩ := hc
  have hSsub : ∀ c : V L, openAt qv ω c → openAt qv' ω c := fun c hc =>
    Nat.lt_of_lt_of_le hc hqq
  have hgle : openGraph (openAt qv ω) ≤ openGraph (openAt qv' ω) := by
    intro x y hxy
    exact ⟨hxy.1, hSsub _ hxy.2.1, hSsub _ hxy.2.2⟩
  exact ⟨a, b, hT', hB', SimpleGraph.Reachable.mono hgle hreach⟩

/-- The seed space: one independent uniform level per cell. -/
abbrev Ω (L M : ℕ) := V L → Fin M

/-- The `L × L` grid has exactly `L*L` cells, so the seed space
has exactly `M ^ (L*L)` configurations (statement 3: exact
enumeration is definitional). -/
theorem card_Ω : Fintype.card (Ω L M) = M ^ (L * L) := by
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, pow_mul]

/-- **R_L**: the crossing probability at threshold `qv` — the
EXACT finite sum of the crossing indicator over all seed
configurations, under the uniform measure on `Ω` (statement 3).
No sampling, no approximation. -/
noncomputable def R (M : ℕ) (T B : V L → Prop) (qv : ℕ) : ℝ :=
  ((Fintype.card (Ω L M) : ℕ) : ℝ)⁻¹
    * ∑ ω ∈ (Finset.univ : Finset (Ω L M)),
      if crossing T B qv ω then (1 : ℝ) else 0

/-- **Statement 2 (audit)**: the crossing probability does not
decrease as more cells are opened. Pointwise on the SHARED seed:
the crossing event at the smaller threshold is contained in the
event at the larger one, so
the indicator of every configuration only grows — the coupling
argument, done exactly and without measure theory. -/
theorem R_monotone (M : ℕ) (T B : V L → Prop) {qv qv' : ℕ} (hqq : qv ≤ qv') :
    R M T B qv ≤ R M T B qv' := by
  classical
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
  exact Finset.sum_le_sum fun ω _ => by
    by_cases h : crossing T B qv ω
    · rw [if_pos h, if_pos (crossing_mono T B ω hqq h)]
    · rw [if_neg h]
      by_cases h2' : crossing T B qv' ω
      · rw [if_pos h2']
        norm_num
      · rw [if_neg h2']


/-! ### Emergence jump: one cell flips the macro property -/

/-- The parity seed on the `2 × 2` grid: rank-sum mod 2. -/
def seedParity (x y : ℕ) : Fin 2 :=
  ⟨(x + y) % 2, Nat.mod_lt _ (by omega)⟩

/-- Edgeless graphs only connect a vertex to itself. -/
theorem edgeless_reachable_eq {V : Type*} {G : SimpleGraph V}
    (hno : ∀ x y : V, ¬ G.Adj x y) {u v : V} (h : G.Reachable u v) : u = v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hz _ => exact absurd hz (hno _ _)

/-- **Emergence jump witness** (Layer-3 control result): on the
`2 × 2` grid with the parity seed (`ω c` = rank-sum mod 2),
raising the threshold from `1` to `2` FLIPS the macro property:
at threshold `1` the open cells `{(0,0), (1,1)}` are mutually
non-adjacent, so no top-bottom crossing exists; at threshold `2`
the single extra cell `(0,1)` connects the halves and a
top-bottom path appears. Global capability out of ONE local
event — the qualitative transition the audit asks about,
formalized on the same seed. -/
theorem emergence_jump_witness :
    ∃ ω : V 2 → Fin 2,
      ¬ crossing (fun c : V 2 => c.1.val = 0) (fun c : V 2 => c.1.val = 1) 1 ω
      ∧ crossing (fun c : V 2 => c.1.val = 0) (fun c : V 2 => c.1.val = 1) 2 ω := by
  classical
  refine ⟨fun c => seedParity c.1.val c.2.val, ?_, ?_⟩
  · -- ¬crossing at threshold 1: open cells {(0,0), (1,1)} are non-adjacent
    rintro ⟨a, b, haT, hbB, hreach⟩
    have hno : ∀ x y : V 2, ¬ (openGraph (openAt 1
        (fun c : V 2 => seedParity c.1.val c.2.val))).Adj x y := by
      intro x y hp
      obtain ⟨hca, hx, hy⟩ := hp
      have hx1 : x = (0, 0) ∨ x = (1, 1) := by
        obtain ⟨x1, x2⟩ := x
        simp only [openAt] at hx
        have hx2 : (seedParity x1.val x2.val).val < 1 := hx
        simp only [seedParity] at hx2
        have h4 : x1.val = 0 ∨ x1.val = 1 := by
          have hlt := x1.isLt; omega
        have h5 : x2.val = 0 ∨ x2.val = 1 := by
          have hlt := x2.isLt; omega
        rcases h4 with h4 | h4
        · rcases h5 with h5 | h5
          · rw [h4, h5] at hx2
            left
            refine Prod.ext ?_ ?_
            · exact Fin.val_injective (by simp [h4])
            · exact Fin.val_injective (by simp [h5])
          · rw [h4, h5] at hx2; omega
        · rcases h5 with h5 | h5
          · rw [h4, h5] at hx2; omega
          · rw [h4, h5] at hx2
            simp only [Nat.mod_self] at hx2
            right
            refine Prod.ext ?_ ?_
            · exact Fin.val_injective (by simp [h4])
            · exact Fin.val_injective (by simp [h5])
      have hy1 : y = (0, 0) ∨ y = (1, 1) := by
        obtain ⟨y1, y2⟩ := y
        simp only [openAt] at hy
        have hy2 : (seedParity y1.val y2.val).val < 1 := hy
        simp only [seedParity] at hy2
        have h4 : y1.val = 0 ∨ y1.val = 1 := by
          have hlt := y1.isLt; omega
        have h5 : y2.val = 0 ∨ y2.val = 1 := by
          have hlt := y2.isLt; omega
        rcases h4 with h4 | h4
        · rcases h5 with h5 | h5
          · rw [h4, h5] at hy2
            left
            refine Prod.ext ?_ ?_
            · exact Fin.val_injective (by simp [h4])
            · exact Fin.val_injective (by simp [h5])
          · rw [h4, h5] at hy2; omega
        · rcases h5 with h5 | h5
          · rw [h4, h5] at hy2; omega
          · rw [h4, h5] at hy2
            simp only [Nat.mod_self] at hy2
            right
            refine Prod.ext ?_ ?_
            · exact Fin.val_injective (by simp [h4])
            · exact Fin.val_injective (by simp [h5])
      rcases hx1 with rfl | rfl <;>
      rcases hy1 with rfl | rfl
      · exact cellAdj_loopless _ hca
      · have h2 : ¬ cellAdj ((0 : Fin 2), (0 : Fin 2))
            ((1 : Fin 2), (1 : Fin 2)) := by simp [cellAdj, step]
        exact h2 hca
      · have h2 : ¬ cellAdj ((1 : Fin 2), (1 : Fin 2))
            ((0 : Fin 2), (0 : Fin 2)) := by simp [cellAdj, step]
        exact h2 hca
      · exact cellAdj_loopless _ hca
    have hab' : a = b := edgeless_reachable_eq hno hreach
    subst hab'
    have h0 : a.1.val = 0 := haT
    have h1 : a.1.val = 1 := hbB
    omega
  · -- crossing at threshold 2: the walk (0,0) → (0,1) → (1,1)
    refine ⟨(0, 0), (1, 1), rfl, rfl, ⟨?_⟩⟩
    have h01 : (openGraph (openAt 2
        (fun c : V 2 => seedParity c.1.val c.2.val))).Adj
        (0, 0) (0, 1) := by
      refine ⟨?_, ?_, ?_⟩
      · simp [cellAdj, step]
      · simp [openAt, seedParity]
      · simp [openAt, seedParity]
    have h11 : (openGraph (openAt 2
        (fun c : V 2 => seedParity c.1.val c.2.val))).Adj
        (0, 1) (1, 1) := by
      refine ⟨?_, ?_, ?_⟩
      · simp [cellAdj, step]
      · simp [openAt, seedParity]
      · simp [openAt, seedParity]
    exact SimpleGraph.Walk.cons h01
      (SimpleGraph.Walk.cons h11 SimpleGraph.Walk.nil)


/-! ### Threshold-system interface (unification with HAGI line) -/

/-- **Monotone threshold system** (the common shape behind
percolation `R` and HAGI capability models `θ`): a family of
"capability levels" indexed by an intensity, nondecreasing in the
intensity. Both `R_monotone` (percolation: intensity = threshold)
and the audit's growth-θ models (intensity = absorbed credit) are
instances of this shape, so monotone-threshold arguments — e.g.
the optimal-split Pareto dominance — transfer once, for every
system realizing the interface. -/
class ThresholdSystem (Ints : Type) [Preorder Ints] where
  /-- Capability as a function of intensity. -/
  cap : Ints → ℝ
  /-- Nondecreasing in intensity. -/
  mono : ∀ i j : Ints, i ≤ j → cap i ≤ cap j

export ThresholdSystem (cap mono)

/-- **Percolation is a threshold system**: intensity = threshold;
monotonicity is exactly `R_monotone`. -/
noncomputable def percolationSystem (L M : ℕ) (T B : V L → Prop) :
    ThresholdSystem ℕ where
  cap := R M T B
  mono := fun _i _j h => R_monotone M T B h

end Hagi.Percolation
