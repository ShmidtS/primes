/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic


/-!
# Rank increment under orthogonal growth (R360)

Formal core of "What Does Model Growth Really Add?
Functional Capacity Beyond Parameters" (arXiv:2607.14571):
zero-gated function-preserving growth adds exactly `K` new
functionally independent directions — formalized here as
the rank increment of the stacked functional Jacobian under
ORTHOGONAL transversality (the new directions are dormant:
orthogonal to the old row space).

`rank_orthogonal_growth`: if the `k` new rows are linearly
independent and each is orthogonal to every old row, then
the stacked matrix has rank exactly `rank M + k`.

Decoupling moral (the paper's point, mirrored by the theorem
shape): capacity (rank) grows while the old function (row
space of M) is untouched — the increment is exact, not an
inequality.

## References

[1] arXiv:2607.14571 (2026).
-/

open Matrix

open Finset

namespace Hagi.Spectral

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vertical stack of `M : Matrix m n ℝ` and `R : Matrix k n ℝ`
as a matrix over `m ⊕ k` — the grown functional Jacobian. -/
def stackRows {k : Type*} [Fintype k] [DecidableEq k]
    (M : Matrix m n ℝ) (R : Matrix k n ℝ) : Matrix (m ⊕ k) n ℝ :=
  Matrix.of fun i c => Sum.elim (fun x => M x c) (fun y => R y c) i

/-- The new directions are dormant: every new row is
orthogonal to every old row (explicit dot product). -/
def OrthRows {k : Type*} [Fintype k]
    (M : Matrix m n ℝ) (R : Matrix k n ℝ) : Prop :=
  ∀ i j, ∑ c, M i c * R j c = 0

/-- **Rank increment under orthogonal growth** (R360): with
`k` linearly independent new rows orthogonal to all old
rows, the stacked Jacobian has rank EXACTLY
`M.rank + k` — the capacity grows by the full number of
added directions while the old row space is untouched. -/
theorem rank_orthogonal_growth {k : Type*} [Fintype k] [DecidableEq k]
    (M : Matrix m n ℝ) (R : Matrix k n ℝ)
    (hind : LinearIndependent ℝ R.row)
    (horth : OrthRows M R) :
    (stackRows M R).rank = M.rank + Fintype.card k := by
  classical
  -- the row range of the stack is the union of the two ranges
  have hrange : Set.range (stackRows M R).row
      = Set.range M.row ∪ Set.range R.row := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact Or.inl ⟨i, rfl⟩
      | inr j => exact Or.inr ⟨j, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  -- orthogonality of the two row spans (double span induction)
  have hdotgen : ∀ v ∈ Submodule.span ℝ (Set.range M.row),
      ∀ w ∈ Submodule.span ℝ (Set.range R.row),
      ∑ c, v c * w c = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro w hw
        induction hw using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨j, rfl⟩ := hy
            exact horth i j
        | zero => simp
        | add y z _ _ hy hz =>
            rw [show ∑ c, M.row i c * (y + z) c = ∑ c, M.row i c * y c
              + ∑ c, M.row i c * z c from by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun c _ => by rw [Pi.add_apply]; ring]
            rw [hy, hz]
            ring
        | smul d y _ hy =>
            rw [show ∑ c, M.row i c * (d • y) c = d * ∑ c, M.row i c * y c from by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun c _ => by rw [Pi.smul_apply, smul_eq_mul]; ring]
            rw [hy]
            ring
    | zero => intro w _; simp
    | add x y _ _ ihx ihy =>
        intro w hw
        rw [show ∑ c, (x + y) c * w c = ∑ c, x c * w c + ∑ c, y c * w c from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by rw [Pi.add_apply]; ring]
        rw [ihx w hw, ihy w hw]
        ring
    | smul d x _ ihx =>
        intro w hw
        rw [show ∑ c, (d • x) c * w c = d * ∑ c, x c * w c from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by rw [Pi.smul_apply, smul_eq_mul]; ring]
        rw [ihx w hw]
        ring
  -- hence their infimum is trivial (a self-orthogonal vector is 0)
  have hinf : Submodule.span ℝ (Set.range M.row)
      ⊓ Submodule.span ℝ (Set.range R.row) = ⊥ := by
    refine Submodule.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
    · have hzero : ∑ c, v c * v c = 0 := hdotgen v hv.1 v hv.2
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => mul_self_nonneg (v c))).mp hzero
      have hv0 : v = 0 := by
        funext c
        exact mul_self_eq_zero.mp (hall c (mem_univ c))
      rw [hv0]
      simp
    · rw [Submodule.mem_bot] at hv
      rw [hv]
      simp
  -- rank = finrank of the row span; the span splits as a sup
  rw [Matrix.rank_eq_finrank_span_row, hrange, Submodule.span_union]
  rw [Matrix.rank_eq_finrank_span_row M]
  have hfs := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (Set.range M.row))
    (Submodule.span ℝ (Set.range R.row))
  rw [hinf] at hfs
  simp at hfs
  rw [finrank_span_eq_card hind] at hfs
  linarith

/-!
## Growth directions are automatically safe (R367)

Bridge between `rank_orthogonal_growth` (R360: new dormant
rows grow the functional capacity) and the SafeQP old-domain
constraints (R348): ANY update direction lying in the span of
the new (old-gradient-orthogonal) directions interferes with
EVERY protected old gradient by exactly zero — new capacity
and old-function preservation are compatible by construction.
Growth does not have to pay a safety budget.
-/

/-- If the `k` growth directions `u` are each orthogonal to
every protected gradient `g i`, then every update `d` in
their span satisfies all hard SafeQP constraints
(`ε = 0`): zero interference with the old domains. -/
theorem span_growth_zero_interference {α κ : Type*}
    [Fintype α] [Fintype κ]
    (g : α → (n → ℝ)) (u : κ → (n → ℝ))
    (horth : ∀ i j, ∑ c, g i c * u j c = 0)
    (d : n → ℝ)
    (hd : d ∈ Submodule.span ℝ (Set.range u)) :
    ∀ i, ∑ c, g i c * d c = 0 := by
  intro i
  induction hd using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact horth i j
  | zero => simp
  | add x y _ _ ihx ihy =>
      rw [show ∑ c, g i c * (x + y) c = ∑ c, g i c * x c
        + ∑ c, g i c * y c from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [Pi.add_apply]; ring]
      rw [ihx, ihy]
      ring
  | smul a x _ ihx =>
      rw [show ∑ c, g i c * (a • x) c = a * ∑ c, g i c * x c from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by
          rw [Pi.smul_apply, smul_eq_mul]; ring]
      rw [ihx]
      ring

end Hagi.Spectral

