/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore

set_option linter.style.header false

/-!
# Coordinate minimization as an exact KL certificate

Track E2 (addendum A9 + A9-supplement, CRAM / arXiv:2611.17309): the
single-variable free energy and the EXACT monotone certificate for soft
coordinate updates — the A9-preferred discrete alternative to Euler steps
of the continuous flow (which carry no monotonicity guarantee; the paper's
own caveat).

* `log_softDef` — `log (softDef z a) = z a − log (Σ exp z)` (softmax log
  repack; shared helper, reused by `Hagi.Energy.EnergyFlow`).
* `singleCellFreeEnergy` — `F_i(p) = (1/β)·Σ p log p + Σ hz p + c`, the
  CRAM single-variable free energy at local field `hz = h_i` with the
  `y_{-i}`-dependent constant `c` (which cancels in every difference).
* `coordinate_kl_identity` — (E2b MAIN) `F_i(p) − F_i(q_i) =
  (1/β)·klDef p q_i` with `q_i = softDef (−β·hz)` the local Gibbs
  minimizer: EXACT for every probability vector `p`, no approximation.
* `coordinate_kl_nonneg` — with `β > 0`: `0 ≤ F_i(p) − F_i(q_i)` — soft
  coordinate updates never increase the single-cell free energy.

## Honest boundaries

The identity is per-cell with the rest of the state FROZEN (`hz` and `c`
are constants of the step); it certifies single-coordinate descent only,
not joint convergence, and `q_i > 0` is automatic (softmax), so no
support ceremony is needed for `klDef p q_i`. The constant `c` cancels
exactly — it is kept in the statement only to match the CRAM form
`F_i(p_i) + C(y_{-i})`.
-/

namespace Hagi.Energy

open Hagi.Prelude (softDef klDef softDef_pos softDef_sum_one
  kl_nonneg_of_nonneg)

section SingleCell

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

omit [DecidableEq α] in
/-- Softmax log repack: `log (softDef z a) = z a − log (Σ exp z)`
(the normalizer is positive on a nonempty carrier). -/
theorem log_softDef (z : α → ℝ) (a : α) :
    Real.log (softDef z a) = z a - Real.log (∑ b, Real.exp (z b)) := by
  have hZ : 0 < ∑ b, Real.exp (z b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [softDef, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ),
    Real.log_exp]

omit [Nonempty α] [DecidableEq α] in
theorem sum_mul_right_eq (f : α → ℝ) (r : ℝ) :
    (∑ a, f a * r) = (∑ a, f a) * r :=
  (Finset.sum_mul Finset.univ f r).symm

/-- Single-variable CRAM free energy at local field `hz` with
`y_{-i}`-constant `c`: `F_i(p) = (1/β)·Σ p log p + Σ hz p + c`. -/
noncomputable def singleCellFreeEnergy (β : ℝ) (hz : α → ℝ) (c : ℝ)
    (p : α → ℝ) : ℝ :=
  (1 / β) * (∑ a, p a * Real.log (p a)) + (∑ a, hz a * p a) + c

omit [DecidableEq α] in
/-- (E2b MAIN) Exact coordinate-KL identity: for every probability vector
`p` and `β ≠ 0`, the single-cell free energy gap to the local Gibbs
minimizer `q_i = softDef (−β·hz)` is EXACTLY `(1/β)·KL(p ‖ q_i)`. -/
theorem coordinate_kl_identity (β : ℝ) (hβ : β ≠ 0) (hz : α → ℝ) (c : ℝ)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    singleCellFreeEnergy β hz c p
        - singleCellFreeEnergy β hz c (softDef (fun a => -β * hz a))
      = (1 / β) * klDef p (softDef (fun a => -β * hz a)) := by
  have hqpos : ∀ a, 0 < softDef (fun a => -β * hz a) a :=
    fun a => softDef_pos (fun a => -β * hz a) a
  have hqsum : ∑ a, softDef (fun a => -β * hz a) a = 1 := softDef_sum_one _
  have hqlog : ∀ a, Real.log (softDef (fun a => -β * hz a) a)
      = -β * hz a - Real.log (∑ b, Real.exp (-β * hz b)) :=
    fun a => log_softDef (fun a => -β * hz a) a
  have hFq : singleCellFreeEnergy β hz c (softDef (fun a => -β * hz a))
      = c - (1 / β) * Real.log (∑ b, Real.exp (-β * hz b)) := by
    rw [singleCellFreeEnergy]
    have h1 : ∀ a, softDef (fun a => -β * hz a) a
          * Real.log (softDef (fun a => -β * hz a) a)
        = softDef (fun a => -β * hz a) a * (-β * hz a)
          - Real.log (∑ b, Real.exp (-β * hz b))
            * softDef (fun a => -β * hz a) a := by
      intro a; rw [hqlog a]; ring
    rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_sub_distrib,
      ← Finset.mul_sum, hqsum, mul_one]
    have e2 : (∑ a, softDef (fun a => -β * hz a) a * (-β * hz a))
        = -β * (∑ a, hz a * softDef (fun a => -β * hz a) a) := by
      have h : ∀ a, softDef (fun a => -β * hz a) a * (-β * hz a)
          = (hz a * softDef (fun a => -β * hz a) a) * (-β) := fun a => by ring
      rw [Finset.sum_congr rfl (fun a _ => h a), Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e2]
    field_simp
    ring
  have hterm : ∀ a, p a * Real.log (p a / softDef (fun a => -β * hz a) a)
      = p a * (Real.log (p a) + β * hz a
          + Real.log (∑ b, Real.exp (-β * hz b))) := by
    intro a
    rcases lt_or_eq_of_le (hp a) with h | h
    · rw [Real.log_div (ne_of_gt h) (ne_of_gt (hqpos a)), hqlog a]
      ring
    · have h0 : p a = 0 := h.symm
      rw [h0]
      ring
  have step : (∑ a, p a * (Real.log (p a) + β * hz a
        + Real.log (∑ b, Real.exp (-β * hz b))))
      = (∑ a, p a * Real.log (p a)) + β * (∑ a, hz a * p a)
        + Real.log (∑ b, Real.exp (-β * hz b)) := by
    have h2 : ∀ a, p a * (Real.log (p a) + β * hz a
        + Real.log (∑ b, Real.exp (-β * hz b)))
        = p a * Real.log (p a) + (hz a * p a) * β
          + p a * Real.log (∑ b, Real.exp (-β * hz b)) := fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => h2 a), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    have eB : (∑ a, (hz a * p a) * β) = β * (∑ a, hz a * p a) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have eC : (∑ a, p a * Real.log (∑ b, Real.exp (-β * hz b)))
        = Real.log (∑ b, Real.exp (-β * hz b)) := by
      rw [sum_mul_right_eq, hsum, one_mul]
    rw [eB, eC]
  have hfin : ∀ x y z : ℝ, β ≠ 0 →
      (1 / β) * (x + β * y + z) = (1 / β) * x + y + (1 / β) * z := by
    intro x y z h; field_simp
  calc singleCellFreeEnergy β hz c p
          - singleCellFreeEnergy β hz c (softDef (fun a => -β * hz a))
      = ((1 / β) * (∑ a, p a * Real.log (p a)) + (∑ a, hz a * p a) + c)
          - singleCellFreeEnergy β hz c (softDef (fun a => -β * hz a)) := by
        rw [singleCellFreeEnergy]
    _ = ((1 / β) * (∑ a, p a * Real.log (p a)) + (∑ a, hz a * p a))
          + (1 / β) * Real.log (∑ b, Real.exp (-β * hz b)) := by
        rw [hFq]
        ring
    _ = (1 / β) * klDef p (softDef (fun a => -β * hz a)) := by
        rw [klDef, Finset.sum_congr rfl (fun a _ => hterm a), step, hfin _ _ _ hβ]

omit [DecidableEq α] in
/-- Soft coordinate updates never increase the single-cell free energy:
with `β > 0` the KL gap is nonnegative (`q_i > 0` automatically, so
`kl_nonneg_of_nonneg` applies with no support ceremony). -/
theorem coordinate_kl_nonneg (β : ℝ) (hβ : 0 < β) (hz : α → ℝ) (c : ℝ)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    0 ≤ singleCellFreeEnergy β hz c p
        - singleCellFreeEnergy β hz c (softDef (fun a => -β * hz a)) := by
  have hpos : 0 ≤ 1 / β := by positivity
  rw [coordinate_kl_identity β (ne_of_gt hβ) hz c p hp hsum]
  exact mul_nonneg hpos
    (kl_nonneg_of_nonneg p (softDef (fun a => -β * hz a)) hp
      (fun a => softDef_pos (fun a => -β * hz a) a) hsum
      (softDef_sum_one _))

end SingleCell

end Hagi.Energy
