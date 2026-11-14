/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore
import Hagi.Energy.PairwiseCategorical

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

Addendum A11 bridge B1 (the FullBridge section below): the single-cell
certificate is connected to the FULL mean-field free energy
`meanFieldFreeEnergy` of `Hagi.Energy.PairwiseCategorical`:
`meanField_coordinate_update_eq_singleCell` (updating one coordinate
changes the FULL energy by exactly the single-cell delta at the local
mean-field field `meanFieldField`), then the corollaries
`meanField_coordinate_gibbs_nonincreasing` and
`meanField_coordinate_strict_drop_of_ne` (strict when p i != q_i, via
the strict positivity lemma `kl_pos_of_ne`).
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

section FullBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Helpers: sum splitting under a coordinate update -/

omit [Fintype ι] [Fintype α] [DecidableEq α] in
/-- Sum split at a member: `∑ x ∈ s, f x = f a + ∑ x ∈ s \ {a}, f x`. -/
private theorem sum_split_at (s : Finset ι) (a : ι) (h : a ∈ s) (f : ι → ℝ) :
    (∑ x ∈ s, f x) = f a + ∑ x ∈ s \ {a}, f x := by
  have he : s = insert a (s \ {a}) := by ext x; simp [h]
  conv_lhs => rw [he]
  exact Finset.sum_insert (by simp)

omit [Fintype α] [DecidableEq α] in
/-- Split an outer cell-sum under `r` that agrees with the background
`p` off cell `i`: the `i`-term carries `r i`, the rest sees `p`. -/
private theorem sum_split (f : ι → (α → ℝ) → ℝ) (p : ι → (α → ℝ)) (i : ι)
    (r : ι → (α → ℝ)) (hr : ∀ k ≠ i, r k = p k) :
    (∑ k, f k (r k)) = f i (r i) + ∑ k ∈ Finset.univ \ {i}, f k (p k) := by
  rw [sum_split_at Finset.univ i (Finset.mem_univ i) (fun k => f k (r k))]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
    rw [hr k hk.2]

omit [DecidableEq α] in
/-- Ordered-pair interaction sum split at the moved cell `i`: the
row (`k = i`), the column (`j = i`, `k ≠ i`), and the invariant rest
(both indices off `i`). This is the load-bearing invariance step of
the bridge: the rest is literally the same sum for `r` and `p`. -/
private theorem interact_split (K : ι → ι → α → α → ℝ) (p : ι → (α → ℝ))
    (i : ι) (r : ι → (α → ℝ)) (hr : ∀ k ≠ i, r k = p k) :
    (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (r k a * r j b))
      = (∑ k ∈ Finset.univ \ {i},
            ∑ j ∈ (Finset.univ \ {i}) \ {k}, ∑ a, ∑ b,
              K k j a b * (p k a * p j b))
        + (∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (r i a * p j b))
        + (∑ k ∈ Finset.univ \ {i}, ∑ a, ∑ b, K k i a b * (p k a * r i b)) := by
  classical
  have hset : ∀ k : ι, (Finset.univ \ {k}) \ {i} = (Finset.univ \ {i}) \ {k} :=
    fun k => by ext x; simp only [Finset.mem_sdiff, Finset.mem_singleton]; tauto
  have hrow : (∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (r i a * r j b))
      = ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (r i a * p j b) :=
    Finset.sum_congr rfl fun j hj => by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
      rw [hr j hj.2]
  have hinner : ∀ k ∈ Finset.univ \ {i},
      (∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (r k a * r j b))
      = (∑ j ∈ (Finset.univ \ {i}) \ {k}, ∑ a, ∑ b, K k j a b * (p k a * p j b))
        + (∑ a, ∑ b, K k i a b * (p k a * r i b)) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
    have hmem : i ∈ Finset.univ \ {k} := by simp [Ne.symm hk.2]
    have hrest : (∑ j ∈ (Finset.univ \ {i}) \ {k},
          ∑ a, ∑ b, K k j a b * (p k a * r j b))
        = ∑ j ∈ (Finset.univ \ {i}) \ {k},
            ∑ a, ∑ b, K k j a b * (p k a * p j b) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        rw [hr j hj.1.2]
    rw [sum_split_at (Finset.univ \ {k}) i hmem
        (fun j => ∑ a, ∑ b, K k j a b * (r k a * r j b)), hset k, hr k hk.2,
      hrest]
    ring
  rw [sum_split_at Finset.univ i (Finset.mem_univ i)
      (fun k => ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (r k a * r j b)),
    hrow, Finset.sum_congr rfl (fun k hk => hinner k hk), Finset.sum_add_distrib]
  ring

omit [Fintype ι] [DecidableEq ι] [DecidableEq α] in
/-- Pull an `a`-indexed factor out of a triple sum (row form). -/
private theorem pull1 (s : Finset ι) (d : α → ℝ) (F : ι → α → α → ℝ) :
    (∑ j ∈ s, ∑ a, ∑ b, d a * F j a b)
      = ∑ a, d a * (∑ j ∈ s, ∑ b, F j a b) := by
  rw [show (∑ j ∈ s, ∑ a, ∑ b, d a * F j a b)
        = ∑ a, ∑ j ∈ s, ∑ b, d a * F j a b from Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

omit [Fintype ι] [DecidableEq ι] [DecidableEq α] in
/-- Pull a `b`-indexed factor out of a triple sum (column form). -/
private theorem pull2 (s : Finset ι) (d : α → ℝ) (F : ι → α → α → ℝ) :
    (∑ j ∈ s, ∑ a, ∑ b, d b * F j a b)
      = ∑ b, d b * (∑ j ∈ s, ∑ a, F j a b) := by
  have e1 : ∀ j : ι, (∑ a, ∑ b, d b * F j a b)
      = ∑ b, d b * (∑ a, F j a b) := by
    intro j
    rw [show (∑ a, ∑ b, d b * F j a b) = ∑ b, ∑ a, d b * F j a b from
        Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => e1 j),
    show (∑ j ∈ s, ∑ b, d b * (∑ a, F j a b)) = ∑ b, ∑ j ∈ s, d b * (∑ a, F j a b) from
      Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]

/-! ### The mean-field local field -/

/-- Local mean-field field at cell `i` over marginal background `p`:
`hz(a) = B i a + (1/2)·Σ_{j≠i} Σ_b (K i j a b + K j i b a)·p j b`.
The `1/2` sits OUTSIDE the ordered double count (C260 convention), so
BOTH ordered directions enter with weight `1/2` each; under symmetric
`K` this collapses to the classic `L_i(a) = B_i(a) + Σ_{j≠i} Σ_b
K i j a b·p j b` (the marginal analogue of the discrete `localField` /
`transposeLocalField` pair of `Hagi.Energy.SingleCellDescent`). -/
noncomputable def meanFieldField (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (p : ι → (α → ℝ)) (i : ι) : α → ℝ :=
  fun a => B i a + (1 / 2) * (∑ j ∈ Finset.univ \ {i}, ∑ b,
    (K i j a b * p j b + K j i b a * p j b))

/-! ### Strict KL positivity (no support ceremony: q > 0) -/

omit [Fintype ι] in
/-- Gibbs gap strictness: `t > 0`, `t ≠ 1 ⟹ 0 < t·log t − t + 1`
(via `log (1/t) < 1/t − 1`; probe C265 P4). -/
private theorem strict_log_term (t : ℝ) (ht0 : 0 < t) (ht1 : t ≠ 1) :
    0 < t * Real.log t - t + 1 := by
  have hinv : 0 < 1 / t := by positivity
  have hne : 1 / t ≠ 1 := by
    intro h; field_simp at h; exact ht1 h.symm
  have h1 : Real.log (1 / t) < 1 / t - 1 :=
    Real.log_lt_sub_one_of_pos hinv hne
  have h2 : Real.log (1 / t) = -Real.log t := by
    rw [show (1 / t) = t⁻¹ from by field_simp, Real.log_inv]
  rw [h2] at h1
  have h3 : t * (-Real.log t) < t * (1 / t - 1) :=
    mul_lt_mul_of_pos_left h1 ht0
  have h4 : t * (1 / t - 1) = 1 - t := by field_simp
  rw [h4] at h3
  linarith

omit [Fintype ι] [DecidableEq α] in
/-- STRICT KL positivity: for probability vectors `q ≥ 0` (sums one)
and `p > 0` with `q ≠ p`, the divergence `klDef q p` is strictly
positive. Companion of the Prelude's `kl_nonneg` (which gives only
`0 ≤`): proved by the termwise Gibbs gap
`g a = q a·log (q a / p a) − (q a − p a) ≥ 0` with `g a = 0 ↔ q a = p a`
(the `q a = 0` case is exactly strict: total `Real.log` semantics make
the term vanish, leaving the gap `p a > 0`). -/
theorem kl_pos_of_ne (q p : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hp : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1) (hne : q ≠ p) :
    0 < klDef q p := by
  classical
  set g : α → ℝ := fun a => q a * Real.log (q a / p a) - (q a - p a) with hg
  have hgpos : ∀ a, 0 ≤ g a := by
    intro a
    by_cases hq0 : q a = 0
    · simp only [hg, hq0, zero_div, Real.log_zero, mul_zero,
        zero_sub, neg_neg]
      exact le_of_lt (hp a)
    · have hqa : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm hq0)
      have ht0 : 0 < q a / p a := div_pos hqa (hp a)
      have hqt : q a = (q a / p a) * p a := by
        rw [div_mul_cancel₀ (q a) (hp a).ne']
      have hkey : g a = p a * ((q a / p a) * Real.log (q a / p a)
          - (q a / p a) + 1) := by
        simp only [hg]
        linear_combination (Real.log (q a / p a) - 1) * hqt
      by_cases h1 : (q a / p a) = 1
      · have hqap : q a = p a := by
          have e : q a = (q a / p a) * p a := by
            rw [div_mul_cancel₀ (q a) (hp a).ne']
          rw [h1, one_mul] at e
          exact e
        have hga : g a = 0 := by
          simp only [hg, hqap, div_self (hp a).ne', Real.log_one, mul_zero,
            sub_self]
        rw [hga]
      · rw [hkey]
        exact (mul_pos (hp a) (strict_log_term _ ht0 h1)).le
  have hgeq : ∀ a, g a = 0 → q a = p a := by
    intro a h0
    by_cases hq0 : q a = 0
    · simp only [hg, hq0, zero_div, Real.log_zero, mul_zero,
        zero_sub, neg_neg] at h0
      exact absurd h0 (ne_of_gt (hp a))
    · have hqa : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm hq0)
      have ht0 : 0 < q a / p a := div_pos hqa (hp a)
      have hqt : q a = (q a / p a) * p a := by
        rw [div_mul_cancel₀ (q a) (hp a).ne']
      have hkey : g a = p a * ((q a / p a) * Real.log (q a / p a)
          - (q a / p a) + 1) := by
        simp only [hg]
        linear_combination (Real.log (q a / p a) - 1) * hqt
      rw [hkey] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt (hp a))
      · have ht1 : q a / p a = 1 := by
          by_contra hc
          exact absurd h (strict_log_term _ ht0 hc).ne'
        have e : q a = (q a / p a) * p a := by
          rw [div_mul_cancel₀ (q a) (hp a).ne']
        rw [ht1, one_mul] at e
        exact e
  have hsumg : ∑ a, g a = klDef q p := by
    have hexp : klDef q p = ∑ a, (g a + (q a - p a)) := by
      simp only [klDef]
      exact Finset.sum_congr rfl fun a _ => by simp only [hg]; ring
    rw [hexp]
    have hd : (∑ a : α, (g a + (q a - p a)))
        = (∑ a : α, g a) + (∑ a : α, (q a - p a)) := Finset.sum_add_distrib
    have h1 : ∑ a, (q a - p a) = 0 := by
      have e : ∑ a, (q a - p a) = (∑ a : α, q a) - (∑ a : α, p a) :=
        Finset.sum_sub_distrib q p
      rw [e, hqsum, hpsum]
      norm_num
    linarith
  by_contra hcon
  have hz : klDef q p = 0 :=
    le_antisymm (le_of_not_gt hcon) (kl_nonneg_of_nonneg q p hq hp hqsum hpsum)
  rw [← hsumg] at hz
  have hall : ∀ a, g a = 0 := by
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hgpos a)).mp hz a
      (Finset.mem_univ a)
    exact this
  exact hne (funext fun a => hgeq a (hall a))

/-! ### The bridge identity -/

omit [DecidableEq α] in
/-- (B1 MAIN) Updating exactly one coordinate `i` of the global
product-belief `p` changes the FULL mean-field free energy by EXACTLY
the single-cell free-energy difference at the local mean-field field
`meanFieldField B K p i` (with the background FROZEN — the field is
computed at the pre-update `p`). Pure linearity: no probability
premises, exact for every `q`, `p`, `B`, `K`, `β`. All terms of the
energy not involving cell `i` — entropy cells `j ≠ i`, unary fields
`j ≠ i`, and the both-indices-off-`i` interaction pairs — are invariant
under the update; the cross terms are linear in `p i`, which is where
the ordered-pair `1/2`-outside convention of C260 is load-bearing
(numeric anchor: asymmetric `K` on `Fin 2 × Bool`, probe C265). -/
theorem meanField_coordinate_update_eq_singleCell (β : ℝ) (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (p : ι → (α → ℝ)) (i : ι) (q : α → ℝ) :
    meanFieldFreeEnergy β B K (Function.update p i q)
        - meanFieldFreeEnergy β B K p
      = singleCellFreeEnergy β (meanFieldField B K p i) 0 q
        - singleCellFreeEnergy β (meanFieldField B K p i) 0 (p i) := by
  classical
  set r := Function.update p i q with hrdef
  have hr : ∀ k ≠ i, r k = p k := fun k hk => by
    rw [hrdef, Function.update_apply]
    simp [hk]
  have hri : r i = q := by rw [hrdef, Function.update_self]
  -- entropy difference
  have hE : (∑ k, ∑ a, r k a * Real.log (r k a))
        - (∑ k, ∑ a, p k a * Real.log (p k a))
      = (∑ a, q a * Real.log (q a)) - (∑ a, p i a * Real.log (p i a)) := by
    rw [sum_split (fun k u => ∑ a, u a * Real.log (u a)) p i r hr, hri,
      sum_split (fun k u => ∑ a, u a * Real.log (u a)) p i p (fun k _ => rfl)]
    ring
  -- unary field difference
  have hB : (∑ k, ∑ a, B k a * r k a) - (∑ k, ∑ a, B k a * p k a)
      = (∑ a, B i a * q a) - (∑ a, B i a * p i a) := by
    rw [sum_split (fun k u => ∑ a, B k a * u a) p i r hr, hri,
      sum_split (fun k u => ∑ a, B k a * u a) p i p (fun k _ => rfl)]
    ring
  -- interaction difference: row form
  have hSrow : (∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (q a * p j b))
        - (∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (p i a * p j b))
      = ∑ a, (q a - p i a)
          * (∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b) := by
    have hj : ∀ j ∈ Finset.univ \ {i}, (∑ a, ∑ b, K i j a b * (q a * p j b))
        = (∑ a, ∑ b, K i j a b * (p i a * p j b))
          + (∑ a, ∑ b, (q a - p i a) * (K i j a b * p j b)) := by
      intro j _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib,
      pull1 _ (fun a => q a - p i a) (fun j a b => K i j a b * p j b)]
    ring
  -- interaction difference: column form
  have hScol : (∑ k ∈ Finset.univ \ {i}, ∑ a, ∑ b, K k i a b * (p k a * q b))
        - (∑ k ∈ Finset.univ \ {i}, ∑ a, ∑ b, K k i a b * (p k a * p i b))
      = ∑ a, (q a - p i a)
          * (∑ j ∈ Finset.univ \ {i}, ∑ b, K j i b a * p j b) := by
    have hk : ∀ k ∈ Finset.univ \ {i}, (∑ a, ∑ b, K k i a b * (p k a * q b))
        = (∑ a, ∑ b, K k i a b * (p k a * p i b))
          + (∑ a, ∑ b, (q b - p i b) * (K k i a b * p k a)) := by
      intro k _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib,
      pull2 _ (fun b => q b - p i b) (fun k a b => K k i a b * p k a)]
    ring
  -- interaction difference: invariant rest cancels (interact_split ×2)
  have hS : (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (r k a * r j b))
        - (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (p k a * p j b))
      = ((∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (q a * p j b))
          - (∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (p i a * p j b)))
        + ((∑ k ∈ Finset.univ \ {i}, ∑ a, ∑ b, K k i a b * (p k a * q b))
          - (∑ k ∈ Finset.univ \ {i}, ∑ a, ∑ b, K k i a b * (p k a * p i b))) := by
    rw [interact_split K p i r hr, hri, interact_split K p i p (fun k _ => rfl)]
    ring
  rw [hSrow, hScol] at hS
  -- the cross-term bookkeeping: unary + (1/2)·(row + column) = hz
  have hcross : ((∑ a, B i a * q a) - (∑ a, B i a * p i a))
        + (1 / 2) * ((∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b))
            + (∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K j i b a * p j b)))
      = ∑ a, meanFieldField B K p i a * (q a - p i a) := by
    have hBd : (∑ a, B i a * q a) - (∑ a, B i a * p i a)
        = ∑ a, B i a * (q a - p i a) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hsum : (∑ a, (q a - p i a)
            * (∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b))
          + (∑ a, (q a - p i a)
            * (∑ j ∈ Finset.univ \ {i}, ∑ b, K j i b a * p j b))
        = ∑ a, (∑ j ∈ Finset.univ \ {i},
              ∑ b, (K i j a b * p j b + K j i b a * p j b)) * (q a - p i a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_add, ← Finset.sum_add_distrib, mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [← Finset.sum_add_distrib]
    rw [hBd, hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [meanFieldField]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- final assembly
  simp only [meanFieldFreeEnergy, singleCellFreeEnergy]
  have hE0 : (∑ k, ∑ a, r k a * Real.log (r k a))
      = (∑ k, ∑ a, p k a * Real.log (p k a))
        + ((∑ a, q a * Real.log (q a))
          - (∑ a, p i a * Real.log (p i a))) := by
    linarith [hE]
  have hE' : (1 / β) * (∑ k, ∑ a, r k a * Real.log (r k a))
      = (1 / β) * ((∑ k, ∑ a, p k a * Real.log (p k a))
        + ((∑ a, q a * Real.log (q a))
          - (∑ a, p i a * Real.log (p i a)))) := by
    rw [hE0]
  have hB' : (∑ k, ∑ a, B k a * r k a) = (∑ k, ∑ a, B k a * p k a)
      + ((∑ a, B i a * q a) - (∑ a, B i a * p i a)) := by linarith [hB]
  have hS0 : (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b,
          K k j a b * (r k a * r j b))
      = (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b, K k j a b * (p k a * p j b))
        + ((∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b))
            + (∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K j i b a * p j b))) := by
    linarith [hS]
  have hS' : (1 / 2) * (∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b,
          K k j a b * (r k a * r j b))
      = (1 / 2) * ((∑ k, ∑ j ∈ Finset.univ \ {k}, ∑ a, ∑ b,
            K k j a b * (p k a * p j b))
        + ((∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b))
            + (∑ a, (q a - p i a)
              * (∑ j ∈ Finset.univ \ {i}, ∑ b, K j i b a * p j b)))) := by
    rw [hS0]
  have hSCd : (∑ a, meanFieldField B K p i a * q a)
        - (∑ a, meanFieldField B K p i a * p i a)
      = ∑ a, meanFieldField B K p i a * (q a - p i a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hE', hB', hS']
  linear_combination hcross - hSCd

omit [DecidableEq α] in
/-- (B1 corollary 1) Soft coordinate Gibbs updates never increase the
FULL mean-field free energy: with `β > 0` and a probability vector
`p i`, updating coordinate `i` to the local Gibbs minimizer
`q_i = softDef (−β·hz)` changes `F` by the single-cell delta, which
C261 proved equals `(1/β)·KL ≥ 0` (reused verbatim via
`coordinate_kl_nonneg`; positivity is NOT reproved here). -/
theorem meanField_coordinate_gibbs_nonincreasing [Nonempty α] (β : ℝ)
    (hβ : 0 < β) (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (p : ι → (α → ℝ)) (i : ι) (hp : ∀ a, 0 ≤ p i a) (hsum : ∑ a, p i a = 1) :
    meanFieldFreeEnergy β B K
        (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
      ≤ meanFieldFreeEnergy β B K p := by
  have hid := meanField_coordinate_update_eq_singleCell β B K p i
    (softDef (fun a => -β * meanFieldField B K p i a))
  have h := coordinate_kl_nonneg β hβ (meanFieldField B K p i) 0
    (p i) hp hsum
  calc meanFieldFreeEnergy β B K
        (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
      = (meanFieldFreeEnergy β B K
            (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
          - meanFieldFreeEnergy β B K p)
        + meanFieldFreeEnergy β B K p := by ring
    _ = (singleCellFreeEnergy β (meanFieldField B K p i) 0
            (softDef (fun a => -β * meanFieldField B K p i a))
          - singleCellFreeEnergy β (meanFieldField B K p i) 0 (p i))
        + meanFieldFreeEnergy β B K p := by rw [hid]
    _ = meanFieldFreeEnergy β B K p
        - (singleCellFreeEnergy β (meanFieldField B K p i) 0 (p i)
          - singleCellFreeEnergy β (meanFieldField B K p i) 0
              (softDef (fun a => -β * meanFieldField B K p i a))) := by ring
    _ ≤ meanFieldFreeEnergy β B K p := sub_le_self _ h

omit [DecidableEq α] in
/-- (B1 corollary 2) STRICT drop: if the updated coordinate is not
already at its Gibbs minimizer (`p i ≠ q_i`), the FULL mean-field free
energy strictly decreases — by the bridge identity and C261's
`coordinate_kl_identity`, the drop is exactly `(1/β)·KL(p i ‖ q_i)`,
strictly positive by `kl_pos_of_ne`. -/
theorem meanField_coordinate_strict_drop_of_ne [Nonempty α] (β : ℝ)
    (hβ : 0 < β) (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (p : ι → (α → ℝ)) (i : ι) (hp : ∀ a, 0 ≤ p i a) (hsum : ∑ a, p i a = 1)
    (hne : p i ≠ softDef (fun a => -β * meanFieldField B K p i a)) :
    meanFieldFreeEnergy β B K
        (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
      < meanFieldFreeEnergy β B K p := by
  have hid := meanField_coordinate_update_eq_singleCell β B K p i
    (softDef (fun a => -β * meanFieldField B K p i a))
  have hkl := coordinate_kl_identity β (ne_of_gt hβ) (meanFieldField B K p i) 0
    (p i) hp hsum
  have hpos : 0 < (1 / β) * klDef (p i)
      (softDef (fun a => -β * meanFieldField B K p i a)) :=
    mul_pos (by positivity) (kl_pos_of_ne (p i)
      (softDef (fun a => -β * meanFieldField B K p i a)) hp hsum
      (fun a => softDef_pos (fun a => -β * meanFieldField B K p i a) a)
      (softDef_sum_one (fun a => -β * meanFieldField B K p i a)) hne)
  calc meanFieldFreeEnergy β B K
        (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
      = (meanFieldFreeEnergy β B K
            (Function.update p i (softDef (fun a => -β * meanFieldField B K p i a)))
          - meanFieldFreeEnergy β B K p)
        + meanFieldFreeEnergy β B K p := by ring
    _ = (singleCellFreeEnergy β (meanFieldField B K p i) 0
            (softDef (fun a => -β * meanFieldField B K p i a))
          - singleCellFreeEnergy β (meanFieldField B K p i) 0 (p i))
        + meanFieldFreeEnergy β B K p := by rw [hid]
    _ = meanFieldFreeEnergy β B K p
        - (singleCellFreeEnergy β (meanFieldField B K p i) 0 (p i)
          - singleCellFreeEnergy β (meanFieldField B K p i) 0
              (softDef (fun a => -β * meanFieldField B K p i a))) := by ring
    _ = meanFieldFreeEnergy β B K p
          - (1 / β) * klDef (p i)
              (softDef (fun a => -β * meanFieldField B K p i a)) := by rw [hkl]
    _ < meanFieldFreeEnergy β B K p := sub_lt_self _ hpos

end FullBridge

end Hagi.Energy
