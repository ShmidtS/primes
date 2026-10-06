/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.DField
import Hagi.Data.FannesSmooth

/-!
# CrossModalGap — the cross-modal information gain

The omni-extension of the HAGI disagreement theory: a modality
pair (X, Y) carries genuinely joint information exactly when the
joint distribution is NOT the product of its marginals. The gap

  G(X;Y) := H(X) + H(Y) − H(X,Y) = KL(p_xy ‖ px ⊗ py)

is the mutual information: the part of the joint state that no
single modality can supply. This is the formal counterpart of
the omni-HAGI principle "a new modality is admissible as a
growth source only if it brings positive cross-modal gain".

Main results:
* `crossModalGap_eq_kl`: the loss/entropy form of the gap IS
  the KL-divergence between the joint and the product of
  marginals;
* `crossModalGap_nonneg`: G ≥ 0 — merging modalities into one
  state never destroys predictive information (subadditivity);
* `crossModalGap_zero_iff_indep`: G = 0 exactly when the two
  modalities are independent — a redundant modality brings no
  cross-modal gain.
-/

namespace Hagi.Omni

open Finset

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
variable {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The marginal of a joint distribution on the first
component. -/
def margX (p : X × Y → ℝ) : X → ℝ := fun x => ∑ y, p (x, y)

/-- The marginal on the second component. -/
def margY (p : X × Y → ℝ) : Y → ℝ := fun y => ∑ x, p (x, y)

/-- The cross-modal gap in entropy form: H(X) + H(Y) − H(X,Y). -/
noncomputable def crossModalGap (p : X × Y → ℝ) : ℝ :=
  Hagi.Data.ent (margX p) + Hagi.Data.ent (margY p) - Hagi.Data.ent p

/-! ### The entropy form IS the KL form -/

/-- The joint-to-product identity: the gap in entropy form
equals the KL divergence of the joint against the product of
marginals — the mutual information. -/
theorem crossModalGap_eq_kl (p : X × Y → ℝ)
    (hp : ∀ z : X × Y, 0 < p z)
    (hsum : ∑ z : X × Y, p z = 1) :
    crossModalGap p
      = Hagi.KLdiv p (fun z => margX p z.1 * margY p z.2) := by
  -- marginals are strictly positive and normalized
  have hmx : ∀ x, 0 < margX p x := by
    intro x
    unfold margX
    exact Finset.sum_pos (fun y _ => hp (x, y))
      Finset.univ_nonempty
  have hmy : ∀ y, 0 < margY p y := by
    intro y
    unfold margY
    exact Finset.sum_pos (fun x _ => hp (x, y))
      Finset.univ_nonempty
  -- the cross re-associations
  have hA : (∑ z : X × Y, p z * Real.log (margX p z.1))
      = ∑ x, margX p x * Real.log (margX p x) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    have hpair : ∀ y : Y, (x, y).1 = x := fun _ => rfl
    rw [Finset.sum_congr rfl (fun y _ => by rw [hpair y]), ← Finset.sum_mul, margX]
  have hB : (∑ z : X × Y, p z * Real.log (margY p z.2))
      = ∑ y, margY p y * Real.log (margY p y) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hpair : ∀ x : X, (x, y).2 = y := fun _ => rfl
    rw [Finset.sum_congr rfl (fun x _ => by rw [hpair x]), ← Finset.sum_mul, margY]
  -- unfold both sides and match
  unfold crossModalGap Hagi.Data.ent Hagi.KLdiv
  -- split the log of the ratio
  have hsplit : ∀ z : X × Y,
      Real.log (p z / (margX p z.1 * margY p z.2))
        = Real.log (p z) - Real.log (margX p z.1)
            - Real.log (margY p z.2) := by
    intro z
    rw [Real.log_div (ne_of_gt (hp z))
        (ne_of_gt (mul_pos (hmx z.1) (hmy z.2))),
      Real.log_mul (ne_of_gt (hmx z.1)) (ne_of_gt (hmy z.2))]
    ring
  have hKL : (∑ z : X × Y, p z * Real.log (p z
        / (margX p z.1 * margY p z.2)))
      = (∑ z, p z * Real.log (p z))
        - (∑ z, p z * Real.log (margX p z.1))
        - (∑ z, p z * Real.log (margY p z.2)) := by
    have hterm : ∀ z : X × Y,
        p z * Real.log (p z / (margX p z.1 * margY p z.2))
          = p z * Real.log (p z) - p z * Real.log (margX p z.1)
              - p z * Real.log (margY p z.2) := by
      intro z
      rw [hsplit z]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hKL, hA, hB]
  ring

/-- Marginals of a positive joint distribution sum to one. -/
theorem margX_sum_one (p : X × Y → ℝ)
    (hsum : ∑ z, p z = 1) : ∑ x, margX p x = 1 := by
  unfold margX
  rw [← Fintype.sum_prod_type]
  exact hsum

theorem margY_sum_one (p : X × Y → ℝ)
    (hsum : ∑ z, p z = 1) : ∑ y, margY p y = 1 := by
  unfold margY
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact hsum

/-- Marginals of a strictly positive joint are strictly
positive (needs both modalities nonempty). -/
theorem margX_pos (p : X × Y → ℝ) (hp : ∀ z, 0 < p z) :
    ∀ x, 0 < margX p x := by
  intro x
  unfold margX
  exact Finset.sum_pos (fun y _ => hp (x, y)) Finset.univ_nonempty

theorem margY_pos (p : X × Y → ℝ) (hp : ∀ z, 0 < p z) :
    ∀ y, 0 < margY p y := by
  intro y
  unfold margY
  exact Finset.sum_pos (fun x _ => hp (x, y)) Finset.univ_nonempty

/-- The product of marginals sums to one and is strictly
positive. -/
theorem prodMarg_sum_one (p : X × Y → ℝ) (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1) :
    ∑ z : X × Y, margX p z.1 * margY p z.2 = 1 := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : X,
      (∑ y : Y, margX p x * margY p y)
        = margX p x * ∑ y : Y, margY p y := by
    intro x
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_mul]
  rw [margX_sum_one p hsum, one_mul]
  exact margY_sum_one p hsum

/-- **The cross-modal gain is nonnegative**: merging two
modalities into one shared state never destroys predictive
information — the entropy form of subadditivity. -/
theorem crossModalGap_nonneg (p : X × Y → ℝ)
    (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1) :
    0 ≤ crossModalGap p := by
  rw [crossModalGap_eq_kl p hp hsum]
  exact Hagi.kl_nonneg p (fun z => margX p z.1 * margY p z.2)
    hp (fun z => mul_pos (margX_pos p hp z.1) (margY_pos p hp z.2))
    hsum (prodMarg_sum_one p hp hsum)

/-- **Zero gap ⟺ modal independence**: the cross-modal gain
vanishes exactly when the joint distribution is the product of
its marginals — an independent (redundant) modality brings no
new cross-modal information. -/
theorem crossModalGap_zero_iff_indep (p : X × Y → ℝ)
    (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1) :
    crossModalGap p = 0
      ↔ ∀ x y, p (x, y) = margX p x * margY p y := by
  constructor
  · intro h0
    have hkl : Hagi.KLdiv p (fun z => margX p z.1 * margY p z.2) = 0 := by
      rw [← crossModalGap_eq_kl p hp hsum, h0]
    have hall := Hagi.kl_zero_iff_eq p (fun z => margX p z.1 * margY p z.2)
      hp (fun z => mul_pos (margX_pos p hp z.1) (margY_pos p hp z.2))
      hsum (prodMarg_sum_one p hp hsum) hkl
    intro x y
    exact hall (x, y)
  · intro h
    have hkl : Hagi.KLdiv p (fun z => margX p z.1 * margY p z.2) = 0 := by
      unfold Hagi.KLdiv
      apply Finset.sum_eq_zero
      intro z _
      rw [h z.1 z.2]
      have hdiv : (margX p z.1 * margY p z.2)
          / (margX p z.1 * margY p z.2) = 1 :=
        div_self (ne_of_gt (mul_pos (margX_pos p hp z.1) (margY_pos p hp z.2)))
      rw [hdiv, Real.log_one, mul_zero]
    rw [crossModalGap_eq_kl p hp hsum, hkl]

end Hagi.Omni
