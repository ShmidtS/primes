/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

set_option linter.style.header false

/-!
# Low-rank leaf mixing: when a mixer after the concat is invisible

Setup: leaf `a` reads the mixed view `∑_b Q a b • h_b` through head
`W a`, and the merged logit is the mean over leaves (`mixedLogits`)
of these per-leaf logits.

`mixed_invisible` — if the column sums of `Q` reproduce every head
(`∀ b, ∑_a Q a b • W a = W b`), the mixed logits equal the plain
ensemble mean logits (`plainLogits`): the mixer is invisible to the
head. This is a sufficient condition; the converse is not proved.
-/

open scoped Matrix

namespace Hagi

variable {k n : Type*} [Fintype k] [Fintype n]

/-- The merged logits of the mixed ladder: each leaf a reads the
Q-mixed hidden states through its head W a, and the heads
average. -/
noncomputable def mixedLogits (Q : n → n → ℝ)
    (W : n → (k → ℝ)) (h : n → (k → ℝ)) : ℝ :=
  (∑ a, (W a) ⬝ᵥ (∑ b, Q a b • h b)) / (Fintype.card n)

/-- The un-mixed ensemble mean logit (heads read the identity
views). -/
noncomputable def plainLogits (W : n → (k → ℝ)) (h : n → (k → ℝ)) : ℝ :=
  (∑ a, (W a) ⬝ᵥ h a) / (Fintype.card n)

/-- If the mixer's column sums reproduce every head (`hinv`), then
the mixed logits equal the plain ensemble mean logits: the mixer is
invisible to the head. By bilinearity, the double sum re-associates
to `∑_b (∑_a Q a b • W a) ⬝ᵥ h b`, and each inner head-sum is `W b`
by `hinv`. -/
theorem mixed_invisible {Q : n → n → ℝ} {W : n → (k → ℝ)}
    {h : n → (k → ℝ)}
    (hinv : ∀ b : n, ∑ a, Q a b • W a = W b) :
    mixedLogits Q W h = plainLogits W h := by
  unfold mixedLogits plainLogits
  have key : ∀ a : n,
      (W a) ⬝ᵥ (∑ b, Q a b • h b)
        = ∑ b, Q a b * ((W a) ⬝ᵥ h b) := by
    intro a
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun b _ => dotProduct_smul _ _ _
  have hstep : (∑ a, (W a) ⬝ᵥ (∑ b, Q a b • h b))
      = ∑ b, (∑ a, Q a b • W a) ⬝ᵥ h b := by
    simp only [key]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    -- ∑_a Q a b * (W a ⬝ᵥ h b) = (∑_a Q a b • W a) ⬝ᵥ h b
    have h2 : (∑ a, Q a b • W a) ⬝ᵥ h b
        = ∑ a, Q a b * ((W a) ⬝ᵥ h b) := by
      simp only [Finset.sum_apply, dotProduct, Finset.sum_mul,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h2]
  rw [hstep]
  simp only [hinv]

end Hagi
