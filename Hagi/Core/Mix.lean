/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

set_option linter.style.header false

/-!
# Low-rank leaf mixing: when a mixer after the concat is invisible

The `composition gap` measured on the ladder is at the threshold of
zero (-0.024 nats, AGENT_WORKLOG). The engineering question is
whether a *low-rank rotation* Q applied to the concat hidden state
(the "mixer" idea, now in the logit regime rather than the state
regime of `Hagi.Core/Lift`) can only help — or when it silently destroys
the ensemble.

**Setup.** N leaves read a shared hidden state `h` (the concat of
per-leaf columns); leaf `a` applies head `W_a` producing logits
`z_a = W_a ⬝ᵥ h_a` where `h_a = ∑_b Q a b • h_b` is the leaf's view
through the mixer Q. The merged logit is the mean of the `z_a`.

**The invisibility condition.** The mixing is *logit-invisible* —
the merged logits are exactly the un-mixed ensemble mean — whenever
(SUFFICIENCY; the converse is NOT proved) the
column sums of Q reproduce each head:

`∀ b, ∑_a Q a b • W_a = W_b`.

This is precisely the parent-preserving condition of
`Hagi.parentPreservingQ` (the transpose analogue: rows there, sums
here), specialized to the logit regime. When it holds, the
ensemble theorem (`ensemble_ce_le_mean_general`) applies verbatim:
the merged CE is at most the mean child CE, and any measured gain
of the mixed ladder over the mean is compositional, not an artifact.

**When it fails**, the mixer *moves mass between leaves* — this is
exactly the divergent-leaf regime of `Hagi.Core/Select`: mixing a strong
standalone leaf into a weak one can strictly degrade the ensemble,
and the standalone quality ranking does not protect against it.

**Prescription for the code.** A mixer stage added after concat is
safe iff its column sums reproduce the heads (unit column sums with
a shared head W: `W_a = W` for all a forces `∑_a Q a b = 1`). For
orthogonal mixers this is the "orthogonal to the inter-leaf
contrast" condition: the mixer must act on the subspace where the
heads agree, never across the leaf-comparison direction. Otherwise
the mixer must be trained, not trusted.
-/

open scoped Matrix

namespace Hagi

variable {k n : Type*} [Fintype k] [Fintype n]

/-- The merged logits of the mixed ladder: leaf `a` reads
`∑_b Q a b • h_b` through head `W_a`, and the head averages. -/
noncomputable def mixedLogits (Q : n → n → ℝ)
    (W : n → (k → ℝ)) (h : n → (k → ℝ)) : ℝ :=
  (∑ a, (W a) ⬝ᵥ (∑ b, Q a b • h b)) / (Fintype.card n)

/-- The un-mixed ensemble mean logit (heads read the identity
views). -/
noncomputable def plainLogits (W : n → (k → ℝ)) (h : n → (k → ℝ)) : ℝ :=
  (∑ a, (W a) ⬝ᵥ h a) / (Fintype.card n)

/-- **The invisibility theorem.** If the mixer's column sums
reproduce every head (`∀ b, ∑_a Q a b • W_a = W_b`), then the mixed
logits equal the plain ensemble mean logits — the mixer is
invisible to the head, and the ensemble bound applies unchanged.

The algebra: by bilinearity of the dot product, the double sum
`∑_a W_a ⬝ᵥ (∑_b Q a b • h_b)` re-associates to
`∑_b (∑_a Q a b • W_a) ⬝ᵥ h_b`, and each inner head-sum is `W_b`
by the invisibility condition. -/
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
