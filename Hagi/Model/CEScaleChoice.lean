/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEJointScale

set_option linter.style.header false

/-!
# The common certified finite scale-choice interface

Both scale-selection settings of the CE chain select an element of a
finite codebook by minimizing a declared nonnegative penalty, using
Mathlib's `Finset.exists_min_image`.  This module records that shared
shape once: a `ScaleChoice` bundles the selected code with its
codebook membership and its domination certificate, and one generalized
separable theorem (`scaleChoiceSum_le`) proves the sum-form union bound
for an arbitrary index type and codebook.

The bridges `grouped_scale_choice` and `joint_scale_choice` instantiate
the record for the independent per-group selector of
`CEGroupedScale.selectedGroupScales` and for the coupled selector of
`CEJointScale.selectedCoupledScales`, whose codebook is the complete
assignment space.  Statements and proofs of the existing selectors are
frozen and untouched; the corollaries below are derived through the
general theorems.

What deliberately stays out of the interface: the coupled-specific
facts (comparison with the separable total, zero-penalty collapse, the
possible cancellation inside the joint observed penalty) remain in
their own modules, and no claim is made about true cross-entropy,
out-of-sample quality, or physical storage.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEScaleChoice

open Hagi.Model

/-- A certified choice from a finite codebook: the selected element,
its membership in the codebook, and the proof that its penalty is at
most the penalty of every codebook element. -/
structure ScaleChoice {κ : Type} (penalty : κ → ℝ) (s : Finset κ) where
  /-- The selected codebook element. -/
  chosen : κ
  /-- The selection belongs to the declared finite codebook. -/
  chosen_mem : chosen ∈ s
  /-- The selection's penalty is minimal on the codebook. -/
  min_le : ∀ k ∈ s, penalty chosen ≤ penalty k

/-- The selected penalty is at most the penalty of any codebook
element; this is the interface's pointwise domination lemma. -/
theorem le_of_mem {κ : Type} (penalty : κ → ℝ) {s : Finset κ}
    (c : ScaleChoice penalty s) (k : κ) (hk : k ∈ s) :
    penalty c.chosen ≤ penalty k :=
  c.min_le k hk

/-- Generalized separable union bound: if every index independently
carries a certified codebook choice, then the sum of the selected
penalties is at most the sum of the penalties of any codebook-valued
alternative assignment.  The proof exists once here; concrete
per-block selectors instantiate it instead of repeating it. -/
theorem scaleChoiceSum_le {ι κ : Type} [Fintype ι] (s : Finset κ)
    (penalty : ι → κ → ℝ)
    (c : ∀ g : ι, ScaleChoice (penalty g) s)
    (alternative : ι → κ) (halt : ∀ g, alternative g ∈ s) :
    ∑ g, penalty g (c g).chosen ≤ ∑ g, penalty g (alternative g) := by
  apply Finset.sum_le_sum
  intro g _hg
  exact (c g).min_le (alternative g) (halt g)

/-- Bridge to the independent per-group selector: at every group the
frozen `CEGroupedScale.selectedGroupScales` is a certified choice from
the complete finite code family. -/
noncomputable def grouped_scale_choice {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    ScaleChoice (CEGroupedScale.blockPenalty e X w g)
      (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode) where
  chosen := CEGroupedScale.selectedGroupScales e X w g
  chosen_mem := (CEGroupedScale.selectedGroupScales_spec e X w g).1
  min_le := fun k _hk => CEGroupedScale.selectedGroupScales_score_le e X w g k

/-- Bridge to the coupled selector: the frozen
`CEJointScale.selectedCoupledScales` is a certified choice whose
codebook is the complete finite assignment space. -/
noncomputable def joint_scale_choice {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    ScaleChoice (CEJointScale.coupledPenalty e X w)
      (Finset.univ : Finset (Fin G → Hagi.Runtime.DyadicScaleCode)) where
  chosen := CEJointScale.selectedCoupledScales e X w
  chosen_mem := (CEJointScale.selectedCoupledScales_spec e X w).1
  min_le := fun scales _hs =>
    CEJointScale.selectedCoupledScales_score_le e X w scales

/-- The separable total of the frozen per-group selections is at most
the separable total of any alternative assignment; derived through the
generalized union bound, not by repeating its proof. -/
theorem grouped_scale_choice_sum_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (alternative : Fin G → Hagi.Runtime.DyadicScaleCode) :
    ∑ g, CEGroupedScale.blockPenalty e X w g
        (CEGroupedScale.selectedGroupScales e X w g) ≤
      ∑ g, CEGroupedScale.blockPenalty e X w g (alternative g) :=
  scaleChoiceSum_le (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode)
    (CEGroupedScale.blockPenalty e X w) (grouped_scale_choice e X w)
    alternative (fun _g => Finset.mem_univ _)

/-- The coupled score of the frozen coupled selection is at most the
coupled score of any complete alternative; derived through the
interface's domination lemma over the full assignment space. -/
theorem joint_scale_choice_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (alternative : Fin G → Hagi.Runtime.DyadicScaleCode) :
    CEJointScale.coupledPenalty e X w
        (CEJointScale.selectedCoupledScales e X w) ≤
      CEJointScale.coupledPenalty e X w alternative :=
  (joint_scale_choice e X w).min_le alternative
    (Finset.mem_univ alternative)

end Hagi.Model.CEScaleChoice
