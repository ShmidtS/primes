/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEPackedStep

/-!
# Exact finite selection among the 255 certified dyadic scales

The selector minimizes the proved CE increase bound, not the true CE.
Its 255 candidate score evaluations are not a FLOP count, and its 16-bit
logical payload is not a physical memory measurement.  The implementation
follows Mathlib's `Finset.exists_min_image` and the local `Classical.choose`
pattern from `Hagi/Unified/ParetoExecution.lean`, without importing the
Unified layer.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEScaleSelection

/-- Certified CE-increase penalty at the common level encoded by `k`. -/
noncomputable def scalePenalty {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (k : Hagi.Runtime.DyadicScaleCode) : ℝ :=
  CEQuantized.ceQuantPenalty X w (Hagi.Runtime.dyadicLevel k)

/-- Both actual observed and saturation-aware structural penalties are
nonnegative, including for arbitrary feature data and saturated inputs. -/
theorem scalePenalty_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (k : Hagi.Runtime.DyadicScaleCode) : 0 ≤ scalePenalty X w k := by
  apply le_min
  · unfold CEQuantized.ceQuantObservedPenalty
    positivity
  · unfold CEQuantized.ceQuantStructuralPenalty
    positivity

/-- Number of candidate scores compared by finite scale selection. -/
def scaleEvaluationCount : ℕ := Fintype.card Hagi.Runtime.DyadicScaleCode

/-- The complete finite candidate class has 255 entries; this theorem does
not count arithmetic instructions inside each score evaluation. -/
theorem scaleEvaluationCount_eq : scaleEvaluationCount = 255 := by
  norm_num [scaleEvaluationCount, Hagi.Runtime.DyadicScaleCode]

/-- Exact minimizer of the certified bound over all 255 codes. -/
noncomputable def selectedScale {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    Hagi.Runtime.DyadicScaleCode :=
  Classical.choose
    (Finset.exists_min_image (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode)
      (scalePenalty X w)
      ⟨Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- The chosen code belongs to the complete finite set and attains its
minimum penalty. -/
theorem selectedScale_spec {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    selectedScale X w ∈ (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode) ∧
      ∀ k ∈ (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode),
        scalePenalty X w (selectedScale X w) ≤ scalePenalty X w k := by
  exact Classical.choose_spec
    (Finset.exists_min_image (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode)
      (scalePenalty X w)
      ⟨Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- The selected bound is at most every candidate's bound. -/
theorem selectedScale_score_le {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d))
    (k : Hagi.Runtime.DyadicScaleCode) :
    scalePenalty X w (selectedScale X w) ≤ scalePenalty X w k :=
  (selectedScale_spec X w).2 k (Finset.mem_univ k)

/-- Every selected common level is positive. -/
theorem selectedScale_level_pos {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    0 < Hagi.Runtime.dyadicLevel (selectedScale X w) :=
  Hagi.Runtime.dyadicLevel_pos _

/-- The selected actual quantized successor satisfies the minimized
certified CE-increase bound; this is not a minimum-CE assertion. -/
theorem selectedScale_ce_le {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (t : V) (w : EuclideanSpace ℝ (Fin d)) :
    Hagi.ceOneHot t (ceLogits X (CEQuantized.ternaryCEParameters
      (Hagi.Runtime.dyadicLevel (selectedScale X w)) w)) ≤
      Hagi.ceOneHot t (ceLogits X w) + scalePenalty X w (selectedScale X w) := by
  exact CEQuantized.ceOneHot_ternary_le_ceQuantPenalty X t
    (Hagi.Runtime.dyadicLevel (selectedScale X w)) w (selectedScale_level_pos X w)

/-- Any eligible candidate makes the selected certified bound eligible. -/
theorem selectedScale_strict_margin_of_exists {V : Type} [Fintype V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (h : ∃ k, scalePenalty X
        (ceNextParameters X θ t (safeStepSize X θ t)) k <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    scalePenalty X (ceNextParameters X θ t (safeStepSize X θ t))
        (selectedScale X (ceNextParameters X θ t (safeStepSize X θ t))) <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact lt_of_le_of_lt
    (selectedScale_score_le X (ceNextParameters X θ t (safeStepSize X θ t)) k) hk

/-- Conditional actual strict CE descent for the general safe successor.
Without the displayed candidate existence premise no descent is claimed. -/
theorem selectedScale_strict_descent_of_exists {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ} (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hr : 0 < ceStepRange X θ t)
    (h : ∃ k, scalePenalty X
        (ceNextParameters X θ t (safeStepSize X θ t)) k <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X (CEQuantized.ternaryCEParameters
      (Hagi.Runtime.dyadicLevel
        (selectedScale X (ceNextParameters X θ t (safeStepSize X θ t))))
      (ceNextParameters X θ t (safeStepSize X θ t)))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  apply CEQuantized.ceOneHot_ternary_safeStep_lt X θ t
    (Hagi.Runtime.dyadicLevel
      (selectedScale X (ceNextParameters X θ t (safeStepSize X θ t))))
  · exact selectedScale_level_pos X (ceNextParameters X θ t (safeStepSize X θ t))
  · exact hr
  · exact selectedScale_strict_margin_of_exists X θ t h

/-- The known code 31 has zero certified penalty for the actual witness
successor, by the previously proved observed-penalty calculation. -/
theorem ceQuantWitness_knownSampleScale_score :
    scalePenalty CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      Hagi.Runtime.knownSampleScale = 0 := by
  rw [scalePenalty, Hagi.Runtime.knownSampleScale_level]
  exact CEQuantized.ceQuantWitness_ceQuantPenalty

/-- The chosen witness score is exactly zero: minimal above the zero score
of code 31 and nonnegative below.  The selected code itself is not fixed. -/
theorem ceQuantWitness_selectedScale_score :
    scalePenalty CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor) = 0 := by
  apply le_antisymm
  · exact (selectedScale_score_le CEQuantized.ceQuantWitnessFeatures
      CEPackedStep.rawSuccessor Hagi.Runtime.knownSampleScale).trans_eq
        ceQuantWitness_knownSampleScale_score
  · exact scalePenalty_nonneg _ _ _

/-- The derived selected-scale margin for the known witness. -/
theorem ceQuantWitness_selectedScale_strict_margin :
    scalePenalty CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
        (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor) <
      2 * (ceAlignment CEQuantized.ceQuantWitnessFeatures 0 0) ^ 2 /
        (ceStepRange CEQuantized.ceQuantWitnessFeatures 0 0) ^ 2 := by
  rw [ceQuantWitness_selectedScale_score, CEQuantized.ceQuantWitness_alignment,
    CEQuantized.ceQuantWitness_range]
  norm_num

/-- Actual strict CE descent at whichever scale the finite selector chose. -/
theorem ceQuantWitness_selectedScale_strict_descent :
    Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
      (CEQuantized.ternaryCEParameters
        (Hagi.Runtime.dyadicLevel
          (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))
        CEPackedStep.rawSuccessor)) <
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  change Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
    (CEQuantized.ternaryCEParameters _
      (ceNextParameters CEQuantized.ceQuantWitnessFeatures 0 0
        (safeStepSize CEQuantized.ceQuantWitnessFeatures 0 0)))) < _
  apply CEQuantized.ceOneHot_ternary_safeStep_lt
  · exact selectedScale_level_pos _ _
  · rw [CEQuantized.ceQuantWitness_range]
    norm_num
  · exact ceQuantWitness_selectedScale_strict_margin

/-- The real 16-bit payload containing the selected scale and the actual
raw successor's exact ternary word at that same scale. -/
noncomputable def packedSelected : BitVec 16 :=
  Hagi.Runtime.dyadicBlock
    (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor)
    (fun j => Hagi.Runtime.ternaryValueEncode
      (Hagi.Runtime.dyadicLevel
        (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))
      (CEPackedStep.rawSuccessor.ofLp j))

/-- Decoding the selected payload returns precisely the selected quantized
parameters, retaining the common scale across encoding and decoding. -/
theorem decodeStep_packedSelected : CEPackedStep.decodeStep packedSelected =
    some (CEQuantized.ternaryCEParameters
      (Hagi.Runtime.dyadicLevel
        (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))
      CEPackedStep.rawSuccessor) := by
  unfold CEPackedStep.decodeStep packedSelected
  rw [Hagi.Runtime.dyadicBlockDecode_encode]
  simp only [Option.map_some]
  congr 1
  ext j
  exact Hagi.Runtime.ternaryValueDecode_encode _ _

/-- The decoded selected packed witness has actual strict CE descent. -/
theorem decoded_packedSelected_strict_descent :
    ∃ decoded_w : EuclideanSpace ℝ (Fin 5),
      CEPackedStep.decodeStep packedSelected = some decoded_w ∧
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures decoded_w) <
        Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  refine ⟨CEQuantized.ternaryCEParameters
    (Hagi.Runtime.dyadicLevel
      (selectedScale CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))
    CEPackedStep.rawSuccessor, decodeStep_packedSelected, ?_⟩
  exact ceQuantWitness_selectedScale_strict_descent

end Hagi.Model.CEScaleSelection
