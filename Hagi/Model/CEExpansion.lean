/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEDescent

/-!
# One-coordinate latent/readout expansion of a finite categorical head

The appended latent feature can be arbitrary.  A zero appended readout
coefficient preserves every logit and every categorical cross-entropy loss.
The new coefficient remains available to an ordinary parameter update.
These equations concern the supplied finite model, not a Transformer,
held-out performance, native computation or universal architecture optimality.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEExpansion

open Hagi.Model

/-- Append one supplied latent feature to every finite categorical row. -/
def expandedFeatures {V : Type} {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (Z : V → ℝ) :
    Matrix V (Fin (d + 1)) ℝ :=
  fun v => Fin.snoc (X v) (Z v)

/-- Append one readout coefficient to the existing finite parameters. -/
noncomputable def expandedParameters {d : ℕ}
    (θ : EuclideanSpace ℝ (Fin d)) (gamma : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc θ.ofLp gamma)

/-- The exact enlarged logit is the old logit plus the new feature times
its readout coefficient. -/
theorem ceLogits_expandedParameters {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (gamma : ℝ) (v : V) :
    ceLogits (expandedFeatures X Z) (expandedParameters θ gamma) v =
      ceLogits X θ v + Z v * gamma := by
  simp [ceLogits, Matrix.mulVec, dotProduct, expandedFeatures,
    expandedParameters, Fin.sum_univ_castSucc]

/-- A zero new readout coefficient preserves categorical cross-entropy.
The new latent feature need not vanish. -/
theorem ceOneHot_expandedParameters_zero {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (t : V) :
    Hagi.ceOneHot t (ceLogits (expandedFeatures X Z)
      (expandedParameters θ 0)) = Hagi.ceOneHot t (ceLogits X θ) := by
  congr 1
  funext v
  simpa using ceLogits_expandedParameters X θ Z 0 v

/-- Declared operation-cell count for preparing the new finite batch /
vocabulary block, in the same abstract operation unit as supplied training
costs.  This is not physical FLOPs, RAM, bytes or execution time. -/
def expandedFeatureEvaluationCount (B : ℕ) (V : Type) [Fintype V] : ℕ :=
  B * Fintype.card V

end Hagi.Model.CEExpansion
