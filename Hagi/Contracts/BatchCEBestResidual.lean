import Hagi.Contracts.BatchCEAlignmentBudget

/-!
# Best-prefix common residual bounds

The minimum squared common batch residual over a nonempty prefix is at most
at most its arithmetic average.  The finite feature-curvature budget therefore
supplies an explicit best-prefix `O(1/T)` bound, with the exact constants of
`BatchCEAlignmentBudget`.  This is not a last-iterate convergence theorem.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BatchCEBestResidual

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BatchCETrajectory
open Hagi.Contracts.BatchCEAlignmentBudget

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Some actual iteration in a nonempty finite prefix has common squared
mean residual at most the exact trajectory Cesaro average. -/
theorem exists_alignment_le_fixedAlignmentCesaro
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) (hT : 0 < T) :
    ∃ t : Fin T, batchAlignment X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      fixedAlignmentCesaro X y S opCost opRisk write T := by
  classical
  let f : ℕ → ℝ := fun t => batchAlignment X
    (coreParameters (fixedBatchState X y S opCost opRisk write t)) y
  obtain ⟨t, htT, htmin⟩ := Finset.exists_min_image (Finset.range T) f
    ⟨0, Finset.mem_range.mpr hT⟩
  have htlt : t < T := Finset.mem_range.mp htT
  refine ⟨⟨t, htlt⟩, ?_⟩
  have hmul : f t * (T : ℝ) ≤ ∑ i ∈ Finset.range T, f i := by
    calc
      f t * (T : ℝ) = ∑ _i ∈ Finset.range T, f t := by
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ Finset.range T, f i := by
        exact Finset.sum_le_sum fun i hi => htmin i hi
  have hle : f t ≤ (∑ i ∈ Finset.range T, f i) / (T : ℝ) := by
    exact (le_div_iff₀ (Nat.cast_pos.mpr hT)).2 hmul
  simpa only [fixedAlignmentCesaro, f] using hle

/-- An actual best-prefix common squared mean residual obeys the explicit
feature-and-initial-loss numerator divided by the positive prefix length. -/
theorem exists_alignment_le_initial_div_time [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) (hT : 0 < T) :
    ∃ t : Fin T, batchAlignment X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      (((rangeCurvature X + 1) / 2) * batchCEObjective X y S) / (T : ℝ) := by
  obtain ⟨t, ht⟩ := exists_alignment_le_fixedAlignmentCesaro
    X y S opCost opRisk write T hT
  exact ⟨t, ht.trans (fixedAlignmentCesaro_le X y S opCost opRisk write T)⟩

/-- The corresponding common residual norm has a square-root best-prefix
bound.  This does not claim the norm at the final time is small. -/
theorem exists_sqrt_alignment_le_sqrt_initial_div_time [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) (hT : 0 < T) :
    ∃ t : Fin T, Real.sqrt (batchAlignment X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y) ≤
      Real.sqrt ((((rangeCurvature X + 1) / 2) *
        batchCEObjective X y S) / (T : ℝ)) := by
  obtain ⟨t, ht⟩ := exists_alignment_le_initial_div_time
    X y S opCost opRisk write T hT
  exact ⟨t, Real.sqrt_le_sqrt ht⟩

end Hagi.Contracts.BatchCEBestResidual
