import Hagi.Contracts.GatedCETrajectory

/-!
# Infinite accounting of gated safe-step majorizer drops

For the fixed-target canonical gated trajectory, `fixedGatedDrop` evaluates
`gatedSafeDrop` at the actual current `coreParameters` of every recursive
state.  The existing exact loss-difference telescope and final CE
nonnegativity bound every partial sum by the initial objective.  Consequently
the nonnegative drops are summable, tend to zero, and have total sum at most
the initial objective.

Zero squared residual-transpose alignment collapses the direction itself, not
merely the scalar certificate.  The safe-step size may still use its unit
curvature fallback, but its displacement and curvature vanish and the actual
executed CE is exactly preserved.

These are infinite-time majorizer-drop statements only.  They do not assert
summability of squared alignment or residuals, convergence of parameters or
residuals, an optimal loss limit, repeated certificate/budget feasibility, or
any external-quality claim.

Proof references are the existing `GatedCETrajectory` telescope, the
`GatedCESafeStep` algebra, and Mathlib's `summable_of_sum_range_le`.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCESummability

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Hagi.Contracts.GatedCETrajectory
open Filter Topology

section ZeroAlignment

variable {V : Type} [Fintype V]
variable {n : ℕ}

/-- Zero squared residual-transpose alignment makes the direction zero. -/
theorem gatedDirection_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedDirection X θ t = 0 := by
  have hR : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      gatedResidualTranspose X θ t j = 0 := by
    apply (Finset.sum_sq_eq_zero_iff Finset.univ
      (gatedResidualTranspose X θ t)).mp
    simpa only [gatedAlignment] using hA
  apply PiLp.ext
  intro j
  simp [gatedDirection_ofLp, hR j (Finset.mem_univ j)]

/-- Zero alignment makes both second-order terms vanish with the direction. -/
theorem gatedCurvature_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedCurvature X θ t = 0 := by
  have hD := gatedDirection_eq_zero_of_alignment_eq_zero X θ t hA
  simp [gatedCurvature, gatedResidualSecondOrderMass, gatedStepRange,
    gatedUnitAbsLogit, gatedUnitSecondOrderMass, hD]

/-- The certified majorizer drop is exactly zero at zero alignment. -/
theorem gatedSafeDrop_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedSafeDrop X θ t = 0 := by
  have hC := gatedCurvature_eq_zero_of_alignment_eq_zero X θ t hA
  simp [gatedSafeDrop, hC, hA]

/-- Even with the unit curvature fallback, zero alignment gives no update. -/
theorem gatedNextParameters_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) :
    gatedNextParameters X θ t (gatedSafeStepSize X θ t) = θ := by
  rw [gatedNextParameters, gatedDirection_eq_zero_of_alignment_eq_zero X θ t hA]
  simp

/-- The actual CE after the computed safe step is exactly the old CE. -/
theorem gated_ceOneHot_safeStep_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) :
    Hagi.ceOneHot t (gatedForward X
      (gatedNextParameters X θ t (gatedSafeStepSize X θ t))) =
        Hagi.ceOneHot t (gatedForward X θ) := by
  rw [gatedNextParameters_eq_of_alignment_eq_zero X θ t hA]

end ZeroAlignment

section ExecutedZeroAlignment

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- The canonical executed transition preserves gated CE at zero alignment. -/
theorem gatedCEObjective_gatedCETrainStep_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hA : gatedAlignment X (coreParameters S) t = 0) :
    gatedCEObjective X t (gatedCETrainStep X t S opCost opRisk write) =
      gatedCEObjective X t S := by
  rw [gatedCEObjective, gatedCEObjective, coreParameters_gatedCETrainStep]
  exact gated_ceOneHot_safeStep_eq_of_alignment_eq_zero X (coreParameters S) t hA

end ExecutedZeroAlignment

section InfiniteAccounting

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- The current majorizer-drop sequence `fixedGatedDrop`, evaluated using the
actual parameters of `fixedGatedState s`, never at stale or successor parameters. -/
noncomputable def fixedGatedDrop (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) : ℝ :=
  gatedSafeDrop X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- Every current safe-step majorizer drop is nonnegative. -/
theorem fixedGatedDrop_nonneg (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    0 ≤ fixedGatedDrop X t S opCost opRisk write s :=
  gatedSafeDrop_nonneg X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- Actual telescoping and final CE nonnegativity bound every partial sum of
current drops by the initial gated CE. -/
theorem fixedGatedDrop_sum_le_initial [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ s ∈ Finset.range T, fixedGatedDrop X t S opCost opRisk write s ≤
      gatedCEObjective X t S := by
  calc
    ∑ s ∈ Finset.range T, fixedGatedDrop X t S opCost opRisk write s ≤
        gatedCEObjective X t S -
          fixedGatedObjective X t S opCost opRisk write T :=
      fixedGatedObjective_sum_gatedSafeDrop_le_telescope
        X t S opCost opRisk write T
    _ ≤ gatedCEObjective X t S :=
      sub_le_self _ (fixedGatedObjective_nonneg X t S opCost opRisk write T)

/-- The sequence of actual current majorizer drops is summable. -/
theorem fixedGatedDrop_summable [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Summable (fixedGatedDrop X t S opCost opRisk write) := by
  exact summable_of_sum_range_le
    (fixedGatedDrop_nonneg X t S opCost opRisk write)
    (fixedGatedDrop_sum_le_initial X t S opCost opRisk write)

/-- Infinite-time summability forces the current majorizer drops to zero. -/
theorem fixedGatedDrop_tendsto_zero [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedGatedDrop X t S opCost opRisk write) atTop (𝓝 0) :=
  (fixedGatedDrop_summable X t S opCost opRisk write).tendsto_atTop_zero

/-- The total sum of actual current majorizer drops is at most initial CE. -/
theorem fixedGatedDrop_tsum_le_initial [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    ∑' s, fixedGatedDrop X t S opCost opRisk write s ≤
      gatedCEObjective X t S :=
  (fixedGatedDrop_summable X t S opCost opRisk write).tsum_le_of_sum_range_le
    (fixedGatedDrop_sum_le_initial X t S opCost opRisk write)

end InfiniteAccounting

end Hagi.Contracts.GatedCESummability
