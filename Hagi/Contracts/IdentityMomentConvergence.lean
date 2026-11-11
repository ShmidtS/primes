import Hagi.Contracts.BatchCEAlignmentBudget

/-!
# Identity-feature mean-prediction convergence

On identity features, the fixed-batch mean residual equals mean model
probability minus the empirical one-hot average.  The actual C205
mean-gradient limit therefore gives marginal moment matching on a positive
batch, with a singleton specialization.  These statements make no claim of
parameter convergence, individual mixed-batch prediction convergence,
held-out generalization or an optimal architecture.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.IdentityMomentConvergence

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BatchCETrajectory
open Hagi.Contracts.BatchCEAlignmentBudget Hagi.Prelude
open Filter Topology

variable {B n a r c k : ℕ}

/-- Arithmetic-mean model probabilities at one current parameter vector.
Empty-batch averaging is totalized here but excluded from the probability
limits by the positive-batch premise. -/
noncomputable def meanPrediction (X : Fin B → Matrix (Fin n) (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun v => (1 / (B : ℝ)) *
    ∑ b, softDef (ceLogits (X b) θ) v

/-- Arithmetic-mean one-hot labels on the supplied finite batch. -/
noncomputable def empiricalTarget (y : Fin B → Fin n) : Fin n → ℝ :=
  fun v => (1 / (B : ℝ)) * ∑ b, ((Pi.single (y b) (1 : ℝ) : Fin n → ℝ)) v

/-- Exact signed residual identity for identity features. -/
private theorem meanPrediction_sub_empiricalTarget_eq_meanResidualTranspose
    (X : Fin B → Matrix (Fin n) (Fin n) ℝ) (hX : ∀ b, X b = 1)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → Fin n) (hB : 0 < B) (v : Fin n) :
    meanPrediction X θ v - empiricalTarget y v =
      meanResidualTranspose X θ y v := by
  classical
  have hres (b : Fin B) :
      residualTranspose (X b) θ (y b) v =
        softDef (ceLogits (X b) θ) v - ((Pi.single (y b) (1 : ℝ) : Fin n → ℝ)) v := by
    rw [hX b]
    simp [residualTranspose, ceResidual, Hagi.Energy.smax, Matrix.one_apply,
      Pi.single_apply]
  unfold meanPrediction empiricalTarget meanResidualTranspose
  simp_rw [hres]
  rw [Finset.sum_sub_distrib]
  have hBne : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hB)
  field_simp

/-- Direct consequence of the real C205 gradient limit on the actual
fixed-batch trajectory: identity-feature mean probabilities approach the
supplied empirical one-hot average. -/
theorem fixedBatch_meanPrediction_tendsto_empiricalTarget
    (X : Fin B → Matrix (Fin n) (Fin n) ℝ) (hX : ∀ b, X b = 1)
    (y : Fin B → Fin n) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hB : 0 < B) :
    Tendsto (fun t => meanPrediction X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)))
      atTop (𝓝 (empiricalTarget y)) := by
  have hlim :=
    Hagi.Contracts.BatchCEAlignmentBudget.fixedBatch_meanGradient_tendsto_zero
      X y S opCost opRisk write
  rw [tendsto_pi_nhds]
  intro v
  have hcoord : Tendsto (fun t => meanResidualTranspose X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)) y v)
      atTop (𝓝 0) := by
    exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) v).continuousAt.tendsto.comp
      hlim
  have hdiff : Tendsto (fun t => meanPrediction X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)) v -
        empiricalTarget y v) atTop (𝓝 0) := by
    convert hcoord using 1
    funext t
    exact meanPrediction_sub_empiricalTarget_eq_meanResidualTranspose
      X hX _ y hB v
  simpa using hdiff.add_const (empiricalTarget y v)

/-- For a singleton batch this is convergence of the actual prediction for
that one supplied example, not for every example of a general dataset. -/
theorem fixedBatch_meanPrediction_tendsto_empiricalTarget_batch_one
    (X : Fin 1 → Matrix (Fin n) (Fin n) ℝ) (hX : ∀ b, X b = 1)
    (y : Fin 1 → Fin n) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fun t => softDef (ceLogits (X 0)
      (coreParameters (fixedBatchState X y S opCost opRisk write t))))
      atTop (𝓝 ((Pi.single (y 0) (1 : ℝ) : Fin n → ℝ))) := by
  have hpred : (fun t => softDef (ceLogits (X 0)
      (coreParameters (fixedBatchState X y S opCost opRisk write t)))) =
      (fun t => meanPrediction X
        (coreParameters (fixedBatchState X y S opCost opRisk write t))) := by
    funext t v
    simp [meanPrediction]
  have htarget : (Pi.single (y 0) (1 : ℝ) : Fin n → ℝ) = empiricalTarget y := by
    funext v
    simp [empiricalTarget]
  rw [hpred, htarget]
  exact fixedBatch_meanPrediction_tendsto_empiricalTarget X hX y S opCost opRisk
    write (by norm_num)

end Hagi.Contracts.IdentityMomentConvergence
