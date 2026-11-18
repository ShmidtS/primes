/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Semantics.Split
import Hagi.Probability.FreedmanTwoSided
import Hagi.Theory.CEChain

/-!
# Certified discrete Flow Matching bridge

C420. The bridge between Conditional Flow Matching (Lipman et al.,
Flow Matching for Generative Modeling) and the certified learning
stack of this repository — an HONEST DISCRETE core, no
continuous-time overreach:

* the OT conditional path and vector field (paper equations for
  `μ_t = t·x₁`, `σ_t = 1 − (1 − σ_min)·t`): `cfmPsi` (the affine
  interpolation `ψ_t`), `cfmOtField` (the closed-form OT conditional
  VF, the ratio of the paper with the same denominator `σ_t`);
* the discrete CFM objective `cfmLoss`: a finite-`Fintype`
  expectation (`pmfMean`, the finite-Ω noise binder — the Gaussian
  prior is NOT constructed, any `PMF Ω` carries it) of the
  squared-difference sample loss `cfmSampleLoss` over a finite time
  grid, data distribution and noise distribution;
* the objective-side instantiation: `cfmSampleLoss` IS the C384
  objective `Hagi.Semantics.sqDiffObjective` evaluated at the
  velocity prediction `v t (ψ_t x₀)` against the OT field target —
  the bridge `cfmSampleLoss_eq_sqDiff` is definitional;
* the unbiasedness bridge `cfm_expected_diff` (with
  `cfmLoss_nested`, the law of total expectation via `pmfMean_bind`):
  the per-sample conditional estimator of the loss DIFFERENCE is
  unbiased — the discrete Fintype counterpart of the ROLE of the
  paper's theorem (equality of CFM and FM objectives up to a
  constant, hence equal gradients);
* the certified-FM micro-loop `cfmLinStep`: the linearized
  (constant-field) velocity parameter carries a
  `Hagi.Theory.CEChain.UniversalSafeStep` structure (C387) whose
  majorizer law is an EQUALITY, so `cfm_lin_descent` specializes the
  universal certified drop, and `cfm_lin_safe_step_zero` shows the
  universal safe step size `A / (2 * C)` drives the sample loss
  exactly to zero (reaching the OT field in one certified step).

## Pins (scope honesty)

- The continuous-time CNF / continuity-equation theory and the
  paper's equality `L_CFM = L_FM` (its theorem on marginal vector
  fields) are NOT formalized here: no statement claims them.  The
  unbiasedness statement below is a finite-`Fintype` computation.
- Gaussian sampling is a binder: the noise lives on a finite `Ω`
  with a `PMF Ω`; no Gaussian measure is constructed.
- Marginal-VF existence is premised by the framing, never proved.
- Convexity in the velocity parameter holds only in the linearized
  `cfmLinStep` specialization (quadratic loss); no general
  convexity-in-`v` claim is made.
- `cfmOtField` divides by `cfmSigma`; the paper's own regime keeps
  the denominator positive, and no theorem here depends on the
  quotient's sign.

## Straightness note (OT paths ↔ zero-drift tracking)

The OT conditional path `cfmPsi` is affine in `t`, so its
conditional vector field is CONSTANT along the path — the
discrete shadow of the paper's straightness discussion.  In the
tracking frame of `Hagi.Theory.OnlinePL` (C412) a straight path is
the zero-drift regime: the target does not move, so the tracking
recursion contracts without the steady-state radius.  This is a
documented analogy, not a theorem.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.FlowMatching

open Hagi.Probability (pmfMean pmfMean_bind pmfMean_map pmfMean_sub
  pmfMean_congr PMF.uniformOfFinset)
open scoped BigOperators

/-! ## The OT conditional path and vector field -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- The OT schedule denominator `σ_t = 1 − (1 − σ_min) · t`
(paper equation for `σ_t(x)` of the OT path). -/
def cfmSigma (σmin t : ℝ) : ℝ := 1 - (1 - σmin) * t

/-- The OT conditional path `ψ_t(x₀) = σ_t · x₀ + t · x₁` (paper
equation: `ψ_t(x) = (1 − (1 − σ_min) t) x + t x₁`): the affine
interpolation from noise `x₀` to data `x₁`. -/
def cfmPsi (σmin t : ℝ) (x0 x1 : V → ℝ) : V → ℝ :=
  fun i => cfmSigma σmin t * x0 i + t * x1 i

/-- The closed-form OT conditional vector field (paper equation:
`u_t(x | x₁) = (x₁ − (1 − σ_min) x) / (1 − (1 − σ_min) t)`), as a
field over the vocabulary `V`.  The denominator is `cfmSigma`; see
the module pins for the division. -/
noncomputable def cfmOtField (σmin t : ℝ) (x0 x1 : V → ℝ) : V → ℝ :=
  fun i => (x1 i - (1 - σmin) * x0 i) / cfmSigma σmin t

/-! ## The sample loss as an ObjectiveSpec instantiation (C384) -/

/-- The per-sample CFM loss: the squared difference between the
velocity prediction `v t (ψ_t x₀)` and the OT conditional field
target.  Definitional bridge: this IS the C384 objective
`Hagi.Semantics.sqDiffObjective` evaluated on the prediction and
the target — see `cfmSampleLoss_eq_sqDiff`. -/
noncomputable def cfmSampleLoss (σmin t : ℝ)
    (v : ℝ → (V → ℝ) → (V → ℝ)) (x0 x1 : V → ℝ) : ℝ :=
  Hagi.Semantics.sqDiffObjective.loss (v t (cfmPsi σmin t x0 x1))
    (cfmOtField σmin t x0 x1)

omit [Nonempty V] in
/-- The floor law transports from the objective side: the sample
loss is nonnegative. -/
theorem cfmSampleLoss_nonneg (σmin t : ℝ)
    (v : ℝ → (V → ℝ) → (V → ℝ)) (x0 x1 : V → ℝ) :
    0 ≤ cfmSampleLoss σmin t v x0 x1 :=
  Hagi.Semantics.sqDiffObjective.loss_nonneg _ _

omit [Nonempty V] in
/-- The bridge to the C384 objective side, definitionally: the CFM
sample loss is `Hagi.Semantics.sqDiffObjective` on the pair
(velocity prediction at the interpolated point, OT field target). -/
theorem cfmSampleLoss_eq_sqDiff (σmin t : ℝ)
    (v : ℝ → (V → ℝ) → (V → ℝ)) (x0 x1 : V → ℝ) :
    cfmSampleLoss σmin t v x0 x1
      = Hagi.Semantics.sqDiffObjective.loss
          (v t (cfmPsi σmin t x0 x1)) (cfmOtField σmin t x0 x1) :=
  rfl

/-! ## The discrete CFM objective: finite-grid expectation -/

section Objective
variable {D Ω : Type} [Fintype D] [Fintype Ω]

/-- The joint sampling distribution of the discrete CFM objective:
the uniform law on the finite time grid `Fin m`, the data law `q`
and the noise law `p` (finite `Ω` — the Gaussian prior binder). -/
noncomputable def cfmJoint (m : ℕ)
    (hm : (Finset.univ : Finset (Fin m)).Nonempty)
    (q : PMF D) (p : PMF Ω) : PMF (Fin m × D × Ω) :=
  (PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hm).bind fun j =>
    q.bind fun d => p.map fun ω => (j, d, ω)

/-- The discrete CFM objective: the `pmfMean` of the sample loss
under the joint law.  The data `x₁` and the noise field `x₀` are
deterministic functions of their finite sample spaces (the
finite-Ω pattern of `Hagi.Probability.FreedmanTwoSided`). -/
noncomputable def cfmLoss (m : ℕ)
    (hm : (Finset.univ : Finset (Fin m)).Nonempty) (σmin : ℝ)
    (T : Fin m → ℝ) (q : PMF D) (p : PMF Ω) (n : Ω → V → ℝ)
    (x1 : D → V → ℝ) (v : ℝ → (V → ℝ) → (V → ℝ)) : ℝ :=
  pmfMean (cfmJoint m hm q p) fun s =>
    cfmSampleLoss σmin (T s.1) v (n s.2.2) (x1 s.2.1)

omit [Nonempty V] in
/-- The law of total expectation, CFM shape: the joint objective
decomposes into nested conditional expectations over the time grid,
the data law and the noise law (`pmfMean_bind`, `pmfMean_map`). -/
theorem cfmLoss_nested (m : ℕ)
    (hm : (Finset.univ : Finset (Fin m)).Nonempty) (σmin : ℝ)
    (T : Fin m → ℝ) (q : PMF D) (p : PMF Ω) (n : Ω → V → ℝ)
    (x1 : D → V → ℝ) (v : ℝ → (V → ℝ) → (V → ℝ)) :
    cfmLoss m hm σmin T q p n x1 v
      = pmfMean (PMF.uniformOfFinset (Finset.univ : Finset (Fin m)) hm)
          fun j => pmfMean q fun d =>
            pmfMean p fun ω => cfmSampleLoss σmin (T j) v (n ω) (x1 d) := by
  simp only [cfmLoss, cfmJoint, pmfMean_bind, pmfMean_map]

omit [Nonempty V] in
/-- The unbiasedness bridge — the honest discrete counterpart of
the ROLE of the paper's CFM/FM theorem (there: the two objectives
coincide up to a θ-free constant, so their gradients agree and the
conditional per-sample estimator is unbiased).  Here, in the finite
`Fintype` frame: the expectation of the per-sample loss DIFFERENCE
estimator equals the difference of the objectives (`pmfMean_sub`),
so minimizing the conditional (per-sample) criterion and minimizing
the joint objective select the same field.  The continuous theorem
itself is NOT formalized (module pins). -/
theorem cfm_expected_diff (m : ℕ)
    (hm : (Finset.univ : Finset (Fin m)).Nonempty) (σmin : ℝ)
    (T : Fin m → ℝ) (q : PMF D) (p : PMF Ω) (n : Ω → V → ℝ)
    (x1 : D → V → ℝ) (v w : ℝ → (V → ℝ) → (V → ℝ)) :
    pmfMean (cfmJoint m hm q p) (fun s =>
      cfmSampleLoss σmin (T s.1) v (n s.2.2) (x1 s.2.1)
        - cfmSampleLoss σmin (T s.1) w (n s.2.2) (x1 s.2.1))
      = cfmLoss m hm σmin T q p n x1 v
        - cfmLoss m hm σmin T q p n x1 w :=
  pmfMean_sub _ _ _

end Objective

/-! ## The certified micro-loop: linearized VF as a UniversalSafeStep (C387) -/

omit [Nonempty V] in
/-- The single-sample majorizer EQUALITY of the linearized velocity
parameter: with the constant field `v ≡ θ` the CFM sample loss is
quadratic in `θ`, and the gradient step `θ − η · ∇` satisfies the
majorizer `L(step) = L − η·A + η²·C` with `A = C = 4·∑(θ − u)²` as
an identity (convexity holds exactly in this specialization — the
module pins scope the convexity claim here). -/
theorem cfmLin_majorizer_eq (σmin t : ℝ) (x0 x1 θ : V → ℝ) (η : ℝ) :
    cfmSampleLoss σmin t
        (fun _ _ i => θ i - η * (2 * (θ i - cfmOtField σmin t x0 x1 i))) x0 x1
    = cfmSampleLoss σmin t (fun _ _ => θ) x0 x1
        - η * (4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2)
        + η ^ 2 * (4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2) := by
  unfold cfmSampleLoss Hagi.Semantics.sqDiffObjective
  have key : ∀ i : V,
      (θ i - η * (2 * (θ i - cfmOtField σmin t x0 x1 i))
          - cfmOtField σmin t x0 x1 i) ^ 2
        = (θ i - cfmOtField σmin t x0 x1 i) ^ 2
            - η * (4 * (θ i - cfmOtField σmin t x0 x1 i) ^ 2)
            + η ^ 2 * (4 * (θ i - cfmOtField σmin t x0 x1 i) ^ 2) :=
    fun i => by ring
  calc ∑ i, (θ i - η * (2 * (θ i - cfmOtField σmin t x0 x1 i))
        - cfmOtField σmin t x0 x1 i) ^ 2
      = ∑ i, ((θ i - cfmOtField σmin t x0 x1 i) ^ 2
            - η * (4 * (θ i - cfmOtField σmin t x0 x1 i) ^ 2)
            + η ^ 2 * (4 * (θ i - cfmOtField σmin t x0 x1 i) ^ 2)) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2)
            - η * (4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2)
            + η ^ 2 * (4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.mul_sum]

/-- The certified-FM micro-loop: the linearized (constant-field)
velocity parameter `θ` as a `Hagi.Theory.CEChain.UniversalSafeStep`
(C387) on ONE sample — the TT-CAT micro-loop shape that can drive
FM training.  Alignment and curvature coincide (`A = C = 4‖θ −
u‖²`), and the majorizer law is the equality
`cfmLin_majorizer_eq`. -/
noncomputable def cfmLinStep (σmin t : ℝ) (x0 x1 : V → ℝ) :
    Hagi.Theory.CEChain.UniversalSafeStep (V → ℝ) where
  loss θ := cfmSampleLoss σmin t (fun _ _ => θ) x0 x1
  step θ η := fun i =>
    θ i - η * (2 * (θ i - cfmOtField σmin t x0 x1 i))
  alignment θ := 4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2
  curvature θ := 4 * ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2
  alignment_nonneg θ := by positivity
  curvature_nonneg θ := by positivity
  majorizes θ η _ := le_of_eq (cfmLin_majorizer_eq σmin t x0 x1 θ η)

omit [Nonempty V] in
/-- Certified descent, FM shape (C387 chain): the universal safe
step theorem of `Hagi.Theory.CEChain` applies verbatim to the
linearized velocity parameter — at positive curvature the safe step
decreases the sample CFM loss by at least the certified drop
`A ^ 2 / (4 * C)`. -/
theorem cfm_lin_descent (σmin t : ℝ) (x0 x1 θ : V → ℝ)
    (hC : 0 < (cfmLinStep σmin t x0 x1).curvature θ) :
    (cfmLinStep σmin t x0 x1).loss
        ((cfmLinStep σmin t x0 x1).step θ
          (Hagi.Theory.CEChain.universalStepSize (cfmLinStep σmin t x0 x1) θ))
      ≤ (cfmLinStep σmin t x0 x1).loss θ
        - Hagi.Theory.CEChain.universalDrop (cfmLinStep σmin t x0 x1) θ :=
  Hagi.Theory.CEChain.universal_descent _ θ hC

omit [Nonempty V] in
/-- The single-sample certified micro-loop closes exactly: at a
nonzero error the universal safe step size is `A / (2 * C) = 1 / 2`,
and the step `θ − (1/2) · 2 (θ − u)` lands on the OT field `u`
itself, so the sample CFM loss after the safe step is ZERO.  One
sample, constant-field specialization (module pins) — not a claim
about full FM training dynamics. -/
theorem cfm_lin_safe_step_zero (σmin t : ℝ) (x0 x1 θ : V → ℝ)
    (hE : ∑ i, (θ i - cfmOtField σmin t x0 x1 i) ^ 2 ≠ 0) :
    (cfmLinStep σmin t x0 x1).loss
      ((cfmLinStep σmin t x0 x1).step θ
        (Hagi.Theory.CEChain.universalStepSize (cfmLinStep σmin t x0 x1) θ))
      = 0 := by
  have hhalf : Hagi.Theory.CEChain.universalStepSize
      (cfmLinStep σmin t x0 x1) θ = 1 / 2 := by
    simp only [Hagi.Theory.CEChain.universalStepSize, cfmLinStep]
    field_simp
  rw [hhalf]
  unfold cfmLinStep cfmSampleLoss Hagi.Semantics.sqDiffObjective
  have hstep : ∀ i : V,
      θ i - (1 / 2) * (2 * (θ i - cfmOtField σmin t x0 x1 i))
        = cfmOtField σmin t x0 x1 i := fun i => by ring
  simp only [hstep]
  simp

end Hagi.Theory.FlowMatching
