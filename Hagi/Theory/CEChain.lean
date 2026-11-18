/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEModel
import Hagi.Model.GatedCEDescent
import Hagi.Model.CEGlobalConvergence
import Hagi.Model.CEMarginPL
import Hagi.Unified.StochasticCELearning

/-!
# The unified cross-entropy theory chain

Audit 4.1 (A17 stage 2): the CE family is ONE mathematical chain,
each stage a specialization of the previous one by an explicit
bridge — not competing variants:

```
CrossEntropy ──▶ Gradient ──▶ Curvature ──▶ SafeStep ──▶ Batch ──▶ Stochastic ──▶ Convergence
  `Hagi.ceOneHot`  majorizer   `η = A / 2C`   universal   batch     accept-form     `ce_global_convergence_reg_closed`
  (Core.Concat)    L ≤ L−ηA+η²C  drop A²/4C    form once   mean      Â−r / Ĉ+u       `_margin` / whp loop
```

* CORE — the SSOT functional `Hagi.ceOneHot` (floor
  `Hagi.Model.CEHeldout.ceOneHot_nonneg`, gradient
  `Hagi.Model.CEGradient.fderiv_ceOneHot_mulVec`).
* STEP — this module proves the universal safe-step theorem ONCE:
  for any model with a quadratic majorizer
  `L(step θ η) ≤ L θ - η * A + η ^ 2 * C` (`η ≥ 0`), the step
  `universalStepSize = A / (2 * C)` achieves the drop
  `universalDrop = A ^ 2 / (4 * C)`
  (`universal_descent`).  Every mature safe-step rule of the family
  is then a ONE-LINE instance:
  - `singleSampleStep` — `Model.CEDescent`: curvature
    `(ceStepRange) ^ 2 / 8`, so `η* = 4A / R ^ 2` and the drop is
    `2 * A ^ 2 / R ^ 2` (`singleSample_stepSize_ident`,
    `singleSample_drop_ident`, `singleSample_descent`).
  - `batchStep` — `Model.BatchCEDescentSafeStep`: curvature
    `batchRangeSquare / 8`, the same line form
    (`batch_stepSize_ident`, `batch_descent`).
  - `gatedStep` — `Model.GatedCESafeStep`: curvature
    `gatedCurvature`, so `η* = A / 2C` and the drop is
    `A ^ 2 / (4 * C)` verbatim (`gated_stepSize_ident`,
    `gated_descent`).
  Each descent corollary has proof term `universal_descent _ θ hC`:
  the quadratic-minimization argument that the three source modules
  each re-proved is now stated and proved exactly once; the source
  statements are unchanged (frozen) and stay the SSOT consumers.
* BATCH — the batch carrier is the SAME construction on the
  arithmetic-mean majorizer (`batchStep`), not a new theory.
* STOCHASTIC — `universal_accept_form`: with an alignment estimate
  `Â` plus nonnegative uncertainty `r` and a curvature estimate `Ĉ`
  plus uncertainty `u`, the accept condition
  `0 < Â - r ∧ 0 < Ĉ + u` certifies the drop lower bound
  `(Â - r) ^ 2 / (4 * (Ĉ + u))` directly from the universal form
  (pure algebra; the full Freedman-radius theorem is C388).
  The end-to-end whp learning theorem stays in
  `Hagi.Unified.StochasticCELearning` (re-exported below).
* CONVERGENCE — the chain head: `ce_global_convergence_reg_closed`
  (PL geometric rate for the regularized head) and
  `ce_global_convergence_margin` re-exported in chain terms.

## Honest pins (what genuinely remains separate)

- The GatedCE zero-curvature unit fallback (`η = 1`, drop `A`) is
  outside the universal form: the quadratic degenerates.  It stays
  in `Model.GatedCESafeStep` (documented C365: the pointwise
  curvature law `0 < R ^ 2 → 0 < A` is false there).
- `Model.CEModel` — the C364 `η = 4A / R ^ 2` descent CONTRACT on
  `loss/next/alignment/rangeSquare`: a parallel packaging of the
  same single/batch facts; this module does not change it.
- `Model.NonlinearCE` / `Model.CEJacobianMajorizer` (Jacobian
  remainder ball), `Model.CEQuantized` (penalty constants), and the
  `Semantics.Split` objective combination (C384) are separate
  tranches, not instances of the quadratic form.
- The margin/realizability convergence route stays open
  (`Model.CEGlobalConvergence` pins).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.CEChain

/-! ## Stage 2 — the universal safe step, proved once -/

variable {Θ : Type}

/-- The universal quadratic-majorizer data of a CE step: a loss, an
`η`-parametrized update, the first-order alignment `A` and the
curvature `C`, with the one law every mature CE tranche proves for
all nonnegative steps: `L(step θ η) ≤ L θ - η * A + η ^ 2 * C`. -/
structure UniversalSafeStep (Θ : Type) where
  /-- The loss being descended. -/
  loss : Θ → ℝ
  /-- The parameter update at step size `η`. -/
  step : Θ → ℝ → Θ
  /-- First-order alignment of the update direction. -/
  alignment : Θ → ℝ
  /-- Quadratic curvature coefficient of the majorizer. -/
  curvature : Θ → ℝ
  /-- The alignment is nonnegative. -/
  alignment_nonneg : ∀ θ : Θ, 0 ≤ alignment θ
  /-- The curvature is nonnegative. -/
  curvature_nonneg : ∀ θ : Θ, 0 ≤ curvature θ
  /-- The quadratic majorizer law: for every nonnegative step
  size, the loss after the step is bounded by
  `L θ - η * A + η ^ 2 * C`. -/
  majorizes : ∀ θ : Θ, ∀ η : ℝ, 0 ≤ η →
    loss (step θ η) ≤ loss θ - η * alignment θ + η ^ 2 * curvature θ

/-- The universal safe step size `A / (2 * C)`: the stationary
point of the quadratic majorizer. -/
noncomputable def universalStepSize (U : UniversalSafeStep Θ)
    (θ : Θ) : ℝ :=
  U.alignment θ / (2 * U.curvature θ)

/-- The universal certified drop `A ^ 2 / (4 * C)`: the value of
`η * A - η ^ 2 * C` at the safe step. -/
noncomputable def universalDrop (U : UniversalSafeStep Θ)
    (θ : Θ) : ℝ :=
  (U.alignment θ) ^ 2 / (4 * U.curvature θ)

/-- THE safe step theorem, once for the whole CE family: at positive
curvature, the step `A / (2 * C)` decreases the loss by at least
`A ^ 2 / (4 * C)`.  The three per-tranche re-proofs of this
quadratic minimization become one-line instances below. -/
theorem universal_descent (U : UniversalSafeStep Θ) (θ : Θ)
    (hC : 0 < U.curvature θ) :
    U.loss (U.step θ (universalStepSize U θ))
      ≤ U.loss θ - universalDrop U θ := by
  have hη : 0 ≤ universalStepSize U θ :=
    div_nonneg (U.alignment_nonneg θ) (by positivity)
  have h := U.majorizes θ (universalStepSize U θ) hη
  have key : universalStepSize U θ * U.alignment θ
      - (universalStepSize U θ) ^ 2 * U.curvature θ
      = universalDrop U θ := by
    simp only [universalStepSize, universalDrop]
    field_simp
    ring
  linarith [h, key]

/-- The certified drop is monotone under one-sided bounds: if the
true alignment is at least `Al > 0` and the true curvature at most
`Cu > 0`, the drop is at least `Al ^ 2 / (4 * Cu)`. -/
theorem universalDrop_ge_of_bounds (U : UniversalSafeStep Θ) (θ : Θ)
    {Al Cu : ℝ} (hCpos : 0 < U.curvature θ)
    (hAl : Al ≤ U.alignment θ) (hCu : U.curvature θ ≤ Cu)
    (hAlpos : 0 < Al) (hCupos : 0 < Cu) :
    Al ^ 2 / (4 * Cu) ≤ universalDrop U θ := by
  have hA : 0 < U.alignment θ := lt_of_lt_of_le hAlpos hAl
  have hsq : Al ^ 2 ≤ (U.alignment θ) ^ 2 := by nlinarith
  simp only [universalDrop]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * Cu)
    (by positivity : (0:ℝ) < 4 * U.curvature θ)]
  nlinarith

/-- The accept-form of the universal step (audit 5.2 algebra, the
C388 target shape): with an alignment estimate `Â` carrying
nonnegative uncertainty `r` and a curvature estimate `Ĉ` carrying
uncertainty `u`, the accept condition `0 < Â - r ∧ 0 < Ĉ + u`
certifies, from the universal form alone, the drop lower bound
`(Â - r) ^ 2 / (4 * (Ĉ + u))`.  No probability here — the
Freedman-radius theorem is C388. -/
theorem universal_accept_form (U : UniversalSafeStep Θ) (θ : Θ)
    {Â Ĉ r u : ℝ} (hCpos : 0 < U.curvature θ)
    (hA : Â - r ≤ U.alignment θ) (hC : U.curvature θ ≤ Ĉ + u) :
    0 < Â - r → 0 < Ĉ + u →
      U.loss (U.step θ (universalStepSize U θ))
        ≤ U.loss θ - (Â - r) ^ 2 / (4 * (Ĉ + u)) := by
  intro h1 h2
  have hd := universalDrop_ge_of_bounds U θ hCpos hA hC h1 h2
  have hd2 := universal_descent U θ hCpos
  linarith

/-! ## Stage 2/3 — the single-sample specialization (CEDescent) -/

variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- The single-sample CE model as a `UniversalSafeStep`: carrier
`Model.CEDescent`, curvature `(ceStepRange) ^ 2 / 8`.  The
`majorizes` field is the η-generic majorizer
`ceOneHot_next_le_majorizer` — the safe-step conclusion is derived,
not imported. -/
noncomputable def singleSampleStep (X : Matrix V (Fin d) ℝ) (t : V) :
    UniversalSafeStep (EuclideanSpace ℝ (Fin d)) where
  loss θ := Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
  step θ η := Hagi.Model.ceNextParameters X θ t η
  alignment θ := Hagi.Model.ceAlignment X θ t
  curvature θ := (Hagi.Model.ceStepRange X θ t) ^ 2 / 8
  alignment_nonneg θ := Hagi.Model.ceAlignment_nonneg X θ t
  curvature_nonneg θ := by positivity
  majorizes θ η hη := by
    have h := Hagi.Model.ceOneHot_next_le_majorizer X θ t hη
    calc Hagi.ceOneHot t (Hagi.Model.ceLogits X
          (Hagi.Model.ceNextParameters X θ t η))
        ≤ Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
            - η * Hagi.Model.ceAlignment X θ t
            + (η * Hagi.Model.ceStepRange X θ t) ^ 2 / 8 :=
          by simpa only [Hagi.Model.ceNextLogits,
            Hagi.Model.ceMajorizer] using h
      _ = Hagi.ceOneHot t (Hagi.Model.ceLogits X θ)
            - η * Hagi.Model.ceAlignment X θ t
            + η ^ 2 * ((Hagi.Model.ceStepRange X θ t) ^ 2 / 8) := by
            ring

/-- A/C identification, single-sample: the universal step size IS
the `Model.CEDescent` line-form safe step `4 * A / R ^ 2`. -/
theorem singleSample_stepSize_ident (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hR : Hagi.Model.ceStepRange X θ t ≠ 0) :
    universalStepSize (singleSampleStep X t) θ
      = Hagi.Model.safeStepSize X θ t := by
  simp only [universalStepSize, singleSampleStep,
    Hagi.Model.safeStepSize, hR, ↓reduceIte]
  field_simp
  ring_nf

/-- A/C identification, single-sample: the universal drop IS the
`Model.CEDescent` guaranteed decrease `2 * A ^ 2 / R ^ 2`. -/
theorem singleSample_drop_ident (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hR : Hagi.Model.ceStepRange X θ t ≠ 0) :
    universalDrop (singleSampleStep X t) θ
      = 2 * (Hagi.Model.ceAlignment X θ t) ^ 2
        / (Hagi.Model.ceStepRange X θ t) ^ 2 := by
  simp only [universalDrop, singleSampleStep]
  field_simp
  ring_nf

/-- Specialization 1 (one line): the single-sample safe-step descent
of `Model.CEDescent` is an instance of `universal_descent`. -/
theorem singleSample_descent (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d))
    (hC : 0 < (singleSampleStep X t).curvature θ) :
    (singleSampleStep X t).loss
        ((singleSampleStep X t).step θ
          (universalStepSize (singleSampleStep X t) θ))
      ≤ (singleSampleStep X t).loss θ
        - universalDrop (singleSampleStep X t) θ :=
  universal_descent _ θ hC

/-! ## Stage 3 — the batch specialization (BatchCEDescentSafeStep) -/

/-- The arithmetic-mean batch CE model as a `UniversalSafeStep`:
carrier `Model.BatchCEDescentSafeStep`, curvature
`batchRangeSquare / 8` — the SAME construction as the single-sample
one, on the averaged majorizer. -/
noncomputable def batchStep {B : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (y : Fin B → V) :
    UniversalSafeStep (EuclideanSpace ℝ (Fin d)) where
  loss θ := Hagi.Model.BatchCEDescent.batchLoss X θ y
  step θ η :=
    Hagi.Model.BatchCEDescent.alongNext θ
      (Hagi.Model.BatchCEDescent.batchMeanDirection X θ y) η
  alignment θ := Hagi.Model.BatchCEDescent.batchAlignment X θ y
  curvature θ := Hagi.Model.BatchCEDescent.batchRangeSquare X θ y / 8
  alignment_nonneg θ :=
    Hagi.Model.BatchCEDescent.batchAlignment_nonneg X θ y
  curvature_nonneg θ := by
    exact div_nonneg
      (Hagi.Model.BatchCEDescent.batchRangeSquare_nonneg X θ y)
      (by positivity)
  majorizes θ η hη := by
    have h :=
      Hagi.Model.BatchCEDescent.batchLoss_alongNext_le_batchMajorizer
        X θ y hη
    calc Hagi.Model.BatchCEDescent.batchLoss X
          (Hagi.Model.BatchCEDescent.alongNext θ
            (Hagi.Model.BatchCEDescent.batchMeanDirection X θ y) η) y
        ≤ Hagi.Model.BatchCEDescent.batchLoss X θ y
            - η * Hagi.Model.BatchCEDescent.batchAlignment X θ y
            + η ^ 2 * Hagi.Model.BatchCEDescent.batchRangeSquare X θ y
              / 8 := h
      _ = Hagi.Model.BatchCEDescent.batchLoss X θ y
            - η * Hagi.Model.BatchCEDescent.batchAlignment X θ y
            + η ^ 2 * (Hagi.Model.BatchCEDescent.batchRangeSquare
                X θ y / 8) := by ring

/-- A/C identification, batch: the universal step size IS the batch
safe step `4 * Ā / R̄ ^ 2`. -/
theorem batch_stepSize_ident {B : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hR : Hagi.Model.BatchCEDescent.batchRangeSquare X θ y ≠ 0) :
    universalStepSize (batchStep X y) θ
      = Hagi.Model.BatchCEDescent.batchSafeStep X θ y := by
  simp only [universalStepSize, batchStep,
    Hagi.Model.BatchCEDescent.batchSafeStep, hR, ↓reduceIte]
  field_simp
  ring_nf

/-- Specialization 2 (one line): the batch safe-step descent of
`Model.BatchCEDescentSafeStep` is an instance of
`universal_descent`. -/
theorem batch_descent {B : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (y : Fin B → V) (θ : EuclideanSpace ℝ (Fin d))
    (hC : 0 < (batchStep X y).curvature θ) :
    (batchStep X y).loss
        ((batchStep X y).step θ (universalStepSize (batchStep X y) θ))
      ≤ (batchStep X y).loss θ - universalDrop (batchStep X y) θ :=
  universal_descent _ θ hC

/-! ## Stage 2 — the gated specialization (GatedCESafeStep) -/

/-- The gated CE model as a `UniversalSafeStep`: carrier
`Model.GatedCEDescent`/`Model.GatedCESafeStep`, curvature
`gatedCurvature` — the `taylor`-majorant branch of the family; its
`η = A / 2C` rule is the universal form verbatim. -/
noncomputable def gatedStep (X : Matrix V (Fin d) ℝ) (t : V) :
    UniversalSafeStep (EuclideanSpace ℝ (Fin d)) where
  loss θ := Hagi.ceOneHot t (Hagi.Model.GatedCEGradient.gatedForward X θ)
  step θ η := Hagi.Model.GatedCEDescent.gatedNextParameters X θ t η
  alignment θ := Hagi.Model.GatedCEDescent.gatedAlignment X θ t
  curvature θ := Hagi.Model.GatedCESafeStep.gatedCurvature X θ t
  alignment_nonneg θ :=
    Hagi.Model.GatedCEDescent.gatedAlignment_nonneg X θ t
  curvature_nonneg θ :=
    Hagi.Model.GatedCESafeStep.gatedCurvature_nonneg X θ t
  majorizes θ _η hη :=
    Hagi.Model.GatedCESafeStep.gated_ceOneHot_le_majorizer X θ t hη

/-- A/C identification, gated: the universal step size IS the gated
safe step `A / (2 * C)` (positive-curvature branch). -/
theorem gated_stepSize_ident (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : Hagi.Model.GatedCESafeStep.gatedCurvature X θ t ≠ 0) :
    universalStepSize (gatedStep X t) θ
      = Hagi.Model.GatedCESafeStep.gatedSafeStepSize X θ t := by
  simp only [universalStepSize, gatedStep,
    Hagi.Model.GatedCESafeStep.gatedSafeStepSize, hC, ↓reduceIte]

/-- Specialization 3 (one line): the gated safe-step descent of
`Model.GatedCESafeStep` is an instance of `universal_descent`
(positive-curvature branch; the zero-curvature unit fallback stays
pinned in the source module). -/
theorem gated_descent (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d))
    (hC : 0 < (gatedStep X t).curvature θ) :
    (gatedStep X t).loss
        ((gatedStep X t).step θ
          (universalStepSize (gatedStep X t) θ))
      ≤ (gatedStep X t).loss θ
        - universalDrop (gatedStep X t) θ :=
  universal_descent _ θ hC

/-! ## Stage 4 — the stochastic pointer (full theorem: C388) -/

/-- Chain pointer to the end-to-end stochastic learning theorem
(C360): whp descent of the real regularized head under fresh-sample
SGD with the Freedman radius.  The accept-form algebra above is its
C387 interface. -/
alias stochasticLearning :=
  Hagi.Unified.StochasticCELearning.stochastic_ce_loop_whp_pl

/-! ## Stage 5 — the convergence head -/

/-- Chain pointer to the closed PL geometric-rate convergence
theorem for the regularized CE head (C351/C354/C357/C359 chain:
convexity → smoothness → PL → rate, attainment discharged). -/
alias convergenceRegClosed :=
  Hagi.Model.CEGlobalConvergence.ce_global_convergence_reg_closed

/-- Chain pointer to the margin-PL convergence variant (ball-local
PL constant from the margin coefficient and radius). -/
alias convergenceMargin :=
  Hagi.Model.CEMarginPL.ce_global_convergence_margin

end Hagi.Theory.CEChain
