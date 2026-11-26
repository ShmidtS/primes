/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.ResidualVQ
import Hagi.Cert.StepGen
import Mathlib.Tactic

set_option linter.style.header false

/-!
# RDAlloc: the rate-distortion compression step certificate

The slow-loop RD-compression composition: the
per-stage bit allocation, the staged quantization error law, the
iso-Frobenius sensitivity, and the certified-transition kernel
assembled into ONE step certificate. Every ingredient is cited
from its own carrier; only the COMPOSITION is new:

* the allocation premise-form is BUDGET-SATISFYING (`RDAlloc`);
  the water-filling OPTIMALITY is cited
  (`Hagi.Budget.rankResidual_equalized`,
  `rankResidual_allocation`, and the iso-Frobenius-weighted
  `weightedExpAllocation_isoFrob_optimal` of
  `Hagi.Budget.IsoFrobAlloc`), NOT re-proven;
* the staged error law is cited
  (`Hagi.Budget.residualTwoStage_error_le_add`: two-stage
  residual quantization composes additively, ε₁ + ε₂) and the
  per-stage product law
  (`quantProd_relError_sq`: (e + f + e·f)² cross-term law) — the
  εᵢ recipe for factorized (LoRA-style) stages is that same law
  εᵢ recipe for factorized (LoRA-style) stages;
* the sensitivity scaling is the iso-Frobenius cascade
  calibration (`Hagi.Budget.isoFrobSensitivity`:
  c_j = isoFrobEnergy(J_{>j})·hScale_j) — the Lipschitz premise
  `|phi X − phi Y| ≤ sens·‖X−Y‖_F` of `rd_step_error_bound` is
  its premise-form instantiation at the composed pipeline;
* the certified transition is the kernel
  (`Hagi.Cert.CertStepGen`): `rd_step_certified` packages the
  compression step with byte-budget accounting
  (`budget' = budget − bytes(alloc)`, nonneg) and the quality
  cost `rdAllocError alloc` in the risk channel, remainder free
  (the no-zero-pinning lesson). The descent premise is in
  drop form `obj s' ≤ obj s − drop` — exactly
  LossCeiling polarity
  (`Hagi.Model.EnergyReasoning.MetricDirection.improves_lossCeiling_intro`
  of CramContracts: lower objective is better; docstring wiring,
  no import — layer discipline).

Hadamard-wrapped blocks: the
 spread bound `Hagi.Contracts.hadamard_ternary_error_bound_of_spread`
(ε = n·(s/2)² + ρ·‖x‖², ρ the deterministic energy-spread
premise) is the per-stage constant for blocks quantized through
an orthonormal Hadamard rotation — instantiate `RDAlloc.eps`
there when the stage wraps a Hadamard block; no new theorem is
needed for that wiring.

Honest scope: two-stage composition; no n-stage
law); no n-stage induction; no probability; no empirical
constants in theorem statements.
-/

open Finset Hagi.Core

namespace Hagi.Budget

variable {m r n : Type} [Fintype m] [Fintype r] [Fintype n]
variable {ι : Type*} [Fintype ι]

/-! ## The allocation (premise-form: budget-satisfying) -/

/-- **RDAlloc**: a per-stage bit allocation with per-stage error
constants. PREMISE-FORM: the allocation only SATISFIES the bit
budget (`hbudget`); water-filling optimality is cited
(`rankResidual_equalized` / `rankResidual_allocation`), not re-proven here.
not re-proven here. The per-stage `eps i` is the error constant
εᵢ(bᵢ) of stage i at the allocated width (
  hadamard_ternary_error_bound_of_spread` bound is the recipe for
  Hadamard-wrapped stages; `Hagi.Budget.quantProd_relError_sq` is the
  recipe for factorized stages). -/
structure RDAlloc (ι : Type*) [Fintype ι] where
  /-- Per-stage bit widths bᵢ. -/
  bits : ι → ℝ
  hbits : ∀ i, 0 ≤ bits i
  /-- Per-stage error constants εᵢ(bᵢ). -/
  eps : ι → ℝ
  heps : ∀ i, 0 ≤ eps i
  /-- The total bit budget. -/
  bitBudget : ℝ
  hbudget : ∑ i, bits i ≤ bitBudget

/-- The byte cost of the allocation: ∑ bᵢ/8. -/
noncomputable def rdAllocBytes (alloc : RDAlloc ι) : ℝ := ∑ i, alloc.bits i / 8

theorem rdAllocBytes_nonneg (alloc : RDAlloc ι) : 0 ≤ rdAllocBytes alloc :=
  sum_nonneg fun i _ => div_nonneg (alloc.hbits i) (by norm_num)

/-- The total quality cost of the allocation: ∑ εᵢ. -/
def rdAllocError (alloc : RDAlloc ι) : ℝ := ∑ i, alloc.eps i

theorem rdAllocError_nonneg (alloc : RDAlloc ι) : 0 ≤ rdAllocError alloc :=
  sum_nonneg fun i _ => alloc.heps i

/-! ## The staged error law (exact composition) -/

/-- Squares kill the sign: frobSq(−X) = frobSq X (glue, needed to
match the sensitivity premise direction). -/
theorem frobSq_neg (X : Matrix m n ℝ) : frobSq (-X) = frobSq X := by
  unfold frobSq
  simp [Matrix.neg_apply]

/-- **MAIN — the composed slow-loop compression error**: the
two-stage residual pipeline Ŵ = R1 + R2 with the additive
error law (ε₁ as the sign premise, ε₂ bounding the second
residual — exactly `residualTwoStage_error_le_add`'s hypotheses)
read out through a sensitivity-`sens` function `phi`
(premise-form iso-Frobenius sensitivity, the readout is
Lipschitz in the Frobenius metric) has function-level perturbation
bounded by `sens · (ε₁ + ε₂)` — weight error to function error
through the sensitivity, weight error composed by the staged
additive law. -/
theorem rd_step_error_bound (W R1 R2 : Matrix m n ℝ) (e1 e2 : ℝ)
    (he1 : 0 ≤ e1)
    (h2 : (frobSq ((W - R1) - R2)).sqrt ≤ e2)
    (phi : Matrix m n ℝ → ℝ) (sens : ℝ)
    (hsens : 0 ≤ sens)
    (hlip : ∀ X Y : Matrix m n ℝ,
      |phi X - phi Y| ≤ sens * (frobSq (X - Y)).sqrt) :
    |phi (R1 + R2) - phi W| ≤ sens * (e1 + e2) := by
  have hlip2 := hlip (R1 + R2) W
  have hconv : frobSq (R1 + R2 - W) = frobSq (W - (R1 + R2)) := by
    have hneg : W - (R1 + R2) = -(R1 + R2 - W) := by
      funext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply]; ring
    rw [hneg, frobSq_neg]
  rw [hconv] at hlip2
  have hadd := residualTwoStage_error_le_add W R1 R2 e1 e2 he1 h2
  calc |phi (R1 + R2) - phi W|
      ≤ sens * (frobSq (W - (R1 + R2))).sqrt := hlip2
    _ ≤ sens * (e1 + e2) := mul_le_mul_of_nonneg_left hadd hsens

/-- Numeric 2-stage anchor: ε₁ = 1/10, ε₂ = 1/20, sensitivity
sens = 2 ⟹ the function-level error bound is the arithmetic
2 · (1/10 + 1/20) = 3/10 — the main theorem instantiated, not a
bare computation. -/
theorem rd_step_anchor (W R1 R2 : Matrix m n ℝ)
    (h2 : (frobSq ((W - R1) - R2)).sqrt ≤ 1 / 20)
    (phi : Matrix m n ℝ → ℝ)
    (hlip : ∀ X Y : Matrix m n ℝ,
      |phi X - phi Y| ≤ 2 * (frobSq (X - Y)).sqrt) :
    |phi (R1 + R2) - phi W| ≤ 3 / 10 := by
  have h := rd_step_error_bound W R1 R2 (1 / 10) (1 / 20)
    (by norm_num) h2 phi 2 (by norm_num) hlip
  linarith

/-! ## The certified transition (kernel packaging) -/

/-- **The compression step IS a certified transition**: the
RD-compression step packaged as a `Hagi.Cert.CertStepGen`
(premise-form `StepCertificate.toCertStepGen` pattern):
byte-budget accounting `budget' = budget − bytes(alloc)` with the
nonnegative remainder as premises, the quality cost
`rdAllocError alloc` carried in the RISK channel (the error
budget) with a FREE remainder (the no-zero-pinning lesson),
the false-commit delta channel in premise form, and the descent in
drop form `obj s' ≤ obj s − drop` — exactly the LossCeiling
polarity (`MetricDirection.improves_lossCeiling_intro`: lower
objective is better). -/
noncomputable def rd_step_certified {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (alloc : RDAlloc ι) (s s' : S)
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - rdAllocBytes alloc)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = rdAllocError alloc + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl deltaLevel s s' where
  drop := drop
  drop_pos := hdrop
  descent := hdesc
  budgetSpend := rdAllocBytes alloc
  budget_next := hbud
  budget_nonneg := hbudnn
  riskSpend := rdAllocError alloc
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := delta
  delta_next := hdelta
  delta_nonneg := hdeltaNN
  floorsKept := hfloors

/-- The byte accounting is the allocation's byte cost. -/
theorem rd_step_certified_budgetSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (alloc : RDAlloc ι) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - rdAllocBytes alloc)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = rdAllocError alloc + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (rd_step_certified M obl deltaLevel alloc s s' drop hdrop hdesc
      hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).budgetSpend = rdAllocBytes alloc := rfl

/-- The risk-channel spend is the allocation's total quality
cost ∑ εᵢ. -/
theorem rd_step_certified_errorSpend {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ)
    (alloc : RDAlloc ι) {s s' : S}
    (drop : ℝ) (hdrop : 0 < drop)
    (hdesc : M.objective s' ≤ M.objective s - drop)
    (hbud : M.budget s' = M.budget s - rdAllocBytes alloc)
    (hbudnn : 0 ≤ M.budget s')
    (riskRem : ℝ)
    (hrisk : M.risk s = rdAllocError alloc + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (delta : ℝ)
    (hdelta : deltaLevel s' = deltaLevel s - delta)
    (hdeltaNN : 0 ≤ deltaLevel s')
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    (rd_step_certified M obl deltaLevel alloc s s' drop hdrop hdesc
      hbud hbudnn riskRem hrisk hrisk' hrem delta hdelta hdeltaNN
      hfloors).riskSpend = rdAllocError alloc := rfl

end Hagi.Budget
