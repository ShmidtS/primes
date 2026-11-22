/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Step.Muon
import Hagi.Step.SafeQPStep
import Hagi.Step.SignSGD
/-!
# The direction-provider contract (audit 4.2)

Optimizers in this layer certify different properties of the
DIRECTION they propose.  Survey (`.tmp/C366/survey.md`): the
genuinely common shape is not a solver but three certificate
predicates over a state→direction map — descent alignment, a norm
bound, and feasibility — with each optimizer honestly claiming a
subset.  `DirectionProvider` is the CEModel pattern applied to
directions: ONE data field (`dir`), no fake-true proof fields; the
proof obligations live in `DirectionCertificate.*` hypothesis-form
definitions, and each bridge below is a theorem that an existing
SSOT definition satisfies the certificates it can honestly claim.

## SafeQP numerical specification (KKT residuals)

The frozen `safeqp_trust_region` takes the per-domain margin
`−ε ≤ ⟪g, d⟫` as an ABSTRACT hypothesis.  This module replaces
"assume the margin" with a CHECKABLE numerical certificate of the
solver output: for the trust-region QP (minimize `½‖d‖² + ⟪g,d⟫`
subject to `‖d‖² ≤ Δ`, multiplier `λ ≥ 0`) the three KKT residuals

* `kktStationarity g d λ = ‖g + λ • d‖`,
* `kktComplementarity d λ Δ = |λ · (‖d‖² − Δ)|`,
* `kktPrimalResidual d Δ = max 0 (‖d‖² − Δ)|

are explicit ℝ-valued functions of the OUTPUT pair `(d, λ)`; any
procedure producing small residuals passes the theorems below.
At `ε = 0` the descent bound degenerates to the exact statement
`⟪g, d⟫ ≤ −λΔ ≤ 0`, so the residual analysis is not vacuous.

`Classical.choice` status: nothing here introduces or removes a
choice operator.  The frozen SafeQP lemmas never used one; the
`Classical.choice` occurrences elsewhere in the repo
(`Cert.StepGen` per-index program choice,
`Contracts.TruncatedSVDTail` witness index) remain where existence
is genuinely needed — documented, untouched.

## Honest ledger (bridged vs not)

Bridged (delegation theorems, existing SSOT lemmas named):

1. negated gradient — `negGradient_isDescent` (exact descent);
2. Muon (C297 spectral bridge) — `muonProvider_hasNormBound`,
   delegating to `muon_step_bound` under the contraction
   hypothesis `∀ z, ‖P z‖ ≤ ‖z‖` (Muon certifies the norm bound,
   NOT descent — honestly only that);
3. SignSGD — `signProvider_isDescent`, delegating to
   `sign_inner_nonneg` on the carrier `EuclideanSpace ℝ k`;
4. SafeQP/KKT — `kkt_descent_bound` (⟹ `isEpsDescent`),
   `kkt_margin_bound` and `kkt_radius_bound` feeding
   `safeqp_kkt_trust_region`, which delegates to the frozen
   `safeqp_trust_region` with the residual-derived margin
   `ΛΔ + ε(1 + ‖d‖)`.

Not bridged (tranches, with reasons):

- `Model.CEModel` / `Model.CEDescent` family: certifies the STEP
  (`safeStep_descent` on the loss), not a direction map; its
  alignment field `A(θ)` is a scalar norm square with no gradient
  field exposed.  A bridge needs a new residual-gradient
  definition — new math, not a delegation.
- MinNorm/MGDA: no such module exists in the repo; the
  multi-objective role is already carried by the per-domain
  margins of the SafeQP family.  Nothing to bridge.
- Newton–Schulz iterations: certify scalar spectral dynamics,
  not a state→direction contract.

Step sizes (`safeqpEtaMax`, the C364 `CEModel` safe step) are the
step-side SSOT; this contract deliberately covers only the
direction side (KISS: unify the certificate shape, not the
solvers).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Step

open Real InnerProductSpace

variable {S : Type} {D : Type} [NormedAddCommGroup D]

/-! ## The contract -/

/-- The direction-provider contract: a state-indexed direction map.
Data only — proof obligations live in `DirectionCertificate.*`
predicates, so no optimizer is forced into fake-true fields. -/
structure DirectionProvider (S D : Type) [NormedAddCommGroup D] where
  /-- The direction the optimizer proposes at a state. -/
  dir : S → D

/- Certificate predicates for a direction provider: each optimizer
claims the subset it can honestly prove. -/
namespace DirectionCertificate

variable [InnerProductSpace ℝ D]

/-- Exact descent certificate: the direction never positively
aligns with the gradient field. -/
def isDescent (grad : S → D) (p : DirectionProvider S D) : Prop :=
  ∀ s, ⟪grad s, p.dir s⟫_ℝ ≤ 0

/-- Approximate descent certificate: the alignment is bounded by
`tol s · (1 + ‖p.dir s‖)` — the KKT-residual form (exact descent is
the `tol = 0` instance). -/
def isEpsDescent (grad : S → D) (tol : S → ℝ)
    (p : DirectionProvider S D) : Prop :=
  ∀ s, ⟪grad s, p.dir s⟫_ℝ ≤ tol s * (1 + ‖p.dir s‖)

/-- Norm-bound certificate: the direction norm is bounded by the
state-indexed bound. -/
def hasNormBound (bound : S → ℝ) (p : DirectionProvider S D) : Prop :=
  ∀ s, ‖p.dir s‖ ≤ bound s

/-- Feasibility certificate: the direction satisfies the
state-indexed feasibility predicate. -/
def isFeasible (feas : S → D → Prop) (p : DirectionProvider S D) :
    Prop := ∀ s, feas s (p.dir s)

end DirectionCertificate

open DirectionCertificate

/-! ## Bridge 1: negated gradient -/

variable [InnerProductSpace ℝ D]

/-- The gradient-descent direction provider: `dir s = −grad s`. -/
def negGradientProvider (grad : S → D) : DirectionProvider S D where
  dir s := -grad s

/-- The negated gradient is an exact descent direction:
`⟪g, −g⟫ = −‖g‖² ≤ 0`. -/
theorem negGradient_isDescent (grad : S → D) :
    isDescent grad (negGradientProvider (S := S) grad) := by
  intro s
  simp only [negGradientProvider, inner_neg_right,
    real_inner_self_eq_norm_sq]
  linarith [sq_nonneg (‖grad s‖)]

/-! ## Bridge 2: Muon (C297 spectral bridge) -/

variable {W : Type} [NormedAddCommGroup W]

/-- The Muon direction provider: `dir g = muonDir P g = P g`
(preconditioned gradient; the state IS the gradient/parameter
vector). -/
def muonProvider (P : W → W) : DirectionProvider W W where
  dir g := muonDir P g

/-- Muon certifies the NORM BOUND (not descent): under the
contraction `∀ z, ‖P z‖ ≤ ‖z‖`, `‖muonDir P g‖ ≤ ‖g‖` —
delegates to `muon_step_bound` (C297). -/
theorem muonProvider_hasNormBound (P : W → W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    hasNormBound (fun g => ‖g‖) (muonProvider P) := fun _ =>
  muon_step_bound P _ hP

/-! ## Bridge 3: SignSGD -/

variable {k : Type} [Fintype k]

/-- The sign direction provider on `EuclideanSpace ℝ k`:
`dir g = −sign g` (descent sign step; the compressed gradient is
negated to point downhill). -/
noncomputable def signProvider : DirectionProvider (EuclideanSpace ℝ k) (EuclideanSpace ℝ k) where
  dir g := -(WithLp.equiv 2 (k → ℝ)).symm
    (fun i => SignSGD.sgn1 ((WithLp.equiv 2 (k → ℝ)) g i))

/-- The sign direction is an exact descent direction:
`⟪g, −sign g⟫ = −Σ |gᵢ| ≤ 0` — delegates to `sign_inner_nonneg`
(the sign compression never flips the descent side). -/
theorem signProvider_isDescent (g : EuclideanSpace ℝ k) :
    ⟪g, (signProvider (k := k)).dir g⟫_ℝ ≤ 0 := by
  have hsplit : ⟪g, (signProvider (k := k)).dir g⟫_ℝ
      = -∑ i, SignSGD.sgn1 ((WithLp.equiv 2 (k → ℝ)) g i)
          * ((WithLp.equiv 2 (k → ℝ)) g i) := by
    simp only [signProvider, inner_neg_right, PiLp.inner_apply]
    simp
  obtain ⟨_, hnn⟩ := SignSGD.sign_inner_nonneg
    (fun i => (WithLp.equiv 2 (k → ℝ)) g i)
  rw [hsplit]
  linarith

/-- Contract form of the sign bridge: `signProvider` is an exact
descent provider for the identity gradient field. -/
theorem signProvider_isDescent' :
    isDescent (id : EuclideanSpace ℝ k → EuclideanSpace ℝ k)
      (signProvider (k := k)) :=
  fun g => signProvider_isDescent g

/-! ## Bridge 4: SafeQP — the KKT numerical specification -/

section KKT

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- KKT stationarity residual of the solver output `(d, λ)` for the
trust-region QP: `‖g + λ • d‖`. -/
noncomputable def kktStationarity (g d : E) (lam : ℝ) : ℝ :=
  ‖g + lam • d‖

/-- KKT complementarity residual: `|λ · (‖d‖² − Δ)|`. -/
noncomputable def kktComplementarity (d : E) (lam delta : ℝ) : ℝ :=
  |lam * (‖d‖ ^ 2 - delta)|

/-- KKT primal-feasibility violation: `max 0 (‖d‖² − Δ)`. -/
noncomputable def kktPrimalResidual (d : E) (delta : ℝ) : ℝ :=
  max 0 (‖d‖ ^ 2 - delta)

/-- Numerical descent bound: small stationarity and complementarity
residuals certify the anti-alignment `⟪g, d⟫ ≤ ε (1 + ‖d‖)`.  At
`ε = 0` this is the exact statement `⟪g, d⟫ ≤ −λΔ ≤ 0`. -/
theorem kkt_descent_bound (g d : E) (lam delta eps : ℝ)
    (_hlam : 0 ≤ lam) (hdelta : 0 ≤ delta)
    (hstat : kktStationarity g d lam ≤ eps)
    (hcomp : kktComplementarity d lam delta ≤ eps) :
    ⟪g, d⟫_ℝ ≤ eps * (‖d‖ + 1) := by
  have hcs : |⟪g + lam • d, d⟫_ℝ| ≤ ‖g + lam • d‖ * ‖d‖ :=
    abs_real_inner_le_norm (g + lam • d) d
  have hsplit : ⟪g + lam • d, d⟫_ℝ = ⟪g, d⟫_ℝ + lam * ‖d‖ ^ 2 := by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have h1 : ⟪g, d⟫_ℝ + lam * ‖d‖ ^ 2 ≤ ‖g + lam • d‖ * ‖d‖ := by
    rw [← hsplit]
    have hboth := abs_le.mp hcs
    linarith [hboth.2]
  have h4 : ‖g + lam • d‖ * ‖d‖ ≤ eps * ‖d‖ :=
    mul_le_mul_of_nonneg_right hstat (norm_nonneg _)
  have hneg : -eps ≤ lam * (‖d‖ ^ 2 - delta) := neg_le_of_abs_le hcomp
  have hlamdelta : 0 ≤ lam * delta := mul_nonneg _hlam hdelta
  have hsplit2 : lam * ‖d‖ ^ 2
      = lam * (‖d‖ ^ 2 - delta) + lam * delta := by ring
  calc ⟪g, d⟫_ℝ
      = ⟪g, d⟫_ℝ + lam * ‖d‖ ^ 2 - lam * ‖d‖ ^ 2 := by ring
    _ ≤ ‖g + lam • d‖ * ‖d‖ - lam * ‖d‖ ^ 2 := by linarith
    _ ≤ eps * ‖d‖ - lam * ‖d‖ ^ 2 := by linarith
    _ = eps * ‖d‖ - lam * (‖d‖ ^ 2 - delta) - lam * delta := by ring
    _ ≤ eps * ‖d‖ + eps - lam * delta := by linarith
    _ ≤ eps * ‖d‖ + eps := by linarith
    _ = eps * (‖d‖ + 1) := by ring

/-- Numerical margin bound: additionally bounding the multiplier
`λ ≤ Λ`, small stationarity and complementarity residuals certify
the lower margin `−(ε (1 + ‖d‖) + ΛΔ) ≤ ⟪g, d⟫` — exactly the
`hfeas` shape of the frozen `safeqp_trust_region`. -/
theorem kkt_margin_bound (g d : E) (lam Lam delta eps : ℝ)
    (_hlam : 0 ≤ lam) (hlamL : lam ≤ Lam) (hdelta : 0 ≤ delta)
    (hstat : kktStationarity g d lam ≤ eps)
    (hcomp : kktComplementarity d lam delta ≤ eps) :
    -(eps * (‖d‖ + 1) + Lam * delta) ≤ ⟪g, d⟫_ℝ := by
  have hcs : |⟪g + lam • d, d⟫_ℝ| ≤ ‖g + lam • d‖ * ‖d‖ :=
    abs_real_inner_le_norm (g + lam • d) d
  have hsplit : ⟪g + lam • d, d⟫_ℝ = ⟪g, d⟫_ℝ + lam * ‖d‖ ^ 2 := by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have hboth := abs_le.mp hcs
  have h4 : ‖g + lam • d‖ * ‖d‖ ≤ eps * ‖d‖ :=
    mul_le_mul_of_nonneg_right hstat (norm_nonneg _)
  have hpos : lam * (‖d‖ ^ 2 - delta) ≤ eps :=
    le_trans (le_abs_self _) hcomp
  have hbnd : lam * ‖d‖ ^ 2 ≤ eps + Lam * delta := by
    have hmono : lam * delta ≤ Lam * delta :=
      mul_le_mul_of_nonneg_right hlamL hdelta
    have hsplit2 : lam * ‖d‖ ^ 2
        = lam * (‖d‖ ^ 2 - delta) + lam * delta := by ring
    linarith
  have hstep1 : ⟪g, d⟫_ℝ ≥ -(eps * ‖d‖) - lam * ‖d‖ ^ 2 := by
    have h5 : -(‖g + lam • d‖ * ‖d‖) ≥ -(eps * ‖d‖) := by
      have hn := neg_le_neg h4
      linarith
    linarith
  linarith

omit [InnerProductSpace ℝ E] in
/-- Numerical radius bound: a small primal-feasibility violation
certifies the trust radius `‖d‖² ≤ Δ + ε` — the `hrad` input of the
frozen `safeqp_trust_region` up to the budget arithmetic. -/
theorem kkt_radius_bound (d : E) (delta eps : ℝ)
    (hprim : kktPrimalResidual d delta ≤ eps) :
    ‖d‖ ^ 2 ≤ delta + eps := by
  simp only [kktPrimalResidual] at hprim
  obtain ⟨_, h⟩ := max_le_iff.mp hprim
  linarith

/-- The SafeQP bridge: a solver output `(d, λ)` with KKT residuals
at most `ε`, multiplier bounded by `Λ`, and trust radius `Δ` set so
that the certified radius fits the margin budget, satisfies the
frozen `safeqp_trust_region` certificate with the residual-derived
margin `ΛΔ + ε (1 + ‖d‖)`.  This replaces the abstract margin
hypothesis by a check on the numerical output — no choice operator
involved. -/
theorem safeqp_kkt_trust_region (g d : E) (lam Lam delta eps L dL : ℝ)
    (hL : 0 < L)
    (hlam : 0 ≤ lam) (hlamL : lam ≤ Lam) (hdelta : 0 ≤ delta)
    (hstat : kktStationarity g d lam ≤ eps)
    (hcomp : kktComplementarity d lam delta ≤ eps)
    (hprim : kktPrimalResidual d delta ≤ eps)
    (h_emp_smooth : dL ≤ -⟪g, d⟫_ℝ + L * ‖d‖ ^ 2 / 2)
    (hradbudget : delta + eps
      ≤ 2 * (Lam * delta + eps + eps * ‖d‖) / L) :
    dL ≤ 2 * (Lam * delta + eps + eps * ‖d‖) := by
  have hfeas : -(Lam * delta + eps + eps * ‖d‖) ≤ ⟪g, d⟫_ℝ := by
    have := kkt_margin_bound g d lam Lam delta eps hlam hlamL hdelta
      hstat hcomp
    linarith
  have hrad : ‖d‖ ^ 2
      ≤ 2 * (Lam * delta + eps + eps * ‖d‖) / L := by
    have hr := kkt_radius_bound d delta eps hprim
    linarith
  exact safeqp_trust_region ⟪g, d⟫_ℝ
    (Lam * delta + eps + eps * ‖d‖) L ‖d‖ dL hfeas hL h_emp_smooth hrad

end KKT

end Hagi.Step
