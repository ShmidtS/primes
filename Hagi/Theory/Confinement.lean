/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEMarginPL
import Hagi.Model.CEGlobalConvergence
import Hagi.Theory.CEChain

/-!
# Confinement for safe-step dynamics (A18.5)

Audit A18.5: a safe step that (weakly) decreases the loss keeps the
whole trajectory inside the start sublevel set; if that sublevel set
is bounded (coercivity), the trajectory is CONFINED to a ball — and
on a ball the margin-PL inequality (`Hagi.Model.CEMarginPL.margin_pl_ball`,
μ = `muBall a B = a²·e^{−a·B}/8`) applies at every iterate, turning
the ball-scoped PL into a global-on-the-sublevel PL regime with the
geometric rate `(1 − μ/L)^T`.

## The two halves assembled here

* MONOTONICITY (`sublevel_confinement`, `universal_safeStep_confinement`,
  `plStep_nonincreasing`): any dynamics with `f (s θ) ≤ f θ` stays in
  `{x | f x ≤ f θ₀}` — a one-induction fact. For the CE chain the
  monotone map is the universal safe step (`Theory.CEChain.safeStepMap`,
  drop `A²/4C ≥ 0` from `universal_descent`); for gradient steps it is
  the smoothness-only descent lemma.
* COERCIVITY (`ceReg_sublevel_bounded`, `ceReg_safe_step_confinement`):
  boundedness of the sublevel set. For the ridge objective `ceReg`
  (λ > 0) this is DERIVED from `ceReg_coerce` (C359) with the explicit
  radius `√(2·ceReg θ₀/λ)`; for a general objective it is a premise.

## The rate theorem

`safe_step_margin_pl_rate` is `Hagi.Model.CEMarginPL.margin_pl_convergence`
with its confinement premise h_conf DISCHARGED: the iterates of a
smooth gradient step stay in the θ₀-sublevel (monotonicity), the
sublevel lies in the ball `‖x‖ ≤ B` (coercivity premise `h_bounded`),
so the ball-scoped PL applies at every iterate and the geometric rate
follows.

## Honest pins (what genuinely remains a premise)

- UNREGULARIZED CE sublevel sets are UNBOUNDED (logit shift): for the
  strictly decreasing `scalarCE a` the sublevel of `θ₀` is the ray
  `[θ₀, ∞)`, and the plStep increments `(2/a)·ρ` are positive, so the
  trajectory drifts to +∞ while the loss → 0. Ball confinement is
  FALSE there, not merely unproven; the unregularized margin rate
  keeps its ball premise (`ce_global_convergence_margin` stays SSOT).
  A scalar instantiation of `h_bounded` for `scalarCE` would be
  unsatisfiable (vacuous) — deliberately not stated.
- The PL constant is ball-scoped (`muBall a B`, decreasing in `a·B`);
  the margin condition is a data-dependent premise, not derived.
- Strictly-decreasing safe steps need `A > 0` (C387 majorizer);
  confinement only uses the weak inequality (sublevels are `≤`-sets).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.Confinement

/-! ## Monotone dynamics stay in the start sublevel -/

/-- The confinement induction: if every step weakly decreases the
loss, then every iterate stays in the sublevel set of the start
point.  This is the whole mechanism of A18.5 — everything else is
obtaining the monotonicity and bounding the sublevel. -/
theorem sublevel_confinement {Θ : Type} (s : Θ → Θ) (f : Θ → ℝ)
    (hmono : ∀ θ, f (s θ) ≤ f θ) (θ₀ : Θ) (t : ℕ) :
    f (s^[t] θ₀) ≤ f θ₀ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hmono _) ih

/-- With the sublevel set `{x | f x ≤ f θ₀}` contained in a ball
(the coercivity premise, with the center absorbed into `f`/the norm
shift), the monotone trajectory is CONFINED to that ball. -/
theorem ball_confinement_of_sublevel {E : Type} [NormedAddCommGroup E]
    (s : E → E) (f : E → ℝ) (hmono : ∀ θ, f (s θ) ≤ f θ)
    (θ₀ : E) (R' : ℝ) (t : ℕ)
    (h_bounded : ∀ x : E, f x ≤ f θ₀ → ‖x‖ ≤ R') :
    ‖s^[t] θ₀‖ ≤ R' :=
  h_bounded _ (sublevel_confinement s f hmono θ₀ t)

/-! ## The CE-chain universal safe step is monotone -/

/-- The safe-step map of a `UniversalSafeStep`: each point moves to
its safe-step update `U.step θ (universalStepSize U θ)`. -/
noncomputable def safeStepMap {Θ : Type} (U : Theory.CEChain.UniversalSafeStep Θ) :
    Θ → Θ :=
  fun θ => U.step θ (Theory.CEChain.universalStepSize U θ)

/-- Monotonicity of the universal safe step at one point (the
`universal_descent` inequality with `universalDrop ≥ 0`). -/
private theorem universal_safeStep_mono {Θ : Type}
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ : Θ) :
    U.loss (safeStepMap U θ) ≤ U.loss θ := by
  have hd := Theory.CEChain.universal_descent U θ (hC θ)
  have hdnn : (0:ℝ) ≤ Theory.CEChain.universalDrop U θ := by
    rw [Theory.CEChain.universalDrop]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (by norm_num : (0:ℝ) < 4) (hC θ)))
  unfold safeStepMap
  linarith

/-- At positive curvature the universal safe step weakly decreases
the loss (`universal_descent` with `universalDrop ≥ 0`), so the CE
chain (single-sample / batch / gated instances of
`Theory.CEChain.UniversalSafeStep`) is a monotone dynamics and its
trajectories stay in the start sublevel set. -/
theorem universal_safeStep_confinement {Θ : Type}
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ₀ : Θ) (t : ℕ) :
    U.loss ((safeStepMap U)^[t] θ₀) ≤ U.loss θ₀ :=
  sublevel_confinement (safeStepMap U) U.loss
    (universal_safeStep_mono U hC) θ₀ t

/-- Ball version: the CE-chain safe-step trajectory is confined once
the start sublevel set is bounded (coercivity premise).  For the
ridge CE this premise is DERIVED (`ceReg_safe_step_confinement`). -/
theorem universal_safeStep_ball_confinement {Θ : Type} [NormedAddCommGroup Θ]
    (U : Theory.CEChain.UniversalSafeStep Θ)
    (hC : ∀ θ : Θ, 0 < U.curvature θ) (θ₀ : Θ) (R' : ℝ) (t : ℕ)
    (h_bounded : ∀ x : Θ, U.loss x ≤ U.loss θ₀ → ‖x‖ ≤ R') :
    ‖(safeStepMap U)^[t] θ₀‖ ≤ R' :=
  ball_confinement_of_sublevel (safeStepMap U) U.loss
    (universal_safeStep_mono U hC) θ₀ R' t h_bounded

/-! ## The gradient step is monotone (smoothness alone) -/

open scoped InnerProductSpace in
/-- Descent lemma, no PL needed: for an `L`-smooth objective (in
inner-product form) the gradient step `plStep` weakly decreases the
loss.  This is the monotonicity key that discharges the confinement
premise of `margin_pl_convergence` below; the proof core is the
smoothness half of `Hagi.Model.CEMarginPL.pl_descent_step_at`. -/
theorem plStep_nonincreasing {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L : ℝ) (θ : E) (hL : 0 < L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2) :
    f (Model.CEGlobalConvergence.plStep grad L θ) ≤ f θ := by
  rw [Model.CEGlobalConvergence.plStep]
  have hstep := h_smooth θ (θ - (1 / L) • grad θ)
  have hin : ⟪grad θ, θ - (1 / L) • grad θ - θ⟫_ℝ
      = -(1 / L) * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hin] at hstep
  have hcoef : L / 2 * ((1 / L) ^ 2 * ‖grad θ‖ ^ 2)
      = ‖grad θ‖ ^ 2 / (2 * L) := by field_simp
  have hnorm : ‖θ - (1 / L) • grad θ - θ‖ ^ 2
      = (1 / L) ^ 2 * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    ring
  rw [hnorm, hcoef] at hstep
  have hXY : f θ + -(1 / L) * ‖grad θ‖ ^ 2 + ‖grad θ‖ ^ 2 / (2 * L)
      = f θ - ‖grad θ‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hXY] at hstep
  have hpos : (0:ℝ) ≤ ‖grad θ‖ ^ 2 / (2 * L) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-! ## The rate theorem: confinement discharges the ball premise -/

open scoped InnerProductSpace in
/-- THE A18.5 RATE THEOREM.  `margin_pl_convergence` with its
confinement premise h_conf REPLACED by a derivation: the gradient
step is monotone by smoothness alone (`plStep_nonincreasing`), the
monotone trajectory stays in the θ₀-sublevel (`sublevel_confinement`),
and the coercivity premise `h_bounded` (the sublevel set of `θ₀` lies
in the ball `‖x‖ ≤ B`, on which PL holds) confines every iterate to
the ball — so the ball-scoped PL applies along the whole trajectory
and the loss gap contracts geometrically at rate `1 − μ/L`.

Pins: `h_bounded` is DERIVED for coercive objectives (the ridge CE,
`ceReg_safe_step_confinement` below, radius `√(2·ceReg θ₀/λ)`) and is
a data-dependent premise for the unregularized CE, whose sublevel
sets are unbounded (logit shift — see the module docstring). -/
theorem safe_step_margin_pl_rate {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L μ fstar B : ℝ) (hL : 0 < L) (hμL : μ ≤ L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (h_pl_ball : ∀ x : E, ‖x‖ ≤ B → 2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2)
    (θ₀ : E) (T : ℕ)
    (h_bounded : ∀ x : E, f x ≤ f θ₀ → ‖x‖ ≤ B) :
    f ((Model.CEGlobalConvergence.plStep grad L)^[T] θ₀) - fstar
      ≤ (1 - μ / L) ^ T * (f θ₀ - fstar) := by
  have hmono : ∀ θ, f (Model.CEGlobalConvergence.plStep grad L θ) ≤ f θ :=
    fun θ => plStep_nonincreasing f grad L θ hL h_smooth
  exact Model.CEMarginPL.margin_pl_convergence f grad L μ fstar B hL hμL
    h_smooth h_floor h_pl_ball θ₀ T
    (fun t _ => ball_confinement_of_sublevel _ f hmono θ₀ B t h_bounded)

/-! ## The ridge case: coercivity derived (C359) -/

variable {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}

/-- The sublevel-boundedness theorem for the ridge objective, derived
from coercivity (`ceReg_coerce`, C359): `ceReg ≥ (λ/2)‖θ‖²`, so any
sub-`c` point has `‖θ‖ ≤ √(2·c/λ)`.  The standalone extraction of the
bound that `ceReg_attains` uses internally, here consumed for
confinement instead of attainment. -/
theorem ceReg_sublevel_bounded (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 < lam) (θ : EuclideanSpace ℝ (Fin d)) {c : ℝ}
    (hle : Model.CEGlobalConvergence.ceReg X t lam θ ≤ c) :
    ‖θ‖ ≤ Real.sqrt (2 * c / lam) := by
  have h := Model.CEGlobalConvergence.ceReg_coerce X t lam hlam.le θ
  have hnn : (0:ℝ) ≤ lam / 2 * ‖θ‖ ^ 2 :=
    mul_nonneg (div_nonneg hlam.le (by norm_num)) (by positivity)
  have hc : (0:ℝ) ≤ c := by linarith [h.trans hle, hnn]
  refine (Real.le_sqrt (norm_nonneg θ)
    (div_nonneg (by linarith) hlam.le)).2 ?_
  rw [le_div_iff₀ hlam, mul_comm]
  have h5 := h.trans hle
  have heq : lam * ‖θ‖ ^ 2 = 2 * (lam / 2 * ‖θ‖ ^ 2) := by ring
  linarith

/-- DERIVED CONFINEMENT for the ridge case: any safe-step dynamics on
the ridge CE (λ > 0) — in particular every `UniversalSafeStep`
instance of `Theory.CEChain` whose loss is `ceReg` — is confined to
the ball of radius `√(2·ceReg θ₀/λ)`, with no confinement premise.
This is the nonvacuity witness for the `h_bounded` premise class of
`safe_step_margin_pl_rate`. -/
theorem ceReg_safe_step_confinement (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ)
    (hlam : 0 < lam) (s : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hmono : ∀ θ, Model.CEGlobalConvergence.ceReg X t lam (s θ)
      ≤ Model.CEGlobalConvergence.ceReg X t lam θ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (τ : ℕ) :
    ‖s^[τ] θ₀‖ ≤
      Real.sqrt (2 * Model.CEGlobalConvergence.ceReg X t lam θ₀ / lam) :=
  ball_confinement_of_sublevel s (Model.CEGlobalConvergence.ceReg X t lam)
    hmono θ₀ _ τ
    (fun x hx => ceReg_sublevel_bounded X t lam hlam x hx)

end Hagi.Theory.Confinement
