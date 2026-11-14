/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore
import Hagi.Energy.PairwiseCategorical
import Hagi.Energy.EnergyCoordinateStep

set_option linter.style.header false

/-!
# Continuous CRAM flow: algebraic Lyapunov identity, supplied-trajectory form

Track E2 (addendum A9 + A9-supplement, CRAM / arXiv:2611.17309): the
continuous part, split per the supplement into (1) algebraic identities and
(2) a SUPPLIED-TRAJECTORY monotonicity theorem — deliberately avoiding any
ODE-existence API.

Algebraic layer:

* `quadraticVar` — the variance form `uᵀ(diag p − ppᵀ)u = Σ p u² − (Σ p u)²`
  of the logsumexp Hessian quadratic form (NO heavy Hessian machinery).
* `quadraticVar_eq` — `= Σ p (u − Σ p u)²` (variance identity).
* `quadraticVar_nonneg` — `≥ 0` for probability vectors (PSD).
* `quadraticVar_const` — constant `u` is the null direction (`H1 = 0`,
  the gauge note: the per-cell gauge constant is invisible to the flow).
* `softmax_legendre_identity` — `vᵀp − β⁻¹ log Σ e^{βv} = β⁻¹ Σ p log p`.
* `logsumexp_grad_along_dir` — gradient of logsumexp IS `p`: the
  directional derivative of `β⁻¹ log Σ e^{β(v + s·u)}` at `s = 0` is
  `Σ softDef(βv)·u`.
* `soft_curve_deriv` — `ṗ_a = β·p_a·(u'_a − Σ p_b u'_b)` along a
  differentiable curve (softmax pushforward of the velocity).

Trajectory layer:

* `localMeanField` — the belief-space field `B_i(a) +
  Σ_{j≠i} Σ_b K_ij(a,b)·p_j(b)`.
* `cram_energy_hasDerivAt` — (E2c MAIN) SUPPLIED-TRAJECTORY derivative:
  for fixed `β > 0`, `τ > 0`, symmetric `K`, and a differentiable curve
  `v(t)` whose velocity `u(t)` satisfies the CRAM ODE
  `u = −(1/τ)·(v + localMeanField p)` pointwise (`p = softDef(βv)` per
  cell), the free energy `E(s) = meanFieldFreeEnergy β B K (softDef(βv(s)))`
  has derivative `−τβ·Σ_i Var_{p_i}(u_i)` at `t`.
* `cram_continuous_energy_nonincreasing` — corollary: that derivative is
  `≤ 0`. The name claims NONINCREASE along the SUPPLIED trajectory only —
  no convergence, no attractivity, no ODE existence.

## Honest boundaries

The premises are explicit and minimal: fixed `θ` (B, K), fixed clamps
(absent here — no clamped cells), fixed `β > 0`, `τ > 0`, symmetric `K`
(the CRAM `W = sym(K)`), componentwise differentiability at the point,
and the pointwise ODE relation. Discrete Euler steps of this flow are NOT
covered (the paper's own caveat) — the safe discrete certificate is
`Hagi.Energy.coordinate_kl_identity`. The gauge null direction
(`quadraticVar_const`) is why per-cell log-partition constants cancel in
the proof (the shadow of `GaugeQuotient`, E4+ scope).
-/

namespace Hagi.Energy

open Hagi.Prelude (softDef softDef_pos softDef_sum_one)

section Algebraic

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Variance form of the logsumexp Hessian quadratic form:
`uᵀ(diag p − ppᵀ)u = Σ p u² − (Σ p u)²`. -/
def quadraticVar (p u : α → ℝ) : ℝ :=
  (∑ a, p a * u a * u a) - (∑ a, p a * u a) ^ 2

omit [Nonempty α] in
/-- Variance identity: the quadratic form is the Σ of squared deviations
from the `p`-mean. -/
theorem quadraticVar_eq (p u : α → ℝ) (hsum : ∑ a, p a = 1) :
    quadraticVar p u = ∑ a, p a * (u a - ∑ b, p b * u b) ^ 2 := by
  have key : ∀ a, p a * (u a - ∑ b, p b * u b) ^ 2
      = p a * u a * u a - (2 * (p a * u a)) * (∑ b, p b * u b)
        + p a * ((∑ b, p b * u b) * (∑ b, p b * u b)) := fun a => by ring
  have e2 : (∑ a, (2 * (p a * u a)) * (∑ b, p b * u b))
      = 2 * (∑ a, p a * u a) * (∑ b, p b * u b) := by
    rw [sum_mul_right_eq]
    congr 1
    rw [Finset.mul_sum]
  have e3 : (∑ a, p a * ((∑ b, p b * u b) * (∑ b, p b * u b)))
      = (∑ a, p a * u a) * (∑ b, p b * u b) := by
    rw [sum_mul_right_eq, hsum, one_mul]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, e2, e3]
  unfold quadraticVar
  ring

omit [Nonempty α] in
omit [Nonempty α] in
/-- PSD in variance form: nonnegative for probability vectors. -/
theorem quadraticVar_nonneg (p u : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : 0 ≤ quadraticVar p u := by
  rw [quadraticVar_eq p u hsum]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (sq_nonneg _)

omit [Nonempty α] in
omit [Nonempty α] in
/-- Gauge: constant direction is the null direction (`H1 = 0`). -/
theorem quadraticVar_const (p : α → ℝ) (hsum : ∑ a, p a = 1) (c : ℝ) :
    quadraticVar p (fun _ => c) = 0 := by
  rw [quadraticVar]
  have h1 : (∑ a, p a * c * c) = c * c := by
    rw [sum_mul_right_eq, sum_mul_right_eq, hsum, one_mul]
  have h2 : (∑ a, p a * c) = c := by
    rw [sum_mul_right_eq, hsum, one_mul]
  rw [h1, h2]
  ring

/-- Softmax Legendre identity:
`vᵀp − β⁻¹ log Σ e^{βv} = β⁻¹ Σ p log p` with `p = softDef(βv)`
(the duality gap of the entropy-regularized linear problem). -/
theorem softmax_legendre_identity (β : ℝ) (hβ : β ≠ 0) (v : α → ℝ) :
    (∑ a, softDef (fun b => β * v b) a * v a)
      - (1 / β) * Real.log (∑ a, Real.exp (β * v a))
      = (1 / β) * (∑ a, softDef (fun b => β * v b) a
          * Real.log (softDef (fun b => β * v b) a)) := by
  have hlog : ∀ a, Real.log (softDef (fun b => β * v b) a) = β * v a
      - Real.log (∑ b, Real.exp (β * v b)) :=
    fun a => log_softDef (fun b => β * v b) a
  have hsum : ∑ a, softDef (fun b => β * v b) a = 1 := softDef_sum_one _
  have hterm : ∀ a, softDef (fun b => β * v b) a
      * Real.log (softDef (fun b => β * v b) a)
      = softDef (fun b => β * v b) a * v a * β
          - softDef (fun b => β * v b) a
            * Real.log (∑ b, Real.exp (β * v b)) := by
    intro a; rw [hlog a]; ring
  conv_rhs => rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_sub_distrib]
  have hL : (∑ a, softDef (fun b => β * v b) a
      * Real.log (∑ b, Real.exp (β * v b)))
      = Real.log (∑ b, Real.exp (β * v b)) := by
    rw [sum_mul_right_eq, hsum, one_mul]
  rw [hL, sum_mul_right_eq]
  field_simp

/-- Gradient of logsumexp IS `p` (directional form): the derivative of
`s ↦ β⁻¹·log Σ exp(β·(v + s·u))` at `s = 0` is `Σ softDef(βv)·u`. -/
theorem logsumexp_grad_along_dir (β : ℝ) (hβ : β ≠ 0) (v u : α → ℝ) :
    HasDerivAt (fun s : ℝ => (1 / β) * Real.log (∑ a, Real.exp (β * (v a + s * u a))))
      (∑ a, softDef (fun b => β * v b) a * u a) 0 := by
  have hstep : ∀ a : α, HasDerivAt (fun s : ℝ => β * (v a + s * u a)) (β * u a) 0 := by
    intro a
    exact (((hasDerivAt_id 0).mul_const (u a)).const_add (v a)).const_mul β
      |>.congr_deriv (by ring)
  have hdN : HasDerivAt (fun s : ℝ => ∑ a, Real.exp (β * (v a + s * u a)))
      (∑ a, Real.exp (β * v a) * (β * u a)) 0 :=
    HasDerivAt.fun_sum fun a _ =>
      ((hstep a).exp).congr_deriv (by rw [zero_mul, add_zero])
  have hZpos : 0 < ∑ a, Real.exp (β * v a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ0 : (∑ a, Real.exp (β * (v a + 0 * u a))) = (∑ a, Real.exp (β * v a)) := by
    simp only [zero_mul, add_zero]
  refine (((hdN.log (by
      simp only [zero_mul, add_zero]
      exact ne_of_gt hZpos)).const_mul (1 / β)).congr_deriv ?_)
  have hR : (∑ a, softDef (fun b => β * v b) a * u a)
      = (∑ a, Real.exp (β * v a) * u a) / (∑ a, Real.exp (β * v a)) := by
    rw [Finset.sum_congr rfl (fun a _ => by
      rw [softDef, div_mul_eq_mul_div]), Finset.sum_div]
  show (1 / β) * ((∑ a, Real.exp (β * v a) * (β * u a))
      / (∑ a, Real.exp (β * (v a + 0 * u a))))
      = (∑ a, softDef (fun b => β * v b) a * u a)
  rw [hZ0, show (∑ a, Real.exp (β * v a) * (β * u a))
      = β * (∑ a, Real.exp (β * v a) * u a) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring, hR]
  field_simp

/-- Softmax pushforward of the velocity:
`ṗ_a = β·p_a·(u'_a − Σ_b p_b·u'_b)` along a differentiable curve. -/
theorem soft_curve_deriv (β : ℝ) (w : ℝ → α → ℝ) (w' : ℝ → α → ℝ) (t : ℝ)
    (hw : ∀ a, HasDerivAt (w · a) (w' t a) t) (a : α) :
    HasDerivAt (fun s => softDef (fun b => β * w s b) a)
      (β * (softDef (fun b => β * w t b) a
        * (w' t a - ∑ b, softDef (fun c => β * w t c) b * w' t b))) t := by
  have hdN : HasDerivAt (fun s => ∑ b, Real.exp (β * w s b))
      (∑ b, Real.exp (β * w t b) * (β * w' t b)) t :=
    HasDerivAt.fun_sum fun b _ => ((hw b).const_mul β).exp
  have hZpos : 0 < ∑ b, Real.exp (β * w t b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ : (∑ b, Real.exp (β * w t b)) ≠ 0 := ne_of_gt hZpos
  have hde : HasDerivAt (fun s => Real.exp (β * w s a))
      (Real.exp (β * w t a) * (β * w' t a)) t := ((hw a).const_mul β).exp
  have hsd : (∑ b, softDef (fun c => β * w t c) b * w' t b)
      = (∑ b, Real.exp (β * w t b) * w' t b)
        / (∑ b, Real.exp (β * w t b)) := by
    rw [Finset.sum_congr rfl (fun b _ => by
      rw [softDef, div_mul_eq_mul_div]), Finset.sum_div]
  refine (hde.div hdN hZ).congr_deriv ?_
  rw [hsd, softDef,
    Finset.sum_congr rfl (fun x _ => (by ring :
      Real.exp (β * w t x) * (β * w' t x) = β * (Real.exp (β * w t x) * w' t x))),
    ← Finset.mul_sum Finset.univ (fun x => Real.exp (β * w t x) * w' t x) β]
  field_simp

end Algebraic

section Flow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- Belief-space mean field at cell `i`, value `a`:
`B_i(a) + Σ_{j≠i} Σ_b K_ij(a,b)·p_j(b)`. -/
noncomputable def localMeanField (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (p : ι → (α → ℝ)) (i : ι) (a : α) : ℝ :=
  B i a + ∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * p j b

end Flow

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- Offdiag double-sum commutation (helper for the pairwise-derivative
symmetrization): swapping the two indices of an ordered-pair sum leaves
it invariant. -/
theorem sum_offdiag_comm (f : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ \ {i}, f i j)
      = (∑ i, ∑ j ∈ Finset.univ \ {i}, f j i) := by
  classical
  have e1 : ∀ (g : ι → ℝ) (i : ι),
      (∑ j ∈ Finset.univ \ {i}, g j)
        = (∑ j ∈ Finset.univ, if j = i then (0:ℝ) else g j) := by
    intro g i
    have step1 : (∑ j ∈ Finset.univ \ {i}, g j)
        = (∑ j ∈ Finset.univ \ {i}, if j = i then (0:ℝ) else g j) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        simp [hj.2]
    rw [step1]
    refine Finset.sum_subset (Finset.subset_univ (Finset.univ \ {i})) ?_
    intro x _ hx
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [ite_eq_left (by
      refine Decidable.byContradiction fun hne => hx ?_
      exact ⟨Finset.mem_univ x, hne⟩)]
  rw [Finset.sum_congr rfl fun i _ => e1 (f i) i]
  conv_rhs => rw [Finset.sum_congr rfl fun i _ => e1 (fun j => f j i) i]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Full double-sum index swap (value indices): `∑ a ∑ b, g a b = ∑ a ∑ b, g b a`. -/
theorem sum_swap (g : α → α → ℝ) : (∑ a, ∑ b, g a b) = (∑ a, ∑ b, g b a) := by
  rw [Finset.sum_comm]

omit [DecidableEq α] in
/-- Derivative of `x ↦ x·log x` along a differentiable positive curve. -/
theorem xlog_deriv (x x' : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (x' t) t) (hpos : 0 < x t) :
    HasDerivAt (fun s => x s * Real.log (x s))
      ((Real.log (x t) + 1) * x' t) t := by
  have hl : HasDerivAt (fun s => Real.log (x s)) (x' t / x t) t :=
    hx.log (ne_of_gt hpos)
  refine hx.mul hl |>.congr_deriv ?_
  field_simp

omit [DecidableEq α] in
/-- Sum-of-deviations identity: `∑ p·(u − ∑ p u)·u = quadraticVar p u` for a
probability vector `p` (the per-cell drift/variance bridge). -/
theorem sum_dev_mul (p u : α → ℝ) (hsum : ∑ a, p a = 1) :
    (∑ a, p a * (u a - ∑ b, p b * u b) * u a) = quadraticVar p u := by
  have key : ∀ a, p a * (u a - ∑ b, p b * u b) * u a
      = p a * (u a * u a) - (∑ b, p b * u b) * (p a * u a) := fun a => by ring
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib]
  show (∑ x, p x * (u x * u x)) - ∑ x, (∑ b, p b * u b) * (p x * u x)
      = (∑ a, p a * u a * u a) - (∑ a, p a * u a) ^ 2
  have e : (∑ a, p a * u a) ^ 2
      = ∑ x, (∑ b, p b * u b) * (p x * u x) := by
    rw [pow_two, Finset.mul_sum]
  rw [e]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

/-- (E2c MAIN) SUPPLIED-TRAJECTORY derivative: for fixed `β > 0`, `τ > 0`,
symmetric `K` (the CRAM `W = sym(K)`), and a curve `v` differentiable at `t`
with velocity `u t` satisfying the pointwise CRAM ODE
`u = −(1/τ)·(v + localMeanField p)`, `p = softDef(βv)` per cell, the mean-field
free energy along the trajectory has derivative
`−τβ·∑ᵢ Var_{pᵢ}(uᵢ)`. No ODE existence is claimed: the trajectory and its
velocity are SUPPLIED. -/
theorem cram_energy_hasDerivAt
    (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ)
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (v : ℝ → ι → α → ℝ) (u : ℝ → ι → α → ℝ) (t : ℝ)
    (hv : ∀ i a, HasDerivAt (fun s => v s i a) (u t i a) t)
    (hode : ∀ i a, u t i a = -(1 / τ) * (v t i a
      + localMeanField B K (fun i => softDef (fun a => β * v t i a)) i a)) :
    HasDerivAt (fun s => meanFieldFreeEnergy β B K
        (fun i => softDef (fun a => β * v s i a)))
      (-(τ * β) * ∑ i, quadraticVar (softDef (fun a => β * v t i a))
        (fun a => u t i a)) t := by
  classical
  -- notation
  set P : ℝ → ι → α → ℝ := fun s i => softDef (fun a => β * v s i a) with hP
  set dp : ι → α → ℝ := fun i a => β * (P t i a
    * (u t i a - ∑ b, P t i b * u t i b)) with hdp
  -- softmax belief derivative (per cell)
  have hdP : ∀ i a, HasDerivAt (fun s => P s i a) (dp i a) t := by
    intro i a
    have h := soft_curve_deriv β (fun s => v s i) (fun s => u s i) t
      (fun b => hv i b) a
    rw [hP]
    exact h
  -- entropy part
  have hdEnt : HasDerivAt (fun s => ∑ i, ∑ a, P s i a * Real.log (P s i a))
      (∑ i, ∑ a, (Real.log (P t i a) + 1) * dp i a) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun a _ => ?_
    exact xlog_deriv (fun s => P s i a) (fun _ => dp i a) t (hdP i a)
      (softDef_pos _ a)
  -- unary part
  have hdUn : HasDerivAt (fun s => ∑ i, ∑ a, B i a * P s i a)
      (∑ i, ∑ a, B i a * dp i a) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun a _ => ?_
    exact ((hdP i a).const_mul (B i a)) |>.congr_deriv (by ring)
  -- pairwise part
  have hdPair : HasDerivAt (fun s => ∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
        K i j a b * (P s i a * P s j b))
      (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
        K i j a b * (dp i a * P t j b + P t i a * dp j b)) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum
      (fun j _ => HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_)
    have h1 : HasDerivAt (fun s => P s i a) (dp i a) t := hdP i a
    have h2 : HasDerivAt (fun s => P s j b) (dp j b) t := hdP j b
    exact (h1.mul h2).const_mul (K i j a b) |>.congr_deriv (by ring)
  -- total
  have hTot : HasDerivAt (fun s => meanFieldFreeEnergy β B K
        (fun i => softDef (fun a => β * v s i a)))
      ((1 / β) * (∑ i, ∑ a, (Real.log (P t i a) + 1) * dp i a)
        + (∑ i, ∑ a, B i a * dp i a)
        + (1 / 2) * (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
            K i j a b * (dp i a * P t j b + P t i a * dp j b))) t := by
    have h1 := (hdEnt.const_mul (1 / β)).add hdUn
    have h2 := h1.add (hdPair.const_mul (1 / 2))
    exact h2
  refine hTot.congr_deriv ?_
  -- collapse: D = -τβ · ∑ᵢ Var_{Pᵢ}(uᵢ)
  set Ub : ι → ℝ := fun i => ∑ b, P t i b * u t i b with hUb
  set MFp : ι → α → ℝ := fun i a =>
    ∑ j ∈ Finset.univ \ {i}, ∑ b, K i j a b * P t j b with hMFp
  set ci : ι → ℝ := fun i => 1 / β
    - (1 / β) * Real.log (∑ b, Real.exp (β * v t i b)) with hci
  -- (P1) the transpose half of the pairwise derivative equals the direct half
  have hA2eqA1 : (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
        K i j a b * (P t i a * dp j b))
      = (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
          K i j a b * (dp i a * P t j b)) := by
    rw [sum_offdiag_comm (fun i j => ∑ a, ∑ b,
      K i j a b * (P t i a * dp j b))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sum_swap (fun a b => K j i a b * (P t j a * dp i b))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hK j i b a]
    ring
  -- (P2) the collapsed pairwise derivative is dp · MFp
  have hPairColl : (1 / 2) * (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
        K i j a b * (dp i a * P t j b + P t i a * dp j b))
      = (∑ i, ∑ a, dp i a * MFp i a) := by
    have hsplit : (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
        K i j a b * (dp i a * P t j b + P t i a * dp j b))
      = (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b, K i j a b * (dp i a * P t j b))
        + (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
            K i j a b * (P t i a * dp j b)) := by
      have hd : ∀ (i j a b), K i j a b * (dp i a * P t j b + P t i a * dp j b)
          = K i j a b * (dp i a * P t j b) + K i j a b * (P t i a * dp j b) := by
        intro i j a b; ring
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          hd i j a b]
      simp only [Finset.sum_add_distrib]
    rw [hsplit, hA2eqA1]
    have halve : ∀ x : ℝ, (1 / 2) * (x + x) = x := fun x => by ring
    rw [halve]
    have hre : (∑ i, ∑ j ∈ Finset.univ \ {i}, ∑ a, ∑ b,
          K i j a b * (dp i a * P t j b))
        = (∑ i, ∑ a, dp i a * MFp i a) := by
      rw [hMFp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hc : ∀ j ∈ Finset.univ \ {i},
          (∑ b, K i j a b * (dp i a * P t j b))
            = dp i a * (∑ b, K i j a b * P t j b) := by
        intro j _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.sum_congr rfl (fun j hj => hc j hj), ← Finset.mul_sum]
    rw [hre]
  -- (P3) entropy+gauge: (1/β)·(log P + 1) = v + ci
  have hlog : ∀ i a, (1 / β) * (Real.log (P t i a) + 1)
      = v t i a + ci i := by
    intro i a
    have hz : Real.log (P t i a) = β * v t i a
        - Real.log (∑ b, Real.exp (β * v t i b)) := by
      show Real.log (softDef (fun a => β * v t i a) a) = _
      exact log_softDef (fun a => β * v t i a) a
    rw [hci, hz]
    field_simp
    ring
  -- (P4) total: D = ∑ᵢₐ dp·(v + MF + ci)
  have hD1 : (1 / β) * (∑ i, ∑ a, (Real.log (P t i a) + 1) * dp i a)
      = ∑ i, ∑ a, dp i a * (v t i a + ci i) := by
    have h3 : ∀ i a, (Real.log (P t i a) + 1) = β * (v t i a + ci i) := by
      intro i a
      rw [← hlog i a]
      field_simp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h3 i a]
    field_simp
  -- (P5) ODE: v + MF = -τ·u
  have hODE : ∀ i a, v t i a
      + localMeanField B K (fun i => P t i) i a = -(τ * u t i a) := by
    intro i a
    show v t i a
        + localMeanField B K (fun i => softDef (fun a => β * v t i a)) i a
          = -(τ * u t i a)
    rw [hode i a]
    field_simp
  -- (P6) per-cell mean absorption: ∑ₐ P·(u − Ub) = 0
  have hAbs : ∀ i, (∑ a, P t i a * (u t i a - Ub i)) = 0 := by
    intro i
    have hsum : ∑ a, P t i a = 1 := softDef_sum_one (fun a => β * v t i a)
    rw [hUb]
    have expand : (∑ a, P t i a * (u t i a - ∑ b, P t i b * u t i b))
        = (∑ a, P t i a * u t i a)
          - (∑ b, P t i b * u t i b) * (∑ a, P t i a) := by
      have he : ∀ a, P t i a * (u t i a - ∑ b, P t i b * u t i b)
          = P t i a * u t i a - P t i a * (∑ b, P t i b * u t i b) := fun a => by ring
      rw [Finset.sum_congr rfl (fun a _ => he a), Finset.sum_sub_distrib,
        Finset.mul_sum]
      ring
    rw [expand, hsum, mul_one, sub_self]
  -- (P7) the gauge part vanishes: ∑ᵢₐ dp·ci = 0
  have hGauge : (∑ i, ∑ a, dp i a * ci i) = 0 := by
    have hterm : ∀ i a, dp i a * ci i
        = (P t i a * (u t i a - Ub i)) * (β * ci i) := by
      intro i a
      rw [hdp, hUb]
      ring
    have h1 : (∑ i, ∑ a, dp i a * ci i)
        = (∑ i, ∑ a, (P t i a * (u t i a - Ub i)) * (β * ci i)) := by
      simp only [hterm]
    have h2 : (∑ i, ∑ a, (P t i a * (u t i a - Ub i)) * (β * ci i))
        = (∑ i, β * ci i * (∑ a, P t i a * (u t i a - Ub i))) := by
      simp only [Hagi.Energy.sum_mul_right_eq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2]
    simp only [hAbs, mul_zero, Finset.sum_const_zero]
  -- (P8) the drift part is the variance sum
  have hDrift : (∑ i, ∑ a, dp i a * u t i a)
      = β * (∑ i, quadraticVar (P t i) (fun a => u t i a)) := by
    have hterm : ∀ i a, dp i a * u t i a
        = β * (P t i a * (u t i a - Ub i) * u t i a) := by
      intro i a
      rw [hdp, hUb]
      ring
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      hterm i a]
    have hstep : (∑ i, ∑ a, β * (P t i a * (u t i a - Ub i) * u t i a))
        = β * ∑ i, (∑ a, P t i a * (u t i a - Ub i) * u t i a) := by
      have hg : ∀ i, (∑ a, β * (P t i a * (u t i a - Ub i) * u t i a))
          = β * (∑ a, P t i a * (u t i a - Ub i) * u t i a) := by
        intro i
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl fun i _ => hg i, Finset.mul_sum]
    rw [hstep]
    exact congrArg (fun x => β * x) (Finset.sum_congr rfl fun i _ =>
      sum_dev_mul (P t i) (fun a => u t i a)
        (softDef_sum_one (fun a => β * v t i a)))
  -- (P9) mean-field def: localMeanField = B + MFp
  have hMFdef : ∀ i a, localMeanField B K (fun i => P t i) i a
      = B i a + MFp i a := by
    intro i a
    rw [localMeanField, hMFp]
  -- (P10) assemble
  have hsplit3 : (∑ i, ∑ a, dp i a * (v t i a + ci i))
        + (∑ i, ∑ a, B i a * dp i a)
        + (∑ i, ∑ a, dp i a * MFp i a)
      = ∑ i, ∑ a, dp i a * (v t i a
          + localMeanField B K (fun i => P t i) i a + ci i) := by
    have hterm : ∀ i a, dp i a * (v t i a + ci i) + B i a * dp i a
        + dp i a * MFp i a
        = dp i a * (v t i a
            + localMeanField B K (fun i => P t i) i a + ci i) := by
      intro i a
      rw [hMFdef i a]
      ring
    rw [show (∑ i, ∑ a, dp i a * (v t i a + ci i))
            + (∑ i, ∑ a, B i a * dp i a)
            + (∑ i, ∑ a, dp i a * MFp i a)
        = ∑ i, ∑ a, (dp i a * (v t i a + ci i) + B i a * dp i a
            + dp i a * MFp i a) from by
        simp only [← Finset.sum_add_distrib]]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun a _ => hterm i a
  -- final numeric identity
  have hODErep : (∑ i, ∑ a, dp i a * (v t i a
        + localMeanField B K (fun i => P t i) i a + ci i))
      = -(τ * β) * ∑ i, quadraticVar (P t i) (fun a => u t i a) := by
    have hpre : (∑ i, ∑ a, dp i a * (v t i a
          + localMeanField B K (fun i => P t i) i a + ci i))
        = ∑ i, ∑ a, dp i a * (-(τ * u t i a) + ci i) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      rw [hODE i a]
    have hsplit4 : (∑ i, ∑ a, dp i a * (-(τ * u t i a) + ci i))
      = -(τ * (∑ i, ∑ a, dp i a * u t i a)) + (∑ i, ∑ a, dp i a * ci i) := by
      have hstep1 : (∑ i, ∑ a, dp i a * (-(τ * u t i a) + ci i))
          = (∑ i, ∑ a, dp i a * (-(τ * u t i a))) + (∑ i, ∑ a, dp i a * ci i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hca : ∀ a, dp i a * (-(τ * u t i a) + ci i)
            = dp i a * -(τ * u t i a) + dp i a * ci i := fun a => by ring
        rw [Finset.sum_congr rfl (fun a ha => hca a), Finset.sum_add_distrib]
      have hstep2 : (∑ i, ∑ a, dp i a * (-(τ * u t i a)))
          = -(τ * (∑ i, ∑ a, dp i a * u t i a)) := by
        have hterm : ∀ i, (∑ a, dp i a * (-(τ * u t i a)))
            = -τ * (∑ a, dp i a * u t i a) := by
          intro i
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
        rw [Finset.sum_congr rfl fun i _ => hterm i]
        simp only [Finset.mul_sum]
        simp only [neg_mul, Finset.sum_neg_distrib]
      rw [hstep1, hstep2]
    rw [hpre, hsplit4, hDrift, hGauge]
    ring
  -- final chain
  rw [hD1, hPairColl, hsplit3, hODErep]

/-- Corollary: the energy derivative along a CRAM-ODE-satisfying supplied
trajectory is nonpositive — the Lyapunov identity in nonincrease form
(NOT a convergence claim). -/
theorem cram_continuous_energy_nonincreasing
    (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ)
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a)
    (v : ℝ → ι → α → ℝ) (u : ℝ → ι → α → ℝ) (t : ℝ)
    (hv : ∀ i a, HasDerivAt (fun s => v s i a) (u t i a) t)
    (hode : ∀ i a, u t i a = -(1 / τ) * (v t i a
      + localMeanField B K (fun i => softDef (fun a => β * v t i a)) i a)) :
    HasDerivAt (fun s => meanFieldFreeEnergy β B K
        (fun i => softDef (fun a => β * v s i a)))
      (-(τ * β) * ∑ i, quadraticVar (softDef (fun a => β * v t i a))
        (fun a => u t i a)) t
    ∧ (-(τ * β) * ∑ i, quadraticVar (softDef (fun a => β * v t i a))
        (fun a => u t i a)) ≤ 0 := by
  refine ⟨cram_energy_hasDerivAt β τ hβ hτ B K hK v u t hv hode, ?_⟩
  have hnn : ∀ i, 0 ≤ quadraticVar (softDef (fun a => β * v t i a))
      (fun a => u t i a) :=
    fun i => quadraticVar_nonneg _ _ (fun a => le_of_lt (softDef_pos _ a))
      (softDef_sum_one _)
  have hX : 0 ≤ τ * β * ∑ i, quadraticVar (softDef (fun a => β * v t i a))
      (fun a => u t i a) :=
    mul_nonneg (mul_nonneg (le_of_lt hτ) (le_of_lt hβ))
      (Finset.sum_nonneg fun i _ => hnn i)
  linarith

end Main

end Hagi.Energy

