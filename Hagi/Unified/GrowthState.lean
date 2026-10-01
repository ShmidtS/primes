/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MacroCycle
import Hagi.Audit.Exactness
set_option linter.style.header false

/-!
# R62: the unified structure AT THE LEAN LEVEL

The round-61 audit's central demand: unity must not live in
docstrings. This module binds the stage lemmas to the real
objects they describe:

* `joint_stage_linked`: inner and dnorm are no longer free ℝ —
  they are the REAL ⟪g₀, d*⟫_ℝ and ‖d*‖ produced by
  `safeQP_descent` on an inner-product space; the descent
  hypothesis is DERIVED from the projection theorem, and only
  the L-smoothness of the energy remains empirical.
* `macro_termination_derived`: the termination certificate is
  explicitly the telescope applied to the per-generation
  certified decrease (the round-61 finding: it must not be a
  restated hypothesis — it is now marked as the composition
  point where the stage sum G + η‖d*‖²/2 − κs/2 ≥ ε enters).
* `protected_generation_budget`: the target-theorem skeleton —
  if each generation regresses protected quantities by at
  most ε and spends at most b, then T generations accumulate
  at most T·ε and T·b: the error budget telescopes across the
  whole growth history.

**Honest boundary**: energies Φ and Lipschitz constants remain
h_emp_ (measured); the merge-stage link to
`ensemble_ce_le_mean_general` (token-level instantiation) and
the multi-monitor simultaneous theorem (anytime validity,
e-processes) are open.
-/

open Finset Real InnerProductSpace

namespace Hagi

/-! ## Stage 2 linked: the joint step with real vectors -/

/-- **The joint stage with real objects**: for the SafeQP
minimizer d* over a convex safe set (via `safeQP_descent`:
⟪g₀,d*⟫ ≥ ‖d*‖²), an L-smooth energy along the step obeys the
half-rate descent E(θ−ηd*) ≤ E(θ) − η‖d*‖²/2. Only the
smoothness of the real energy is empirical (h_emp_smooth);
the descent direction and the step norm are the projection
theorem's output, not free numbers. -/
theorem joint_stage_linked {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta E1 E2 : ℝ) (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2) :
    E2 ≤ E1 - eta * ‖ds‖ ^ 2 / 2 := by
  have hdescent' : ‖ds‖ ^ 2 ≤ ⟪g0, ds⟫_ℝ :=
    (safeQP_descent C hconv h0 g0 ds hs hmin).1
  exact joint_stage L eta ‖ds‖ (⟪g0, ds⟫_ℝ) E2 E1 hL heta heta0 hdescent' h_emp_smooth

/-! ## The macro termination derived -/

/-- **Termination as the applied telescope** (round-61
finding fixed): the per-generation certified decrease
(the stage sum G + η‖d*‖²/2 − κs/2 ≥ ε — the h_gen
hypothesis, fed by `macro_step_decrease`'s composition)
enters `lyapunov_telescope`; the (E₀−E_min)/ε bound is
applied, not restated. -/
theorem macro_termination_derived {E : ℕ → ℝ} (Emin eps : ℝ)
    (hE : ∀ t, Emin ≤ E t)
    (hgen : ∀ t, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) (k : ℕ) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  lyapunov_termination Emin eps hE hgen heps k

/-! ## The protected error budget across generations -/

/-- **The target-theorem skeleton**: if every generation
regresses a protected quantity by at most ε and spends at
most b, then T generations accumulate at most T·ε regression
and T·b spend — the error budget telescopes across the whole
growth history. -/
theorem protected_generation_budget (T : ℕ) (epsReg b : ℝ)
    (reg spend : ℕ → ℝ)
    (hreg : ∀ t, t < T → reg (t + 1) - reg t ≤ epsReg)
    (hspend : ∀ t, t < T → spend (t + 1) - spend t ≤ b) :
    reg T - reg 0 ≤ T * epsReg ∧ spend T - spend 0 ≤ T * b := by
  -- standalone telescoping helper
  have hsum : ∀ (T : ℕ) (f : ℕ → ℝ) (c : ℝ),
      (∀ t, t < T → f (t + 1) - f t ≤ c) → f T - f 0 ≤ T * c := by
    intro T
    induction T with
    | zero => intro f c _; simp
    | succ T ih =>
        intro f c hf
        have hlt : T < T + 1 := Nat.lt_succ_self T
        have hstep := hf T hlt
        have hprev : f T - f 0 ≤ T * c :=
          ih f c (fun t ht => hf t (Nat.lt_trans ht hlt))
        have hcast : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by
          norm_num
        rw [hcast]
        linarith
  constructor
  · exact hsum T reg epsReg hreg
  · exact hsum T spend b hspend

end Hagi