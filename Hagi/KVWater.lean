/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Waterfilling for the KV pyramid

`Hagi.Attention` proved the softmax damping law: a KV error enters
the attention output scaled by its attention mass. The missing
piece — prescribed by the growth program — is the *optimal
allocation* of a fixed precision budget across KV positions: the
waterfilling analogue of `Hagi.ErrorProp` for the attention branch.

**The model.** Each position `i` carries a per-bit error
contribution `c i > 0` (the sensitivity: attention mass times the
value norm, in the linearized regime) and a fixed bit cost; its
residual after `b i` bits decays as `exp (-κ b i)` with a shared
rate `κ > 0` (the exponential regime of quantization SNR:
`error ~ 2^{-b}`, i.e. `κ = log 2`, in the standard model).

**The theorem.** Among all allocations of a fixed budget `B` over
the positions, the total residual `∑ c i * exp (-κ b i)` is
minimized exactly when the *marginal* residuals are equal:
`c i * exp (-κ b* i) = λ` for all `i` — each bit spent buys the
same marginal error reduction everywhere.

Two consequences, stated honestly:

* **The tangent bound** (`waterfilling_bound`): for any feasible
  allocation `b`, the total residual is at least the equalized one
  — the proof is the exponential tangent inequality
  `exp x ≥ 1 + x` applied to the deviations from the optimum.
* **The allocation law** (in the docstring, not a theorem — it
  requires the inverse of `exp`): equalizing gives
  `b* i = (log (c i) - log λ) / κ` — the bits grow *logarithmically*
  in the sensitivity, `b* i - b* j = (log c i - log c j)/κ`. This
  is the honest correction to the naive "bits ∝ p_i·‖v_i‖": the
  *exponent* of the sensitivity drives the allocation, not the
  sensitivity itself. For the code: rank KV positions by
  `log (attention_mass * ‖v‖)`, allocate the budget as a shift of
  that log-ranking (water level λ from the budget constraint), and
  never sweep over allocations — the equalization condition is the
  closed-form optimum.
-/

open Finset

namespace Hagi

section Waterfilling

variable {ι : Type*} [Fintype ι]

/-- The total KV residual of an allocation `b` under per-position
sensitivities `c` and decay rate `κ`. -/
noncomputable def kvResidual (c : ι → ℝ) (kappa : ℝ) (b : ι → ℝ) : ℝ :=
  ∑ i, c i * Real.exp (-kappa * b i)

/-- **The equalization lemma.** If two allocations `b*` (the
candidate optimum) and `b` have the same total budget, and `b*`
equalizes the marginal residuals (`c i * exp (-κ b* i) = λ` for
all i), then the residual of `b` is at least the residual of
`b*`. The proof is the exponential tangent bound
`exp x ≥ 1 + x`: writing `b i = b* i + d i` with `∑ d i = 0`,

`c i * exp (-κ b i) = λ * exp (-κ d i) ≥ λ * (1 - κ d i)`,

and summing kills the linear terms (the budget constraint), giving
`∑ ≥ N * λ = the residual of b*` (each term of which is `λ`). -/
theorem waterfilling_bound (c : ι → ℝ) (kappa : ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (bstar b : ι → ℝ)
    (heq : ∀ i, c i * Real.exp (-kappa * bstar i) = lam)
    (hbudget : ∑ i, b i = ∑ i, bstar i) :
    kvResidual c kappa bstar ≤ kvResidual c kappa b := by
  -- d = b - b*; ∑ d = 0
  set d : ι → ℝ := fun i => b i - bstar i with hd
  have hsumd : ∑ i, d i = 0 := by
    simp only [hd]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero_of_eq hbudget
  -- per-position: c i * exp (-κ b i) ≥ λ * (1 - κ d i)
  have hper : ∀ i, lam * (1 - kappa * d i)
      ≤ c i * Real.exp (-kappa * b i) := by
    intro i
    -- c i * exp (-κ b i) = (c i * exp (-κ b* i)) * exp (-κ d i)
    --                     = λ * exp (-κ d i) ≥ λ * (1 + (-κ d i))
    have hsplit : -kappa * b i = -kappa * bstar i + (-kappa * d i) := by
      simp only [hd]
      ring
    have hterm : c i * Real.exp (-kappa * b i)
        = lam * Real.exp (-kappa * d i) := by
      rw [hsplit, Real.exp_add, ← heq i]
      ring
    have htan : (1:ℝ) + (-kappa * d i) ≤ Real.exp (-kappa * d i) := by
      have := Real.add_one_le_exp (-kappa * d i)
      linarith
    have hstep : lam * (1 + (-kappa * d i))
        ≤ lam * Real.exp (-kappa * d i) :=
      mul_le_mul_of_nonneg_left htan (le_of_lt hlam)
    have hconv : lam * (1 - kappa * d i)
        = lam * (1 + (-kappa * d i)) := by ring
    -- goal: lam * (1 - κ d i) ≤ c i * exp (-κ b i) = [hterm] λ * exp (-κ d i)
    rw [hconv, hterm]
    exact hstep
  -- b* residual = N * λ
  have hstar : kvResidual c kappa bstar = Fintype.card ι * lam := by
    unfold kvResidual
    rw [Finset.sum_congr rfl fun i _ => heq i]
    simp
  -- b residual ≥ ∑ λ (1 - κ d i) = N λ - κ λ ∑ d i = N λ
  unfold kvResidual
  calc ∑ i, c i * Real.exp (-kappa * bstar i)
      = Fintype.card ι * lam := hstar
    _ = ∑ i, lam * (1 - kappa * d i) := by
        have hmul : ∑ i, lam * (1 - kappa * d i)
            = lam * (∑ i, (1 - kappa * d i)) :=
          (Finset.mul_sum Finset.univ (fun i => (1:ℝ) - kappa * d i) lam).symm
        rw [hmul, Finset.sum_sub_distrib]
        have h1 : ∑ i : ι, (1:ℝ) = Fintype.card ι := by simp
        have h2 : ∑ i, kappa * d i = kappa * ∑ i, d i := by
          rw [← Finset.mul_sum]
        rw [h1, h2, hsumd, mul_zero, sub_zero]
        ring
    _ ≤ ∑ i, c i * Real.exp (-kappa * b i) :=
        Finset.sum_le_sum fun i _ => hper i

/-- **The active-set form (round-34 sync with the Python
fix): the allocation law with the positive part.** The
closed-form water level

`b_i* = max(0, (1/κ)·log(c_i/λ))` —

the negative-bit clamp: tensors with c_i ≤ λ (the residual
under the price even at zero budget) are EXCLUDED (b_i* = 0)
and the budget redistributes over the active set
{c_i > λ}. The Lean side previously recorded only the
interior form (c_i·e^{−κb_i*} = λ); the positive part is the
boundary case of the same KKT (the complementarity: the
inactive tensors' marginal at 0 is under the price). The
formal statement: for the inactive tensor (c_i ≤ λ) the
clamped allocation is zero. -/
theorem waterfilling_inactive_clamp (c_i lam kappa : ℝ)
    (hcpos : 0 < c_i) (hlam : 0 < lam) (hkappa : 0 < kappa)
    (hinactive : c_i ≤ lam) :
    max 0 ((1/kappa) * Real.log (c_i / lam)) = 0 := by
  have hratio : c_i / lam ≤ 1 := (div_le_one₀ hlam).mpr hinactive
  -- log(c/λ) ≤ 0 ⟸ c/λ ≤ 1 (log monotone at 1)
  have hlog : Real.log (c_i / lam) ≤ 0 := by
    have h1 : Real.log (c_i / lam) ≤ Real.log 1 :=
      Real.log_le_log (div_pos hcpos hlam) hratio
    rw [Real.log_one] at h1
    exact h1
  -- (1/κ)·log(c/λ) ≤ 0 ⟹ max 0 · = 0
  have hinner : (1/kappa) * Real.log (c_i / lam) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  exact max_eq_left (le_trans hinner (le_refl 0))

end Waterfilling

end Hagi
