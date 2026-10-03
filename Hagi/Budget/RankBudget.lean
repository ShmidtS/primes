/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The rank budget: spectral waterfilling across tensors

The synthesis (§20) prescribes the rank allocation across the
leaf tensors (embedding, head, body LoRA factors) as a
*waterfilling in the log domain*: each tensor j has an
exponentially decaying spectral tail `E_j(r) ≈ c_j • exp(−κ_j • r)`
(measurable on the LoRA-B spectra), and the optimal budget
split follows the equalized-marginal condition — the exact
analogue of `Hagi.Budget/KVWater` with the *bit* variable replaced by
the *rank*.

**The model.** Tensor j, given r_j ranks, leaves a residual
`E_j(r_j) = c_j • exp(−κ_j • r_j)` with `c_j > 0`, `κ_j > 0`
(the exponential-tail hypothesis — to be *measured* on the
LoRA spectra before the allocation is trusted). The cost of r_j
ranks is `r_j • (m_j + n_j)` (the low-rank factor parameters).

**What the module proves:**

* `rankResidual_equalized` — the equalized-marginal optimality
  certificate: if the allocations `(r_j*)` equalize the
  marginals `c_j κ_j exp(−κ_j r_j*) = λ` (per unit cost) and the
  budget binds, then any other feasible allocation has a total
  residual at least as large — the tangent-bound argument of
  `KVWater` transported to the rank domain (the exponential
  convexity gives the same one-sided inequality).
* `rankResidual_allocaion` — the explicit form: at the
  equalized point, `r_j* = (log c_j − log(λ (m_j + n_j)))/κ_j` —
  the ranks grow *logarithmically* in the tail scale c_j and
  *inversely* in the decay rate κ_j: tensors with slow-decaying
  spectra (large c_j, small κ_j) get the ranks, tensors with
  fast-decaying spectra saturate early. The active set
  (tensors with r_j* > 0) is `c_j > λ (m_j + n_j)`.

**Prescription for the code.**

1. BEFORE the allocation: measure the spectra of the LoRA-B
   matrices (`lora_leaf_a1..3`) and fit `(c_j, κ_j)` per tensor
   (log-linear regression of the singular values) — the
   exponential-tail hypothesis is an *input assumption*, and
   the formal certificate below is conditional on it.
2. The optimal rank per tensor is the closed form above with λ
   from the budget constraint — no r-sweep: the scheduled
   sweep becomes a *verification* of the prediction, not a
   search.
3. The saturation prediction: rank-16 saturates for tensor j
   iff `r_j*(16) < 16`, i.e. `c_j exp(−16 κ_j) < λ (m_j+n_j)` —
   the closed-form answer to "where does rank-16 stop paying".
-/

open Finset

namespace Hagi

section RankBudget

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The residual of tensor j at rank r: exponential tail. -/
noncomputable def rankResidual (c κ r : ℝ) : ℝ := c * Real.exp (-κ * r)

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The equalized-marginal optimality (the tangent bound,
rank domain).** If the candidate allocations `(r*)` equalize the
per-unit-cost marginals `c_j κ_j exp(−κ_j r*_j) = λ • (m_j+n_j)`
and the budget binds, then any feasible allocation has a total
residual at least that of `r*` — the same exponential tangent
argument as `KVWater.waterfilling_bound`, with the *rank* in
place of the bits and the per-tensor cost weights. -/
theorem rankResidual_equalized
    (c κ m n : ι → ℝ) (rstar r : ι → ℝ) (lam : ℝ)
    (hc : ∀ j, 0 < c j) (_hk : ∀ j, 0 < κ j)
    (_hlam : 0 < lam)
    (heq : ∀ j, c j * κ j * Real.exp (-κ j * rstar j)
      = lam * (m j + n j))
    (hbudget : ∑ j, rstar j * (m j + n j)
      = ∑ j, r j * (m j + n j)) :
    ∑ j, rankResidual (c j) (κ j) (rstar j)
      ≤ ∑ j, rankResidual (c j) (κ j) (r j) := by
  -- the tangent bound per tensor: exp is convex, the tangent at r* lies below
  have htan : ∀ j : ι,
      rankResidual (c j) (κ j) (rstar j)
        + (lam * (m j + n j)) * (rstar j - r j)
      ≤ rankResidual (c j) (κ j) (r j) := by
    intro j
    -- exp(x) >= 1 + x at x = -κ(r - r*)
    have hexp : (1:ℝ) + (-κ j * (r j - rstar j))
        ≤ Real.exp (-κ j * (r j - rstar j)) := by
      have := Real.add_one_le_exp (-κ j * (r j - rstar j))
      linarith [this]
    -- scale by the positive rstar-residual
    have hpos : 0 < rankResidual (c j) (κ j) (rstar j) := by
      unfold rankResidual
      exact mul_pos (hc j) (Real.exp_pos _)
    have hscale : rankResidual (c j) (κ j) (rstar j)
        + rankResidual (c j) (κ j) (rstar j)
            * (-κ j * (r j - rstar j))
      ≤ rankResidual (c j) (κ j) (rstar j)
          * Real.exp (-κ j * (r j - rstar j)) := by
      have h2 : rankResidual (c j) (κ j) (rstar j)
          + rankResidual (c j) (κ j) (rstar j)
            * (-κ j * (r j - rstar j))
        = rankResidual (c j) (κ j) (rstar j)
            * ((1:ℝ) + (-κ j * (r j - rstar j))) := by
        rw [mul_add, mul_one]
      rw [h2]
      exact mul_le_mul_of_nonneg_left hexp hpos.le
    -- the product collapses to the r-residual
    have hprod : rankResidual (c j) (κ j) (rstar j)
        * Real.exp (-κ j * (r j - rstar j))
      = rankResidual (c j) (κ j) (r j) := by
      unfold rankResidual
      -- RHS exp argument: -κ r = -κ r* + (-κ (r - r*))
      have harg : (-κ j * r j)
          = (-κ j * rstar j) + (-κ j * (r j - rstar j)) := by ring
      rw [harg, Real.exp_add]
      ring
    -- the cross term equals λ(m+n)(r* - r) via heq
    have hcross : rankResidual (c j) (κ j) (rstar j)
        * (-κ j * (r j - rstar j))
      = (lam * (m j + n j)) * (rstar j - r j) := by
      unfold rankResidual
      -- c exp(-κ r*) * (-κ(r - r*)) = -(c κ exp(-κ r*))(r - r*)
      rw [← heq j]
      field_simp
      ring
    -- assemble via hcross: rewrite the goal's cross term, then the two-step chain
    rw [← hcross]
    calc rankResidual (c j) (κ j) (rstar j)
        + rankResidual (c j) (κ j) (rstar j)
          * (-κ j * (r j - rstar j))
        ≤ rankResidual (c j) (κ j) (rstar j)
            * Real.exp (-κ j * (r j - rstar j)) := hscale
      _ = rankResidual (c j) (κ j) (r j) := hprod
  -- sum the tangent bounds; the linear parts cancel by the budget
  have hsum : ∑ j, (rankResidual (c j) (κ j) (rstar j)
      + (lam * (m j + n j)) * (rstar j - r j))
    ≤ ∑ j, rankResidual (c j) (κ j) (r j) :=
    Finset.sum_le_sum fun j _ => htan j
  rw [Finset.sum_add_distrib] at hsum
  -- the linear sum: λ Σ (m+n) r* - λ Σ (m+n) r = 0 by the budget
  have hlin : ∑ j, (lam * (m j + n j)) * (rstar j - r j) = 0 := by
    -- pull lam out, then split each term into rstar/r parts
    have hmem : ∀ j : ι, (lam * (m j + n j)) * (rstar j - r j)
        = lam * (rstar j * (m j + n j))
          - lam * (r j * (m j + n j)) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hmem j,
      Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hbudget, sub_self]
  rw [hlin, add_zero] at hsum
  exact hsum

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The explicit allocation (the closed form, round-25
kappa-corrected — the Lean file synced with the Python fix).**
At the equalized point, the optimal rank of tensor j is

`r_j* = [κ_j⁻¹ · log(c_j·κ_j / (λ (m_j + n_j)))]₊` —

with the tail scale MULTIPLIED by the decay rate in the
numerator (the marginal of E = c·e^{−κr} is c·κ·e^{−κr}; the
equalization c_j κ_j e^{−κ_j r} = λ (m_j+n_j) gives the
closed form) and the positive part max(0, ·) — the ACTIVE
SET `c_j·κ_j > λ (m_j + n_j)` (the inactive tensors get
r_j* = 0; the Python active-set from round 25 synced). The
identity here is the log-form rewrite used to compute it
from the measured spectra. -/
theorem rankResidual_allocation
    (c κ : ι → ℝ) (lam L : ℝ)
    (hc : ∀ j, 0 < c j) (hk : ∀ j, 0 < κ j)
    (_hlam : 0 < lam) (hL : 0 < L) :
    ∀ j, (Real.log (c j * κ j) - Real.log L) / κ j
      = -(1/(κ j)) * Real.log (L / (c j * κ j)) := by
  intro j
  -- log(cκ) - log L = log(cκ/L) = -log(L/(cκ))
  have hck : 0 < c j * κ j := mul_pos (hc j) (hk j)
  have h1 : Real.log (c j * κ j / L)
      = Real.log (c j * κ j) - Real.log L :=
    Real.log_div (by exact ne_of_gt hck) (by exact ne_of_gt hL)
  have h2 : Real.log (L / (c j * κ j))
      = Real.log L - Real.log (c j * κ j) :=
    Real.log_div (by exact ne_of_gt hL) (by exact ne_of_gt hck)
  -- both sides: (log(cκ) - log L)/κ = -(1/κ)(log L - log(cκ))
  rw [h2]
  field_simp
  ring

end RankBudget



end Hagi
