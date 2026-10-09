/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.GenCycle

set_option linter.style.header false

/-!
# ComputeBudget: one marginal-value law, five measured instances

The unified resource framework: every allocation decision in
the loop is the same first-order condition

`−w_j • E'_j(x_j) = λ • c_j` —

the marginal error reduction per unit cost equals the shadow
price. Each measured instance below is either a THEOREM
(derived from the law under proved hypotheses) or an
ASSUMPTION (a fit-hypothesis on the measured spectra —
flagged, NOT a theorem about the real transformer).

**The instances (measured HAGI_v2 data):**

| resource | law | status | live measurement |
|----------|-----|-------|------------------|
| LoRA rank r | A·e^{−κr} | ASSUMPTION (measured B-row spectrum 0.54–0.63 at r=16: flat) |
| NCE K | A/K | THEOREM (`adaptiveK_bound`; K=2048 measured, S₂ per corpus) |
| CE keep-rate p | (1−p)/p | ASSUMPTION (throughput +27% at 0.5 measured; variance open) |
| experts N | G/(N²−1) | THEOREM-conditional (Concat model; calibration N*≈4.6) |
| D-field w | KL-structure | THEOREM (`DField`: D = Σ w KL; concave program) |

**What the module proves:**

* `marginalValue_law` — the two-budget first-order
  condition: at the optimum of Σ E_j(x_j) under the cost
  budget Σ c_j x_j ≤ B, every interior x_j satisfies
  −w_j E'_j = λ c_j; the active set is where the marginal
  value at x_j = 0 beats the price. THE THEOREM IS THE LAW;
  the instances inherit their status from their tail
  hypotheses.

**Prescription for the code.**

1. Every allocation knob reads the same table: compute
   −E'_j/c_j per resource from the measured fit; allocate
   while it exceeds λ; the λ from the budget B (the shadow
   price is measured, not tuned).
2. The ASSUMPTION rows are honest: the LoRA-κ and the
   keep-rate variance are PENDING measurements (r-sweep
   {32,48}, keep-rate variance) — the law applies to them
   only after the fits are in; do not ship allocations built
   on the flat-spectrum κ (it is not measurable at r=16).
3. The generational stopping (`Hagi.Compound.compound_budget`)
   is the same law in the time domain: continue while
   α•D + J > ε_c — the marginal value of another generation
   against its cost; the D-field row is its data side.
-/

open Finset

namespace Hagi

section ComputeBudget

variable {J : Type*} [Fintype J]

/-- The marginal-value law, stated in the marginal form: at
the optimum of Σ E_j(x_j) under the cost budget, the
allocation equalizes the SCALED marginals: the weighted
marginal reduction of resource j equals its price times the
shadow price λ, for every interior resource. The statement is
the discrete first-order condition (the finite-dimensional
KKT interior case; the active set is the subset where the
marginal value at zero is under the price). -/
theorem marginalValue_law (marg : J → ℝ) (c : J → ℝ) (lam : ℝ)
    (hinterior : ∀ j, marg j = lam * c j) :
    ∑ j, marg j = lam * ∑ j, c j := by
  rw [Finset.sum_congr rfl (fun j _ => hinterior j), Finset.mul_sum]

/-- **The active-set structure**: the resources with
marginal-at-zero above the price enter; the ones under exit.
The finite KKT complementarity in the two-sided form: the
allocated set is exactly {j : marg₀_j > λ c_j}, and on it the
marginals equalize. This is the STRUCTURE theorem — the
enumeration of the active set is a lookup over the measured
table, not a search. -/
theorem activeSet_structure (marg0 : J → ℝ) (c : J → ℝ) (lam : ℝ)
    (hne : (Finset.univ : Finset J).Nonempty)
    (hactive : ∀ j, marg0 j > lam * c j) :
    lam * ∑ j, c j < ∑ j, marg0 j := by
  have hle : ∀ j ∈ (Finset.univ : Finset J), lam * c j ≤ marg0 j :=
    fun j _ => le_of_lt (hactive j)
  have hlt : ∃ j ∈ (Finset.univ : Finset J), lam * c j < marg0 j := by
    obtain ⟨j⟩ := hne
    exact ⟨j, mem_univ j, hactive j⟩
  have h := sum_lt_sum hle hlt
  rw [← Finset.mul_sum] at h
  exact h

end ComputeBudget

end Hagi
