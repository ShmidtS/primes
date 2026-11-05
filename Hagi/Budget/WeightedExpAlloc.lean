/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.RankBudget

set_option linter.style.header false

open scoped BigOperators

namespace Hagi.Budget

variable {ι : Type*} [Fintype ι]

/-- Sum of effective resource weights per residual decay coefficient. -/
noncomputable def weightedExpBudget (κ w : ι → ℝ) : ℝ := ∑ i, w i / κ i

/-- Log-affine pressure used by the continuous exponential budget solution. -/
noncomputable def weightedExpLogCoeff (c κ w : ι → ℝ) : ℝ :=
  ∑ i, (w i / κ i) * Real.log (c i * κ i / w i)

/-- Positive Lagrange price of the continuous exponential budget solution. -/
noncomputable def weightedExpPrice (c κ w : ι → ℝ) (B : ℝ) : ℝ :=
  Real.exp ((weightedExpLogCoeff c κ w - B) / weightedExpBudget κ w)

/-- Closed-form continuous allocation. Resource weights occur in the budget,
not in the residual objective. -/
noncomputable def weightedExpAllocation (c κ w : ι → ℝ) (B : ℝ) (i : ι) : ℝ :=
  (Real.log (c i * κ i / w i)
    - (weightedExpLogCoeff c κ w - B) / weightedExpBudget κ w) / κ i

variable [Nonempty ι]

theorem weightedExpBudget_pos (κ w : ι → ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) : 0 < weightedExpBudget κ w := by
  unfold weightedExpBudget
  exact Finset.sum_pos (fun i _ => div_pos (hw i) (hκ i)) Finset.univ_nonempty

/-- Weighted equality budget of the closed-form exponential allocation. -/
theorem weightedExpAllocation_budget (c κ w : ι → ℝ) (B : ℝ)
    (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) :
    ∑ i, w i * weightedExpAllocation c κ w B i = B := by
  let A := weightedExpBudget κ w
  let C := weightedExpLogCoeff c κ w
  have hA : A ≠ 0 := (weightedExpBudget_pos κ w hκ hw).ne'
  change ∑ i, w i * ((Real.log (c i * κ i / w i) - (C - B) / A) / κ i) = B
  calc
    ∑ i, w i * ((Real.log (c i * κ i / w i) - (C - B) / A) / κ i)
        = ∑ i, ((w i / κ i) * Real.log (c i * κ i / w i)
            - (w i / κ i) * ((C - B) / A)) := by
          apply Finset.sum_congr rfl
          intro i _
          field_simp [(hκ i).ne']
    _ = C - A * ((C - B) / A) := by
          rw [Finset.sum_sub_distrib]
          have hf : ∑ i, (w i / κ i) * Real.log (c i * κ i / w i) = C := rfl
          have hs : ∑ i, (w i / κ i) * ((C - B) / A) = A * ((C - B) / A) := by
            simp [A, weightedExpBudget, Finset.sum_mul]
          rw [hf, hs]
    _ = B := by field_simp [hA]; abel

omit [Nonempty ι] in
/-- Marginals at the closed-form allocation are the price times cost weight. -/
theorem weightedExpAllocation_marginal (c κ w : ι → ℝ) (B : ℝ)
    (hc : ∀ i, 0 < c i) (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i) (i : ι) :
    c i * κ i * Real.exp (-κ i * weightedExpAllocation c κ w B i)
      = weightedExpPrice c κ w B * w i := by
  have hp : 0 < weightedExpPrice c κ w B := Real.exp_pos _
  have hratio : 0 < c i * κ i / w i := div_pos (mul_pos (hc i) (hκ i)) (hw i)
  have harg : -κ i * weightedExpAllocation c κ w B i =
      Real.log (weightedExpPrice c κ w B) - Real.log (c i * κ i / w i) := by
    rw [show Real.log (weightedExpPrice c κ w B) =
      (weightedExpLogCoeff c κ w - B) / weightedExpBudget κ w from Real.log_exp _]
    unfold weightedExpAllocation
    field_simp [(hκ i).ne']
    ring
  rw [harg, Real.exp_sub, Real.exp_log hp, Real.exp_log hratio,
    weightedExpPrice]
  field_simp [(hw i).ne', (hc i).ne', (hκ i).ne']

/-- The constructed allocation is optimal for the unweighted exponential
residual among every real allocation satisfying the same weighted budget.
This is the continuous surrogate result, not an integer-bit or hardware
optimality claim. Its comparison is supplied by `rankResidual_equalized`. -/
theorem weightedExpAllocation_optimal (c κ w : ι → ℝ) (B : ℝ) (r : ι → ℝ)
    (hc : ∀ i, 0 < c i) (hκ : ∀ i, 0 < κ i) (hw : ∀ i, 0 < w i)
    (hbudget : ∑ i, w i * r i = B) :
    ∑ i, c i * Real.exp (-κ i * weightedExpAllocation c κ w B i)
      ≤ ∑ i, c i * Real.exp (-κ i * r i) := by
  classical
  have hstar : ∑ i, weightedExpAllocation c κ w B i * (w i + 0) = B := by
    calc
      ∑ i, weightedExpAllocation c κ w B i * (w i + 0)
          = ∑ i, w i * weightedExpAllocation c κ w B i := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = B := weightedExpAllocation_budget c κ w B hκ hw
  have hr : ∑ i, r i * (w i + 0) = B := by
    calc
      ∑ i, r i * (w i + 0) = ∑ i, w i * r i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = B := hbudget
  have hb : ∑ i, weightedExpAllocation c κ w B i * (w i + 0)
      = ∑ i, r i * (w i + 0) := hstar.trans hr.symm
  simpa [rankResidual] using
    rankResidual_equalized c κ w (fun _ => 0)
      (weightedExpAllocation c κ w B) r (weightedExpPrice c κ w B)
      hc hκ (Real.exp_pos _)
      (fun i => by simpa using weightedExpAllocation_marginal c κ w B hc hκ hw i)
      hb

end Hagi.Budget
