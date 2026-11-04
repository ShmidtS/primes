import Mathlib.Tactic
import Hagi.Learning.FOOF
import Hagi.Learning.RegCovPD

set_option linter.style.header false

/-!
# FOOFUnique — единственность решения Mesa/FOOF (цикл 13)

Если оба W₁ и W₂ удовлетворяют нормальному уравнению
W·(XXᵀ+λI) = VXᵀ и C = XXᵀ+λI обратима (теорема regCov_det_unit
при λ>0), то W₁ = W₂ — аналитический оптимум регуляризованной
least-squares задачи ЕДИНСТВЕНЕН.
-/

open Finset Matrix

namespace Hagi.Learning.FOOFUnique

open Hagi.Learning.FOOF Hagi.Learning.RegCovPD

variable {d T : ℕ}

/-- ЕДИНСТВЕННОСТЬ: нормальное уравнение имеет не более одного
решения при обратимой C. -/
theorem foof_normal_unique (V X : Matrix (Fin d) (Fin T) ℝ)
    (lam : ℝ) (hinv : IsUnit (regCov X lam).det)
    (W1 W2 : Matrix (Fin d) (Fin d) ℝ)
    (h1 : W1 * regCov X lam = V * Xᵀ)
    (h2 : W2 * regCov X lam = V * Xᵀ) :
    W1 = W2 := by
  have hdiff : (W1 - W2) * regCov X lam = 0 := by
    rw [Matrix.sub_mul, h1, h2, sub_self]
  have hcanc : W1 - W2 = 0 := by
    have hkey : W1 - W2
        = (W1 - W2) * regCov X lam * (regCov X lam)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hinv,
        Matrix.mul_one]
    rw [hdiff, zero_mul] at hkey
    exact hkey
  exact eq_of_sub_eq_zero hcanc

/-- СЛЕДСТВИЕ: foofW — единственное решение нормального
уравнения (при обратимости C, обеспечиваемой regCov_det_unit
при λ > 0 в согласованном контексте DecidableEq). -/
theorem foofW_unique (V X : Matrix (Fin d) (Fin T) ℝ)
    (lam : ℝ) (hinv : IsUnit (regCov X lam).det)
    (W : Matrix (Fin d) (Fin d) ℝ)
    (hW : W * regCov X lam = V * Xᵀ) :
    W = foofW V X lam :=
  (foof_normal_unique V X lam hinv W (foofW V X lam) hW
    (foof_normal_eq V X lam hinv))

end Hagi.Learning.FOOFUnique
