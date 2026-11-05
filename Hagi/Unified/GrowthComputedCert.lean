import Hagi.System.GrowthComputed
import Hagi.Unified.HonestTransition

set_option linter.style.header false

/-!
# GrowthComputedCert — computed growth → CertStep (цикл 47)

Каноническая computed-energy машина не просто доказывает ledger
`growEnergy_derived`: её реальный переход весов даёт минимальное
ядро `CertStep` с вычисленным положительным drop. Никаких
`h_emp_*`: коэффициент `(1−(1−η)²)` и энергия вычисляются.
-/

namespace Hagi.Unified.GrowthComputedCert

open Hagi.System.GrowthComputed Hagi.Unified.HonestTransition

/-- Реальный переход computed-growth: параметры заменяются
градиентным шагом; остальные каналы состояния сохраняются. -/
noncomputable def next {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S : Hagi.System.GrowthState X) (eta : ℝ) :
    Hagi.System.GrowthState X :=
  { S with weights := growthStep S.weights eta }

/-- Вычисленный CertStep роста: drop = `(1−(1−η)²)·E`,
фактическое равенство из `growthQuad_step`. -/
noncomputable def stepCert {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S : Hagi.System.GrowthState X)
    (eta : ℝ) (h0 : 0 < eta) (h2 : eta < 2)
    (hw : ∑ i, S.weights i ^ 2 ≠ 0) :
    CertStep (fun St => growthQuad St.weights) S (next S eta) where
  drop := (1 - (1 - eta) ^ 2) * growthQuad S.weights
  drop_pos := by
    have hcoef : 0 < 1 - (1 - eta) ^ 2 := by
      have hlt : (1 - eta) ^ 2 < 1 := by
        have hleft : -1 < 1 - eta := by linarith
        have hright : 1 - eta < 1 := by linarith
        nlinarith [sq_nonneg (1 - eta), hleft, hright]
      linarith
    exact mul_pos hcoef (growthQuad_pos_of_nonzero S.weights hw)
  actual := by
    change growthQuad (growthStep S.weights eta)
      ≤ growthQuad S.weights - (1 - (1 - eta) ^ 2) * growthQuad S.weights
    rw [growthQuad_step]
    ring_nf
    exact le_rfl

end Hagi.Unified.GrowthComputedCert
