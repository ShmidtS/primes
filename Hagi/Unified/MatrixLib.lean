import Hagi.External.Flywheel.SVD
import Hagi.External.Flywheel.CourantFischer
import Hagi.External.Flywheel.WeylInequality
import Hagi.External.Flywheel.SpectralNormGap
import Hagi.External.Flywheel.MatrixNormRelations
import Hagi.External.Flywheel.FrobeniusNorm
import Hagi.External.Flywheel.TruncatedSVDRank1
import Hagi.External.Flywheel.MDLRank
import Hagi.External.Flywheel.CoherenceCharacterization
import Hagi.External.Flywheel.NormSupport

/-!
# Unified.MatrixLib — фасад матричной библиотеки Flywheel

Слой-6 фасад: SVD, Эккарт–Янг, Вейль, Курант–Фишер,
кронекеровы перестановки, MDL-ранг. Кандидат в апстрим
Mathlib (план аудита v5 L1-Matrix).
-/

open Matrix

namespace Hagi.Unified

/-- МАТРИЧНАЯ БИБЛИОТЕКА (сводка): (1) сингулярные значения
неотрицательны; (2) MDL-ошибка усечения антинтонна по
рангу (больше ранг — меньше ошибка). Спектральная теория
корректна и монотонна. -/
theorem matrix_svd_nonneg_and_mdl_antitone
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    ∀ i : n, 0 ≤ Hagi.External.Flywheel.Matrix.SVD.singularValues A i
      ∧ Antitone (Hagi.External.Flywheel.Hagi.MDL.Rank.mdlErr A) := by
  intro i
  exact ⟨Hagi.External.Flywheel.Matrix.SVD.singularValues_nonneg A i,
    Hagi.External.Flywheel.Hagi.MDL.Rank.mdlErr_antitone A⟩

end Hagi.Unified
