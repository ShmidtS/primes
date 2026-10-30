import Mathlib
import Hagi.Core.Attention
import Hagi.Core.BlockDiag
import Hagi.Core.ErrorProp
import Hagi.Core.Kronecker
import Hagi.Core.Merge
import Hagi.Core.Mix
import Hagi.Core.Ridge
import Hagi.External.Flywheel.CoherenceCharacterization
import Hagi.External.Flywheel.CourantFischer
import Hagi.External.Flywheel.FrobeniusNorm
import Hagi.External.Flywheel.MDLRank
import Hagi.External.Flywheel.MatrixNormRelations
import Hagi.External.Flywheel.NormSupport
import Hagi.External.Flywheel.SVD
import Hagi.External.Flywheel.SpectralNormGap
import Hagi.External.Flywheel.TruncatedSVDRank1
import Hagi.External.Flywheel.WeylInequality

/-!
# AlgebraMatrixCore — алгебра и матрицы
(слияние одно-теоремных фасадов CoreAlgebra/MatrixLib, аудит v9 P3).
-/

namespace Hagi.Unified

/-!
# Unified.CoreAlgebra — фасад компонентной алгебры

Слой-6 фасад: компонентные примитивы HAGI — устойчивость
внимания (ошибка демпфируется весами), оптимальность риджа
(решение нормального уравнения минимизирует), распространение
ошибки по слоям, кронекерова алгебра.
-/


export Hagi.Core (attention_error_damped_sum attention_error_damped
  propagate_bound ridge_optimal kronecker_mul_conjTranspose
  mixed_invisible)

/-- КОМПОНЕНТНЫЙ ПРИНЦИП (сводка): (1) ошибка внимания
демпфируется весами (‖Δ‖ ≤ Σ p·‖e‖); (2) ридж-решение
нормального уравнения глобально оптимально. Смешение не
создает видимых артефактов (mixed_invisible) — примитивы
корректны по построению. -/
theorem core_stable_and_optimal
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ι → ℝ) (v e : ι → E)
    (hp : ∀ i, 0 ≤ p i)
    {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ)
    (y : m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) {w₀ : n → ℝ}
    (hne : ridgeNormalEq X y lam w₀) :
    ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ ∑ i, p i * ‖e i‖
      ∧ ∀ w : n → ℝ, ridge X y lam w ≥ ridge X y lam w₀ :=
  ⟨attention_error_damped_sum p v e hp,
    ridge_optimal hlam hne⟩


/-!
# Unified.MatrixLib — фасад матричной библиотеки Flywheel

Слой-6 фасад: SVD, Эккарт–Янг, Вейль, Курант–Фишер,
кронекеровы перестановки, MDL-ранг. Кандидат в апстрим
Mathlib (план аудита v5 L1-Matrix).
-/

open Matrix


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


