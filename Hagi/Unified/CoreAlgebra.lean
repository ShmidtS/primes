import Hagi.Core.Attention
import Hagi.Core.BlockDiag
import Hagi.Core.ErrorProp
import Hagi.Core.Kronecker
import Hagi.Core.Merge
import Hagi.Core.Mix
import Hagi.Core.Ridge

/-!
# Unified.CoreAlgebra — фасад компонентной алгебры

Слой-6 фасад: компонентные примитивы HAGI — устойчивость
внимания (ошибка демпфируется весами), оптимальность риджа
(решение нормального уравнения минимизирует), распространение
ошибки по слоям, кронекерова алгебра.
-/

namespace Hagi.Unified

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

end Hagi.Unified
