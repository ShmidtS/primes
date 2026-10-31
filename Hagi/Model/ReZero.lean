import Mathlib
import Hagi.Model.PreNorm

/-!
# ReZero — обучаемая residual-масштабировка (источник №67:
# Bachlechner et al., "ReZero is All You Need: Fast
# Convergence at Large Depth", arXiv 2003.04887)

Идея: residual-блок x + α·f(x) с ОБУЧАЕМЫМ α,
инициализированным НУЛЁМ: в начале обучения каждый блок —
ТОЖДЕСТВО (глубокая сеть вырождается в residual-путь),
градиент течёт свободно; α вырастает по мере надобности.
Формализуем: init-тождество (α=0) и линейное по α
возмущение нормы.
-/

namespace Hagi.Model.ReZero

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- ReZero-блок: x + α·f x. -/
def rezeroStep (x fx : X) (alpha : ℝ) : X := x + alpha • fx

/-- ИСТОЧНИК №67, УРОВЕНЬ 1: INIT-ТОЖДЕСТВО — при α = 0
блок РАВЕН входу (глубокая сеть в инициализации — чистый
residual-путь; градиент беспрепятственно течёт по глубине). -/
theorem rezero_identity (x fx : X) :
    rezeroStep x fx 0 = x := by
  unfold rezeroStep
  simp

/-- УРОВЕНЬ 1b: ЛИНЕЙНОСТЬ ВОЗМУЩЕНИЯ ПО α — норма отклонения
блока от входа растёт ЛИНЕЙНО по |α| (малые α — малое
возмущение; управление глубиной через один скаляр). -/
theorem rezero_perturb_bound (x fx : X) (alpha : ℝ) :
    ‖rezeroStep x fx alpha - x‖ ≤ |alpha| * ‖fx‖ := by
  unfold rezeroStep
  rw [add_sub_cancel_left]
  exact le_of_eq (norm_smul alpha fx)

end Hagi.Model.ReZero
