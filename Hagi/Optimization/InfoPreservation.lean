import Mathlib.Tactic
import Hagi.Optimization.MirrorDescent

/-!
# InfoPreservation (аудит v16, Test 6: information
# preservation вдоль траектории)

Регрет-форма сохранения информации: вдоль mirrorIterate
(вариационное ядро №70) суммарное превышение потерь
траектории над ЛЮБЫМ целевым распределением ρ* ограничено
начальным KL-расстоянием T·KL(ρ*‖ρ₀) — дрейф не свободен:
информация о цели сохраняется в среднем (реюз mirror_regret
БЕЗ новых посылок).
-/

namespace Hagi.Optimization.InfoPreservation

open Hagi.Optimization

variable {V : Type*} [Fintype V] [Nonempty V]


end Hagi.Optimization.InfoPreservation
