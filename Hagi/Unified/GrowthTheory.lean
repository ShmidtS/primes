import Hagi.Foundations.GrowthDynamics
import Hagi.Growth.FrontierScaling
import Hagi.Growth.Saturation
import Hagi.Foundations.PerronCone
import Hagi.Dynamics.SpeedLimit
import Hagi.Model.StageSemantics

namespace Hagi.Unified

/-!
# GrowthTheory — единая точка входа теории динамики роста (P1.7)

Реестр единой теории динамики и насыщения (план P1.7:
GrowthDynamics + FrontierScaling + Saturation + ростовые
части Unified):

* **Телескопные законы** (`Hagi.Foundations.GrowthDynamics`):
  anytime-бюджеты, band-телескоп, геометрические потолки;
* **Конусная динамика** (`Hagi.Foundations.PerronCone`):
  инвариантность, сравнение, возмущение, явные формы,
  экспоненциальный взлёт;
* **Frontier-масштабирование** (`Hagi.Growth.FrontierScaling`);
* **Насыщение** (`Hagi.Growth.Saturation`);
* **Speed limit** (`Hagi.Dynamics.SpeedLimit`): нижняя
  граница времени обучения;
* **Единый переход** (`Hagi.Model.StageSemantics`):
  advance-семантика + закон роста траекторий
  (advance_trajectory_takeoff).
-/

end Hagi.Unified
