import Hagi.Foundations.StageCalculus
import Hagi.Step.SafeQP
import Hagi.Step.SafeQPStep
import Hagi.Step.StochasticSafeQP
import Hagi.Step.AdaptiveSafeQP
import Hagi.Step.KLSSafeQP
import Hagi.Step.Joint

namespace Hagi.Unified

/-!
# SafeStep — единый контракт безопасного шага (P1.8)

Реестр контракта безопасного шага (план P1.8:
StageCalculus + варианты SafeQP + TopLevel):

* **Стадийный калькулус** (`Hagi.Foundations.StageCalculus`):
  compress/merge/compound/adaptive-законы стадий;
* **Базовый SafeQP** (`Hagi.Step.SafeQP`, `SafeQPStep`):
  сертифицированное QP-обновление в окне L-гладкости
  (η ≤ 1/L, спуск ≥ η⟪g,d⟫ − Lη²‖d‖²/2);
* **Стохастический** (`Hagi.Step.StochasticSafeQP`);
* **Адаптивный** (`Hagi.Step.AdaptiveSafeQP`);
* **KLS-вариант** (`Hagi.Step.KLSSafeQP`):
  klsSafeQP_certified;
* **Joint-композиция** (`Hagi.Step.Joint`).

Все варианты сводятся к единому окну безопасности
(L-липшицев градиент, η ≤ 1/L, активное направление) —
контракт уже формализован в StageInput
(h_eta_pos, h_costs_nn, h_risks_nn) и CorePremises.
-/

end Hagi.Unified
