import Hagi.Information.DiscreteFannes
import Hagi.Data.FannesSmooth
import Hagi.Unified.FannesComplete
import Hagi.Unified.NernstFannes

/-!
# Fannes — единая точка входа неравенства Фанне (P1.4)

Консолидация слоёв неравенства Фанне / непрерывности
энтропии (план P1.4; аудит v4 §3.5):

* **Матричный слой** (`Hagi.Information.DiscreteFannes`):
  энтропия гермитовых состояний, унитарная инвариантность,
  вогнутость, спектральная оценка;
* **Вероятностный слой** (`Hagi.Data.FannesSmooth`):
  TV-Липшицевость шенноновской энтропии со сглаживанием δ
  (`entropy_lipschitz_smooth` — реэкспортирована ниже);
* **Комбинаторный слой** (`Hagi.Unified.FannesComplete`):
  смешивания, безусловная форма (`fanes_unconditional`),
  шеннон vs log card;
* **Термодинамический слой** (`Hagi.Unified.NernstFannes`):
  Нернст-сэндвич поверх непрерывности энтропии.

Все определения канонические (`Prelude.entDef/tvDef`);
фасад-реестр слоёв, дубликатных определений нет.
-/

namespace Hagi.Unified

/-! ## Явный реэкспорт канонического результата вероятностного
слоя (вместо псевдоинтерфейса `FannesLayers := True` —
аудит v4 §3.5: фасад несёт конкретные теоремы). -/

export Hagi.Data (entropy_lipschitz_smooth)

end Hagi.Unified
