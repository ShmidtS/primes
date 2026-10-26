import Hagi.Information.DiscreteFannes
import Hagi.Data.FannesSmooth
import Hagi.Unified.FannesComplete
import Hagi.Unified.NernstFannes

namespace Hagi.Unified

/-- Слой-реестр (см. докмодуль): единая точка входа Фанне. -/
abbrev FannesLayers := True

/-!
# Fannes — единая точка входа неравенства Фанне (P1.4)

Консолидация трёх слоёв неравенства Фанне / непрерывности
энтропии (план рефакторинга P1.4; аудит-дубли «Fannes×3»):

* **Матричный слой** (`Hagi.Information.DiscreteFannes`):
  энтропия гермитовых состояний, унитарная инвариантность,
  вогнутость, спектральная оценка;
* **Вероятностный слой** (`Hagi.Data.FannesSmooth`):
  TV-Липшицевость шенноновской энтропии со сглаживанием δ;
* **Комбинаторный слой** (`Hagi.Unified.FannesComplete`):
  смешивания, безусловная форма, шеннон vs log card;
* **Термодинамический слой** (`Hagi.Unified.NernstFannes`):
  Нернст-сэндвич поверх непрерывности энтропии.

Все определения канонические (`Prelude.entDef/tvDef`);
настоящий модуль — фасад и реестр слоёв, дубликатных
определений нет.
-/

end Hagi.Unified
