import Hagi.Information.Pinsker
import Hagi.Probability.PinskerTV
import Hagi.Unified.ArchitectureTheorem

namespace Hagi.Unified

/-!
# Pinsker — единая точка входа семейства Пинскера (P1.5)

Консолидация форм неравенства Пинскера (план P1.5;
дубли «Pinsker×2 + KL/TV-модули»):

* **Функциональная форма** (`Hagi.Information.Pinsker`,
  `pinsker4_fin`): |E_q f − E_p f| ≤ 2√KL для 0 ≤ f ≤ 1;
* **TV-форма** (`Hagi.Probability.PinskerTV`,
  `pinsker_sqrt_kl`): ½ Σ|p−q| ≤ √KL — классика через
  Бхаттачарью;
* **Энтропийная непрерывность** (`entropy_continuity_pinsker`
  и `'`-вариант в этом же модуле Unified): Фанне-Пинскер
  оценка |H(p) − H(q)|.

Все формы на канонических `Prelude.klDef/entDef/tvDef`;
настоящий модуль — фасад и реестр форм (P1.5), дубликатных
определений нет.
-/

end Hagi.Unified
