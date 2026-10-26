import Hagi.Foundations.Hoeffding
import Hagi.Ensemble.Hoeffding
import Hagi.Probability.Azuma
import Hagi.Probability.Freedman
import Hagi.Probability.FreedmanTwoSided
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.CertifiedEstimator

namespace Hagi.Unified

/-!
# Concentration — единая точка входа концентрационного слоя (P1.6)

Реестр концентрационных неравенств (план P1.6; аудит
«Hoeffding×4»):

* **Хордовое ядро** (`Hagi.Foundations.Chord` через
  Foundations/Ensemble.Hoeffding): канонический хордовый
  аппарат; делегаты exp_chord/exp_chord_ab;
* **Бернулли MGF** (`Hagi.Foundations.Hoeffding`):
  bern_mgf_bound / mgf_hoeffding — продуктовая форма;
* **Азума** (`Hagi.Probability.Azuma`): мартингал-разности;
* **Фридман** (`Hagi.Probability.Freedman`, `FreedmanTwoSided`):
  var-adaptive хвосты + anytime-уверенность
  (`freedman_confidence`) и union-слой
  (`premises_union_confidence`, `probable_conclusion`);
* **Чернов CGF** (`Hagi.Probability.ChernoffCGF`).

Различные объекты (iid / мартингал / adaptive), дубликатных
определений нет; хордовые части делегированы в Foundations.
-/

end Hagi.Unified
