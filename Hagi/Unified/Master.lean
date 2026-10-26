import Hagi.Unified.MasterHAGI
import Hagi.Unified.MasterHAGITrunc
import Hagi.Unified.MasterHAGICoupled
import Hagi.Unified.GrandSynthesis
import Hagi.Unified.Assumptions

namespace Hagi.Unified

/-!
# Master — единая главная теорема HAGI (P2.11)

Сведение четырёх Master-форм к одной иерархии (план P2.11):

* **Главная теорема** — `premises_to_certified`
  (Assumptions.lean): CertifiedHAGIInvariant выводится
  напрямую из конусного блока эмпирических посылок через
  доказанный takeoff (trunc_premises_takeoff); это канон,
  на который замыкаются специализации;
* **MasterHAGI** (R91): одна итерация — CorePremises ⟹
  убывание Φ_HAGI по сертификату (одношаговая база);
* **MasterHAGI_trunc** (горизонт T): конусный блок h_emp ⟹
  CertifiedHAGIInvariant на горизонте (большой посылочный
  блок; его конусное ядро уже выведено в
  trunc_cone_invariance / trunc_premises_takeoff);
* **MasterHAGICoupled**: обструкции (бюджет/рост) —
  отрицательные теоремы, защищающие семантику;
* **GrandSynthesis** (grand_synthesis): конъюнкция пяти
  слоёв — синтетический итог поверх Master-форм.

Специализации — тонкие срезы одной главной теоремы;
дубликатных форм нет.
-/

end Hagi.Unified
