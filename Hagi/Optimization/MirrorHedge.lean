/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Probability.MirrorHedgeGibbs
import Hagi.Probability.MirrorHedgeCertificates
import Hagi.Probability.MirrorHedgeMWU
import Hagi.Probability.MirrorHedgeMWUSelectedLoss
import Hagi.Probability.MirrorHedgeMWUSelectedGradient
import Hagi.Optimization.MirrorHedgeCore
import Hagi.Optimization.MirrorHedgeRegret
import Hagi.Optimization.MirrorHedgeEnergy
import Hagi.Optimization.MirrorHedgeWealth
import Hagi.Optimization.MirrorHedgeRouting
import Hagi.Optimization.MirrorHedgeSurvivor

set_option linter.style.header false

namespace Hagi.Optimization
end Hagi.Optimization

/-!
# MirrorHedge — канон зеркального шага (хаб)

Хаб (split C259): семейство экспоненциальных весов
(Gibbs-концентрация, MWU-потенциал, зеркальный шаг, Hedge-роутинг,
survivor-склейка аудита v5). Содержимое разнесено в тематические
части; модуль сохраняет имя для потребителей (C236 → C259).
-/
