/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.EnergyReasoning.Pseudolikelihood.Core
import Hagi.Model.EnergyReasoning.Pseudolikelihood.LocalField
import Hagi.Model.EnergyReasoning.Pseudolikelihood.Mixing
import Hagi.Model.EnergyReasoning.Pseudolikelihood.CRAM

set_option linter.style.header false

/-!
# Pseudolikelihood (umbrella)

 Split into four files under `Hagi.Model.EnergyReasoning.Pseudolikelihood.*`
(Core, LocalField, Mixing, CRAM); this module is the import point for
consumers (Hagi.lean, Training.StepProvider, Contracts.DataToQuality).
-/

namespace Hagi.Model.EnergyReasoning

end Hagi.Model.EnergyReasoning
