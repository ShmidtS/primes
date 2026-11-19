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

C455 slicing: the former 5555-line monolith is split into four files
under `Hagi.Model.EnergyReasoning.Pseudolikelihood.*` (Core, LocalField,
Mixing, CRAM) with unchanged fully-qualified names. This module remains
the import point for consumers (Hagi.lean, Training.StepProvider,
Contracts.DataToQuality).
-/

namespace Hagi.Model.EnergyReasoning

end Hagi.Model.EnergyReasoning
