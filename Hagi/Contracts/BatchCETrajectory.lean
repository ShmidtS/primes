import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Math.Foundations.Telescope
import Hagi.Unified.ParetoExecution
import Hagi.State.TrainState
import Hagi.State.Transition
import Hagi.Contracts.CEStepCertificate
import Hagi.Contracts.BatchCEStepCore
import Hagi.Contracts.BatchCETrajectory.Core
import Hagi.Contracts.BatchCETrajectory.Direction
import Hagi.Contracts.BatchCETrajectory.FixedBatch

/-!
# BatchCETrajectory — import aggregator

Re-exports the split submodules `Core` / `Direction` / `FixedBatch`
(repeated common-direction batch CE transitions) under the historical
`Hagi.Contracts.BatchCETrajectory` namespace. No new declarations.
-/

namespace Hagi.Contracts.BatchCETrajectory
end Hagi.Contracts.BatchCETrajectory
