import Hagi.Contracts.BatchCEStepCore
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Contracts.BatchCEBudgetHalf
import Hagi.Contracts.BatchCEBudgetPareto
import Hagi.Contracts.BatchCEBudgetIdentity
import Hagi.Contracts.BatchCEBudgetAsym
import Hagi.Contracts.BatchCEBudgetExpanded

/-!
# Executed arithmetic-batch CE descent through the canonical trainStep

This module computes a common batch direction and safe step from actual current
backbone weights and supplied feature/label maps, then executes the existing
`State.trainStep`.  It proves that this executed update is the same
`batchNextParameters` from `Model.BatchCEDescent`.

Certificates concern the actual arithmetic-mean categorical cross-entropy on
the supplied batch, not independent per-example descent, fresh held-out data,
global convergence, or external quality telemetry.  Cost, risk and optional
memory writes remain supplied logical inputs, not physical measurements.
-/

namespace Hagi.Contracts.BatchCEStepCertificate
end Hagi.Contracts.BatchCEStepCertificate
