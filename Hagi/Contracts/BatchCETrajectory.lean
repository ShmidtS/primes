import Hagi.Contracts.BatchCETrajectoryFixedBatch
import Hagi.Contracts.BatchCETrajectoryGuarded
import Hagi.Contracts.BatchCETrajectoryCanonical
import Hagi.Contracts.BatchCETrajectoryMinNorm
import Hagi.Contracts.BatchCETrajectoryFixtures
import Hagi.Contracts.BatchCETrajectoryGuardedInput
import Hagi.Contracts.BatchCETrajectoryDirection
import Hagi.Contracts.BatchCETrajectoryHalfMinNorm
import Hagi.Contracts.BatchCETrajectoryEvaluated

/-!
# Repeated common-direction batch CE transitions

A fixed finite batch is re-evaluated after every actual `State.trainStep`.
The common residual and safe step therefore always use the successor's own
weights, rather than reusing stale first-step quantities.  Nonempty vocabulary
is enough for nonnegative CE and for the per-step majorizer.

The actual loss differences telescope and dominate the sum of certified
majorizer residuals.  Nonnegative CE and antitonicity imply convergence of the
loss values to their real infimum.  That infimum is not asserted to be zero,
to be a global optimum, or to make parameters or residuals converge.

The batch and ledger inputs are supplied and deterministic.  This is not an
IID, fresh-data, external-quality or hardware-compute theorem.
-/

namespace Hagi.Contracts.BatchCETrajectory
end Hagi.Contracts.BatchCETrajectory
