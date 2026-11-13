import Hagi.Model.BatchCEDescentCommon
import Hagi.Model.BatchCEDescentArithmetic
import Hagi.Model.BatchCEDescentDirection
import Hagi.Model.BatchCEDescentSafeStep
import Hagi.Model.BatchCEDescentFixtures
import Hagi.Model.BatchCEDescentHalfEta
import Hagi.Model.BatchCEDescentResidualNorm
import Hagi.Model.BatchCEDescentLogitRange
import Hagi.Model.BatchCEDescentStochastic


/-!
# Common-direction arithmetic-batch cross-entropy descent

This module proves a one-step majorization certificate for the raw arithmetic
mean of one-hot cross-entropy losses on a supplied finite batch.  The common
parameter direction is the arithmetic mean of the existing per-example
negative residual directions.  Its mean directional action is exactly minus
the squared norm of the mean residual transpose, and the quadratic coefficient
uses the arithmetic mean of the squared logit ranges of that same direction.

For an arbitrary common direction and nonnegative step, the existing Böhning
bound `Hagi.Energy.lse_shift_upper` controls second-order error; this is not a
probability tail theorem.  The selected safe step is zero when the mean squared
range is zero.  Otherwise it minimizes the named averaged quadratic majorizer
and gives strict descent of the actual arithmetic-mean batch loss.  Positive
mean squared range implies a nonempty batch and positive alignment.

The results concern only the supplied batch and quadratic majorizer.  A second
candidate is the totalized minimum-norm point of the raw residual-gradient
convex hull.  Its negative gives nonincreasing CE for every sample, with strict
descent at a nonzero minimizer inside the exact half-window.  Empty batches and
zero minimizers use a zero step, with no fabricated strict-progress claim.

These are formal one-step certificates, not global CE minimization, held-out or
statistical performance, native execution speed, or general neural-network
optimality results.  Empty-batch mean values use Lean's `0 / 0 = 0` algebra
convention.

References are the repository implementations in `Model.CEDescent`,
`Model.CEGradient`, and `Energy.PoEBound`.
-/


namespace Hagi.Model.BatchCEDescent
end Hagi.Model.BatchCEDescent
