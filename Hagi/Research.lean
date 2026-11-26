import Hagi.Research.ConditionalInformation
import Hagi.Research.CrossModalGap
import Hagi.Research.OmniInvariant
import Hagi.Research.OmniState
import Hagi.Research.Site
import Hagi.Research.PPT
import Hagi.Research.PPTCanonical
import Hagi.Research.Schelling
import Hagi.Research.SchellingPercolation
import Hagi.Research.MarkovPercolation
import Hagi.Research.SchellingCandidateSelection
import Hagi.Research.SchellingMarkovRouting
import Hagi.Research.Ceilings
import Hagi.Research.ChainUnification
import Hagi.Research.RecursiveSelfDevelopment
import Hagi.Research.RoundViability
import Hagi.Research.RsiCriterion
import Hagi.Research.SeedOnly

/-!
# Hagi.Research — quarantined research models

Research-model modules (Omni cross-modal invariants, Percolation
site thresholds, Schelling routing/selection, Discovery PPT). They are
intentionally OUTSIDE the root `Hagi` import closure and form a closed
consumer cluster (no main theorem in the root closure cites them).
-/
