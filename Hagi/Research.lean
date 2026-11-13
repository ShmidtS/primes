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

/-!
# Hagi.Research — quarantined research models (C240, A5 §R4)

These research-model modules (Omni cross-modal invariants, Percolation
site thresholds, Schelling routing/selection, Discovery PPT) are
intentionally OUTSIDE the root `Hagi` import closure (A5 R4 "Research
quarantine"). They form a closed consumer cluster (no main theorem in the
root closure cites them), remain buildable and tracked by Freeze via the
`Hagi.Research` lean_lib, but their declarations are no longer part of the
root census / NamePool surface. Original namespaces (Hagi.Omni,
Hagi.Percolation, Hagi.Discovery, Hagi.Optimization.Schelling*,
Hagi.Optimization.MarkovPercolation, Hagi.Contracts.Schelling*) are kept,
so all public FQNs are unchanged.
-/
