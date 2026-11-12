import Hagi.Legacy.RecursiveGrowth
import Hagi.Legacy.AdvanceWitness
import Hagi.Legacy.ArchitectureTheorem
import Hagi.Legacy.Assumptions
import Hagi.Legacy.CertifiedGrowth
import Hagi.Legacy.CorePremisesDerived
import Hagi.Legacy.GrandSynthesis
import Hagi.Legacy.HAGICertWitness
import Hagi.Legacy.LearningKernel
import Hagi.Legacy.LinkedWitness
import Hagi.Legacy.MasterChallenge
import Hagi.Legacy.MasterHAGI
import Hagi.Legacy.MasterHAGICoupled
import Hagi.Legacy.MasterHAGITrunc
import Hagi.Legacy.Nonvacuity
import Hagi.Legacy.NonvacuityHorizon
import Hagi.Legacy.QuadraticConcrete
import Hagi.Legacy.StateTakeoff
import Hagi.Legacy.TernaryGrad
import Hagi.Legacy.TopLevel

/-!
# Hagi.Legacy — quarantined vacuous-stack modules (C217)

These modules are intentionally OUTSIDE the root `Hagi` import
closure (audit P0a quarantine). They remain buildable and
CI-covered via the `Hagi.Legacy` lean_lib but their declarations
are no longer part of the root census / NamePool surface.
-/
