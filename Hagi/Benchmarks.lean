import Hagi.Benchmarks.QuadLoopWitness
import Hagi.Benchmarks.QuarticWitness
import Hagi.Benchmarks.QuadraticEndToEnd
import Hagi.Benchmarks.TernaryWitness

/-!
# Hagi.Benchmarks — quarantined toy witness modules (C239, A5 §R3)

These demonstration modules (quadratic/quartic/ternary toy witnesses for
`certified_loop`-family capstones) are intentionally OUTSIDE the root
`Hagi` import closure (A5 R3 "18 toy -> Benchmarks" — the remainder was
already quarantined in `Hagi/Legacy` by C217). They remain buildable and
tracked by Freeze via the `Hagi.Benchmarks` lean_lib, but their
declarations are no longer part of the root census / NamePool surface.
Load-bearing quad modules (QuadMachine, DescentCoreQuad, QuadEta,
ToyTrajectory, LoopInstances) stay in the root closure.
-/
