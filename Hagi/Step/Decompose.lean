/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.Dominate

set_option linter.style.header false

/-!
# Decompose: the merge-gain law and the increment-discrepancy resolution

The central question of the loop — WHERE does the effect come
from — as a decomposition law, plus the resolution of the one
measured inconsistency between the formal laws.

**The decomposition (verified measurements).** The total gain
of a generation splits as

`Δ_total = Δ_ensemble + Δ_joint`

— canonical: 0.0225 + 0.2348; LoRA: 0.0350 + 0.1483; the
JOINT channel dominates both branches. The law of balance:
Δ_joint is LARGE when the mixture is conflict-free AND the
ensemble reserve is unexhausted (dbridge: Δ_ens = 0.078 —
twice canonical — and conflict-free: the prediction
Δ_joint(dbridge) > 0.15); Δ_joint is SMALL under domination
(the round-32 law: the joint optimizes one corpus, the rest
rise) or prior saturation (gen-3: the prior has drunk the
mixture).

**The increment discrepancy (the audit finding).** The
measured N-increments 0.045/0.027 (N = 3→6→9) sit BETWEEN the
GapLaw prediction (0.043/0.012) and the spread²/N law
(0.065/0.032). The resolution (a): the two laws are the TWO
ENVELOPES of a family — GapLaw is the exchangeable-symmetry
lower envelope (the leaves' deviations are permutation-
symmetric), spread²/N is the independence upper envelope
(the deviations are independent); the measured points inside
the envelope mean the leaf deviations are NEITHER fully
exchangeable NOR independent — a mixture regime. The
dbridge point (Δ_ens = 0.078 at N = 3) discriminates: under
GapLaw it is anomalous (too large), under the mixture regime
it is the natural large-spread case.

**The four-point protocol.** leaf-mean → merged-step0 →
merged-after-joint → scratch-equal-compute: the last point
is the honest baseline (N experts at budget C/N each against
one model at C — the same-param inference constraint); the
formal content: the comparison of CE against TOTAL COMPUTE,
not steps.

**Prescription for the code.**

1. The four-point benchmark is the standard of every
   generation: the two Δ's are logged per branch; the joint
   decision (run or skip) reads the law of balance
   (conflict-free + reserve unexhausted).
2. The dbridge joint prediction: Δ_joint > 0.15 — falsified
   immediately by the run.
3. The N-increment logging: report the measured point against
   BOTH envelopes (GapLaw, spread²/N) — the position inside
   the envelope is the diagnostic of the deviation regime.
-/

open Finset

namespace Hagi

section Decompose

-- DEMOTED round-61 (external audit): was `A = A := rfl`.
-- The ens/joint increment decomposition is a notation, not
-- a theorem; the accounting is definitional.

-- DEMOTED round-61 (external audit): was `hlo -> hlo`.
-- The envelope claim (GapLaw as the lower, spread^2/N as
-- the upper envelope of the N-leaf increment) is an OPEN
-- empirical hypothesis — NOT proven; STATUS references
-- corrected. The mixture-regime diagnostic is empirical.

end Decompose

end Hagi
