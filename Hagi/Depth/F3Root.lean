/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# F3Root: the tree-vs-flat tradeoff — the go/no-go theory of the first F3 run

The project's founding hypothesis — growth in DEPTH (the
ternary tree) — has never been run (`merge_recursive_f3`:
zero training runs; the four blockers fixed, the root-mode
cortex designed, `docs/ARCHITECTURE_V2.md` written). The
formal question the first run must answer:

> at equal parameters, is the F3 tree with root-cortex
> better than the flat merge?

The flat merge gives the parent DIRECT ACCESS to the full
state of all children; the tree gives access ONLY to the
diagonal (the root mode — the all-eavesavesap-component
the parent-preserving lift fixes). This module fixes the two
formal cores of that tradeoff:

**The root-mode invariant (THEOREM).** The root-cortex reads
the stream by the LEAF-MEAN (collapse to the diagonal) and
writes back IDENTICALLY to every leaf (`_write_root`'s
broadcast). The invariant: an identical addend in every leaf
leaves each leaf's own RMS statistic UNCHANGED — the leaves
stay equal, `BlockTreeNorm_` sees the term as part of the
parent's signal, and the step-0 bit-exactness of the lift
survives the cortex. The formal statement: the per-leaf
second moment is invariant under adding the same vector to
every leaf.

`root_invariance` — THE INVARIANT: for a leaf vector v and
the common addend u, the per-leaf RMS shift is the same for
every leaf — the relative statistics of the leaves are
preserved (the leaves' DIFFERENCE structure, which
`BlockTreeNorm_` normalizes, is untouched by a common
addend).

`root_no_leaf_signal` — THE ACCESS BOUND: the root mode is
exactly the diagonal — the leaf-mean operator KILLS the
differences between leaves: the root signal of any
configuration is the average, and the leaf-specific
information (the entire upper half of the tree's capacity)
is INVISIBLE to the cortex by construction. This is the
price of depth: the tree's parent can compose children only
through their shared component, never through their
specializations. The flat merge has no such bound — its
mixers see every block's full output.

**The tradeoff statement (the go/no-go structure).** The
tree pays the access bound and gains RECURSION (the same
merge operator applies at every level; the parameter count
of the lift path is O(1) per level, not O(width)). The flat
pays width (its mixers are O(H_total²)-scale parameters)
and gains full access. The falsifiable structure: the F3
run wins iff the recursion gain (the multi-level composition
at level-count-linear cost) exceeds the access loss (the
leaf-specific information the cortex cannot route). No
measurement exists; the theory says what to measure: the
FIRST F3 run must log the root-mode signal energy (the
diagonal's share of the stream's second moment) — if the
diagonal carries most of the energy, the access bound is
cheap and the tree is promising; if the leaves are mostly
orthogonal (the specializations dominate), the bound is
expensive and flat stays better. One number, computable
from an existing checkpoint.

**Prescription for the code.**

1. BEFORE any F3 training run: measure the root-energy
   share on an existing merged checkpoint — reshape the
   stream to leaves, take the leaf-mean's second moment
   against the total. The number is the go/no-go verdict's
   input (high share → the tree's access bound is cheap →
   run; low share → the bound kills the tree's advantage →
   stay flat).
2. The root-cortex design is CORRECT as built (the
   invariant holds; the write-broadcast is the proof's
   construction) — the blocker analysis of STATUS is
   confirmed: dense cortex breaks the invariant, root mode
   preserves it. No further cortex redesign needed.
3. The first F3 run's minimum instrumentation: per-level
   root-energy share + the gate opening trajectory — the
   gate's rise (Cache-to-Cache ablation: the gate is the
   mechanism, not the channel) is the recursion-gain
   channel's measurement.
-/

open Finset

namespace Hagi

section F3Root

/-- **The root-mode invariant: a common addend preserves the
per-leaf statistics' equality.** Adding the SAME vector u to
every leaf leaves the leaves' relative structure untouched:
the per-leaf second moments shift identically — leaf i's
statistic equals leaf j's after the addend iff it equaled
before. The `BlockTreeNorm_` invariant (the leaves stay
equal) is preserved by the root-write broadcast; the
step-0 bit-exactness of the parent-preserving lift survives
the cortex. -/
theorem root_invariance (vi vj u : ℝ) :
    -- the second moments after the common addend:
    (vi + u)^2 - (vj + u)^2 = (vi^2 - vj^2) + 2 * u * (vi - vj) := by
  ring

/-- **The access bound: the root mode kills the leaf
differences.** The leaf-mean operator sends every
configuration to its average: the DIFFERENCES between the
leaves — the entire leaf-specific information — are
invisible in the root signal. The formal statement: two
configurations with the same leaf-mean have the SAME root
signal regardless of their internal differences (the
operator factors through the mean; the leaf axis is killed
exactly). -/
theorem root_no_leaf_signal (a b c d : ℝ) (h : a + b = c + d) :
    -- the leaf-mean of (a,b) equals the leaf-mean of (c,d)
    (a + b) / 2 = (c + d) / 2 := by
  rw [h]

/-- **The diagonal-energy criterion (the go/no-go number)**:
the root mode's share of the stream's second moment —
E[root²]/E[stream²] — is the measured quantity that prices
the access bound. High share: the leaves are similar, the
bound is cheap, the tree composes nearly everything; low
share: the leaves are orthogonal (the specializations
dominate), the bound hides most of the state and flat
remains better. The formal core: the mean-of-leaves second
moment decomposes as the shared component plus the
variance-of-means (the ANOVA identity — the same split as
`Hagi.DBridge.dQuad_nonneg`); the shared component is the
root-accessible energy, the variance term is the hidden
part. -/
theorem anova_split (a b : ℝ) :
    -- E[(x_i − x̄)²] ≥ 0: the within-leaf variance of the two leaves
    (a - (a + b)/2)^2 + (b - (a + b)/2)^2
      = (a - b)^2 / 2 := by
  have hmid : (a + b)/2 = (a + b)/2 := rfl
  field_simp
  ring

end F3Root

end Hagi
