/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Softmax
import Mathlib.Tactic

/-!
# Certified sandwich CE bench bridge

The consumption bit of `Hagi.Theory.
RationalSoftmax`.  The certified-CE training loop of
`scripts/bench_bridge.py` (`--mode cert-sandwich`) descends the
RATIONAL sandwich certificate `-log (lo u / ∑ hi)` (built from
the two-sided exponential bounds) instead
`z ^ 2 / Σ z ^ 2` surrogate.  This module states the descent
bridge that makes that loop meaningful: a measured drop of the
rational certificate controls the drop of the TRUE one-hot
cross-entropy up to the certificate's gap-width bound.

## The bridge

`sandwich_descent` (abstract): if the true values are below
their certificates at both states and the initial excess is
bounded by `g`, then every certificate drop `ce − ce' ≥ 0`
forces the true drop `tc − tc'` to be at least the certificate
drop minus `g`.

`certCE_descent` (instantiated): applying `certCE_le` at the
two logit states and `certCE_gap` at the initial one, the
descent of `-log (lo u / ∑ hi)` to `-log (lo' u / ∑ hi')`
lower-bounds the descent of the true `-log (softDef · u)` by
that drop minus `log ((hi u * ∑ hi) / (lo u * ∑ lo))` — the
certified width link: descending the rational certificate
descends the true CE down to the gap boundary.

## Honest pins

1. The bench objective is the exact rational product
   `∏ (∑ hi) / lo_y`; log monotonicity makes its descent
   EQUIVALENT to the descent of the mean certificate CE
   `-(1/N) ∑ -log (lo y / ∑ hi)` — the certificate channel
   never evaluates an irrational log.  Float true-CE in the
   bench is TELEMETRY ONLY (outside the certificate).
2. The bench learning rate is a guarded normalized analytic
   gradient step (measured-drop admission); no smoothness
   constant is certified for the sandwich objective; the
   adaptive-majorizer η of `Hagi.Theory.AdaptiveMajorizer` is
   not used by the bench.
3. Feature/weight snap-to-grid pins (family) live in
   the bench script, not here; this module is n,m-free.
-/

set_option linter.style.header false

namespace Hagi.Theory.CertSandwichBench

open Real Hagi.Prelude Hagi.Theory.RationalSoftmax

/-- Abstract descent bridge: with true values below their
certificates at both states and the initial certificate excess
`ce - tc` bounded by `g`, any certificate drop `ce - ce' ≥ 0`
forces the true drop `tc - tc'` to be at least `ce - ce' - g`:
descending the certificate descends the truth down to the gap
boundary. -/
theorem sandwich_descent {ce ce' tc tc' g : ℝ}
    (_h1 : tc ≤ ce) (h2 : tc' ≤ ce') (hg : ce - tc ≤ g)
    (hd : 0 ≤ ce - ce') : ce - ce' - g ≤ tc - tc' := by
  linarith

variable {V : Type} [Fintype V] [Nonempty V]

/-- Instantiated bridge: the descent of the rational sandwich
certificate `-log (lo u / ∑ hi)` between two logit states
lower-bounds the descent of the true one-hot cross-entropy
`-log (softDef · u)` by the certificate drop minus the
certified gap-width bound `log ((hi u * ∑ hi) / (lo u * ∑ lo))`
of the INITIAL state (`certCE_gap`).  This is the theorem the
`--mode cert-sandwich` bench loop of `scripts/bench_bridge.py`
consumes: measured drops of the rational objective certify
drops of the true CE up to the tracked gap width. -/
theorem certCE_descent {z z' lo lo' hi hi' : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v)
    (hlo' : ∀ v, lo' v ≤ Real.exp (z' v)) (hlo0' : ∀ v, 0 < lo' v)
    (hhi' : ∀ v, Real.exp (z' v) ≤ hi' v) (u : V) :
    (-Real.log (lo u / ∑ w, hi w)) - (-Real.log (lo' u / ∑ w, hi' w))
        - Real.log ((hi u * ∑ w, hi w) / (lo u * ∑ w, lo w))
      ≤ (-Real.log (softDef z u)) - (-Real.log (softDef z' u)) := by
  have t1 := certCE_le hlo hlo0 hhi u
  have t2 := certCE_le hlo' hlo0' hhi' u
  have gp := certCE_gap hlo hlo0 hhi u
  linarith

end Hagi.Theory.CertSandwichBench
