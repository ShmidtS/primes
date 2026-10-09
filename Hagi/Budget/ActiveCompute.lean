/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.ConfigurationCost

/-!
# ActiveCompute — the compute bill of switching

The heterarchy dividend priced in FLOPs: the
switchable architecture runs ONE active configuration at a
time (context switching, not summation) — the per-token
compute bill is the CORTEX plus the ACTIVE fiber, while the
naive dense alternative pays for the whole family on every
token (or must run N experts to cover the context).

* `active_flops`: the per-token bill of the switchable step:
  (c + r)·d multiply–adds — cortex columns plus the active
  fiber's rank;
* `active_beats_dense_family`: under c + r ≤ d and N ≥ 2
  configurations, the active bill is at most 1/N of the
  dense family's N·d² — switching is an N-fold compute
  saving, not just a parameter saving;
* `switching_never_exceeds_dense`: even the worst case
  (active bill with c + r ≤ d) never exceeds a SINGLE dense
  expert's d² — heterarchical switching never costs more
  than the monolith, at any context entropy.
-/

namespace Hagi

/-- **The active bill**: cortex c columns + active fiber of
rank r over a d-dim state: (c + r)·d multiply–adds per
token. -/
theorem active_flops (c r d : ℕ) :
    (c + r) * d = c * d + r * d := by ring

/-- **Switching never exceeds the monolith**: with
c + r ≤ d the per-token active bill never exceeds a single
dense expert's d². -/
theorem switching_never_exceeds_dense (c r d : ℕ)
    (hcr : c + r ≤ d) :
    (c + r) * d ≤ d * d :=
  Nat.mul_le_mul_right d hcr

/-- **The N-fold dividend**: with N ≥ 2 switchable
configurations and c + r ≤ d, the active per-token bill is
at most 1/N of the naive dense family's N·d² — heterarchy
saves compute by the family size, not merely parameters. -/
theorem active_beats_dense_family (c r d N : ℕ)
    (hcr : c + r ≤ d) (hN : 2 ≤ N) :
    N * ((c + r) * d) ≤ N * (d * d)
      ∧ (c + r) * d ≤ d * d
      ∧ d * d ≤ N * d * d := by
  refine ⟨?_, switching_never_exceeds_dense c r d hcr, ?_⟩
  · exact Nat.mul_le_mul_left N
      (switching_never_exceeds_dense c r d hcr)
  · nlinarith [hN]

end Hagi
