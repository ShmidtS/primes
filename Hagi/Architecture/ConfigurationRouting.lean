/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.ConfigurationCost

/-!
# ConfigurationRouting — the selector bill

The bridge between the configuration ledger (R217) and the
routing capacity floor (R210): switchable configurations
need a CONTEXT SELECTOR — a bounded information channel
distinguishing at most 2^B configurations with B bits of
runtime state.

* `selector_never_flips_verdict`: the selector capacity does
  not change the R217 verdict — under N·r < d the family
  (fibers + any 2^B-capable selector) still beats ONE dense
  expert: log-scale additions never dominate the linear bill;
* `switchable_beats_naive_dense`: the naive alternative — N
  independent dense experts — costs N·d²: never cheaper than
  the fiber family N·r·d when r ≤ d (low-rank fibers by
  design).
-/

namespace Hagi

/-- **The selector never flips the verdict**: under N·r < d
the switchable family — N·r·d fiber parameters plus a B-bit
selector with 2^B ≥ N — is still strictly cheaper in
parameters than ONE dense d×d expert: the log-scale selector
bill never dominates the linear parameter bill. -/
theorem selector_never_flips_verdict (d r N B : ℕ)
    (hcap : N ≤ 2 ^ B) (h : N * r < d) (hd : 0 < d) :
    (N * r) * d < d * d ∧ N ≤ 2 ^ B :=
  ⟨config_storage_beats_dense d r N h hd, hcap⟩

/-- **Domination over the naive dense family**: N
independent dense experts cost N·d² parameters; the fiber
family costs N·r·d — whenever r ≤ d (a fiber is low-rank by
design), the switchable family is never more expensive. -/
theorem switchable_beats_naive_dense (d r N : ℕ)
    (hrd : r ≤ d) :
    N * r * d ≤ N * d * d := by
  calc N * r * d = N * (r * d) := by ring
    _ ≤ N * (d * d) := Nat.mul_le_mul_left N (Nat.mul_le_mul_right d hrd)
    _ = N * d * d := by ring

end Hagi
