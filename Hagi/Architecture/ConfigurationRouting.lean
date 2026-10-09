/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.ConfigurationCost

/-!
# ConfigurationRouting — the selector bill

* `selector_never_flips_verdict` — if `N ≤ 2 ^ B` and
  `N * r < d`, the family `(N * r) * d` is still strictly
  cheaper than one dense `d * d` expert (and `N ≤ 2 ^ B`
  holds).
* `switchable_beats_naive_dense` — if `r ≤ d`, the fiber
  family `N * r * d` costs at most the naive dense family
  `N * d * d`.
-/

namespace Hagi

/-- If `N ≤ 2 ^ B` and `N * r < d`, then
`(N * r) * d < d * d` (and `N ≤ 2 ^ B`). -/
theorem selector_never_flips_verdict (d r N B : ℕ)
    (hcap : N ≤ 2 ^ B) (h : N * r < d) (hd : 0 < d) :
    (N * r) * d < d * d ∧ N ≤ 2 ^ B :=
  ⟨config_storage_beats_dense d r N h hd, hcap⟩

/-- If `r ≤ d`, the fiber family costs at most the naive
dense family: `N * r * d ≤ N * d * d`. -/
theorem switchable_beats_naive_dense (d r N : ℕ)
    (hrd : r ≤ d) :
    N * r * d ≤ N * d * d := by
  calc N * r * d = N * (r * d) := by ring
    _ ≤ N * (d * d) := Nat.mul_le_mul_left N (Nat.mul_le_mul_right d hrd)
    _ = N * d * d := by ring

end Hagi
