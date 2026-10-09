/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber

/-!
# ConfigurationCost — the parameter bill of storing configurations

Parameter accounting for N experts stored as rank-r fibers
over a shared d-dim cortex:

* `fiber_family_cost` — the family costs `N * r * d`
  coordinates (reassociation of `N * (r * d)`).
* `config_storage_beats_dense` — if `N * r < d` and `0 < d`,
  the whole family `(N * r) * d` is cheaper than one dense
  `d * d` expert.
-/

namespace Hagi

/-- N rank-r fibers over a shared d-dim cortex cost
`N * r * d` coordinates in total. -/
theorem fiber_family_cost (d r N : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hN : 0 < N) :
    N * (r * d) = (N * r) * d := by ring

/-- If `N * r < d` and `0 < d`, the family of N
configurations costs fewer parameters than one dense `d × d`
expert. -/
theorem config_storage_beats_dense (d r N : ℕ)
    (h : N * r < d) (hd : 0 < d) :
    (N * r) * d < d * d :=
  Nat.mul_lt_mul_of_pos_right h hd

end Hagi
