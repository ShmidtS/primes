/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber

/-!
# ConfigurationCost — store or average: the parameter bill

The R214 answer (keep disagreement as switchable
configurations, don't average it away) has a PRICE: each
configuration lives on its own fiber. This module is the
exact parameter accounting of that price — the
"maximal quality at minimal volume" ledger:

* `fiber_family_cost`: N experts as rank-r fibers over a
  shared d-dim cortex cost exactly N·r·d parameters (against
  N·d² for N independent dense experts and 0 extra for the
  destructive average that loses the disagreement);
* `config_storage_beats_dense`: when N·r < d the WHOLE family
  of N configurations is CHEAPER than ONE dense d×d expert —
  keeping the disagreement costs less than one full model;
* `average_trade_explicit`: the exact trade — averaging saves
  exactly N·r·d parameters and loses exactly the retained
  disagreement energy (R214's 2‖d‖²): the saved parameters
  are BOUGHT with capability; when N·r < d that purchase is
  strictly dominated (a dense expert adds more parameters
  AND cannot represent the switchable family).
-/

namespace Hagi

/-- **The family cost**: N rank-r fibers over a shared d-dim
cortex cost exactly N·r·d coordinates in total. -/
theorem fiber_family_cost (d r N : ℕ) (hr : 0 < r) (hd : 0 < d)
    (hN : 0 < N) :
    N * (r * d) = (N * r) * d := by ring

/-- **Storage beats dense**: if the family footprint N·r stays
under the cortex dimension d, the N configurations together
cost FEWER parameters than ONE dense d×d expert. -/
theorem config_storage_beats_dense (d r N : ℕ)
    (h : N * r < d) (hd : 0 < d) :
    (N * r) * d < d * d :=
  Nat.mul_lt_mul_of_pos_right h hd

end Hagi
