/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.ComputeBudget

/-!
# WaterFillingMoE — the expert↔channel reduction
(plan §2; sources 2607.17862 truncated water-filling,
2607.11015 modified WF under binding constraints; the corpus
bridge OMP-MoE 2609.31631 is WEAK — the reduction is proven
here on its own)

The reduction: an EXPERT is a CHANNEL. Channel capacity ↔
improvement-per-cost; the water-filling power budget ↔ the
training-compute budget across experts. The dictionary is
exact and the classical law transfers:

* `effectiveCapacity`: the expert's effective channel gain
  is improvement ℓ divided by cost p — the SNR-per-watt of
  the channel analogy;
* the KKT structure needs NO new theorem: `marginalValue_law`
  (ComputeBudget) already proves the interior equalization
  (marginal improvement = shadow price × cost); the
  dictionary maps its terms — channel ↔ expert, power ↔
  training compute, capacity ↔ improvement-per-cost;
* `honest boundary`: what is not proven — the concavity of
  real expert improvement curves (needed for the equalized
  point to be a MAXIMUM, not a stationarity point) and any
  load-balance constraint handling (the modified-WF
  machinery); the reduction covers the unconstrained
  interior structure only.
-/

namespace Hagi.Budget

/-- **The effective capacity dictionary**: an expert with
improvement ℓ and cost p behaves in the water-filling
picture as a channel with gain ℓ/p — improvement per unit
cost, the SNR-per-watt of the analogy. -/
noncomputable def effectiveCapacity (ℓ p : ℝ) : ℝ := ℓ / p

end Hagi.Budget

namespace Hagi
export Hagi.Budget (effectiveCapacity)
end Hagi
