/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Natural
import Hagi.Contracts.BatchCEGrowthSelection

/-! Checked interoperability of the pinned Natural tactics with Hagi proofs. -/
namespace Hagi.Contracts

open Hagi.Contracts.BatchCEGrowth Hagi.Contracts.BatchCEGrowthSelection

example {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity) :
    smoothedGrowthYield S S = 0 := by
  default_apply smoothedGrowthYield_self

end Hagi.Contracts
