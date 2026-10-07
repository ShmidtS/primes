/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.InformationRetention

/-!
# RoutingCapacity — the router is a bounded information channel

The router-as-channel view (the HAGI reading of the 119 core):
routing (top-k, quantized gates) is a DETERMINISTIC compression
of the input; the capabilities it can serve downstream are
capped by its ROUTE COUNT, and the routes are capped by the
routing-state BITS: exponential form of the counting floor.

Main results:

* `router_capacity_bound`: K pairwise-separated task families
  served ε-well through such a router force K ≤ 2^B — the
  routing state must hold log₂ K bits: the top-k/quantization
  budget is a CAPABILITY budget, not an engineering choice.
-/

namespace Hagi.Information

open Finset

/-- **The router capacity bound**: if K pairwise 2ε-separated
task families are each served ε-well through a deterministic
router with B bits of state (at most 2^B routes), then
K ≤ 2^B: preserving K separated capabilities requires
log₂ K routing bits. -/
theorem router_capacity_bound {A Q : Type} [Fintype Q]
    [DecidableEq Q] (eps : ℝ) (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated eps good tasks)
    (encode : A → Q) (decode : Q → A)
    (hcover : ∀ x ∈ tasks, ∃ w : A, good (decode (encode w)) x)
    (B : ℕ) (hQ : Fintype.card Q ≤ 2 ^ B) :
    tasks.card ≤ 2 ^ B := by
  have h1 : tasks.card ≤ Fintype.card Q :=
    quantized_separation_needs_range eps good tasks hsep encode
      decode hcover
  exact le_trans h1 hQ

end Hagi.Information
