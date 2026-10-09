/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Depth.RootContrast

set_option linter.style.header false

/-!
# Unified — two recursions, one currency

* `uncertainty_contraction`: a contracting operator
  (`P x ≤ x`) contracts every isotone uncertainty measure:
  `U (P x) ≤ U x`.
* `finite_termination`: if every non-fixed step of `P`
  strictly decreases a ℕ-rank, then `rank ((P^[k]) x0) + k ≤
  rank x0` after `k` non-fixed steps — the chain reaches a
  fixed point within `rank x0` steps.
* `traininfer_critical`: the cost `J(T) = T + C·(N∞ +
  a·e^{−kT})` has its critical point at
  `T* = log (C·a·k) / k`.
* `highway_gain_transport_bound`: a gain bounded by
  `E_capt · η` with `η ≤ 1` is bounded by `E_capt`.
-/

open Finset Real

namespace Hagi

section StateLattice

/-- If `P x ≤ x` for all `x` and `U` is isotone, then
`U (P x) ≤ U x` for all `x`. -/
theorem uncertainty_contraction {α β : Type} [Preorder α] [Preorder β]
    (P : α → α) (U : α → β)
    (hmono : ∀ x y, x ≤ y → U x ≤ U y) (hcontract : ∀ x, P x ≤ x) :
    ∀ x, U (P x) ≤ U x := by
  intro x
  exact hmono _ _ (hcontract x)

/-- If every non-fixed step of `P` strictly decreases `rank`
and the first `k` iterates from `x0` are all non-fixed, then
`rank ((P^[k]) x0) + k ≤ rank x0`. -/
theorem finite_termination {α : Type} (rank : α → ℕ) (P : α → α)
    (hstrict : ∀ x, P x ≠ x → rank (P x) < rank x) (x0 : α) (k : ℕ)
    (hchain : ∀ i < k, (P^[i]) x0 ≠ (P^[i+1]) x0) :
    (P^[k]) x0 ≠ x0 → rank ((P^[k]) x0) + k ≤ rank x0 := by
  have htele : ∀ j ≤ k, rank ((P^[j]) x0) + j ≤ rank x0 := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjk : j < k := by omega
        have hne : (P^[j]) x0 ≠ (P^[j+1]) x0 := hchain j hjk
        have hstep : rank ((P^[j+1]) x0) < rank ((P^[j]) x0) := by
          have h1 : (P^[j+1]) x0 = P ((P^[j]) x0) := Function.iterate_succ_apply' P j x0
          rw [h1]
          refine hstrict _ (fun hcon => hne ?_)
          exact (h1 ▸ hcon).symm
        have hih := ih (by omega)
        omega
  intro hfinal
  have h := htele k (le_refl k)
  omega

end StateLattice

section TrainInfer

/-- For `C, a, k > 0` with `1 < C * a * k`, the derivative
of `J(T) = T + C·(N∞ + a·e^{−kT})` vanishes at
`T* = log (C * a * k) / k`: the stated identity
`1 − C·a·k·e^{−k·T*} = 0` holds. -/
theorem traininfer_critical (C a k : ℝ) (hC : 0 < C) (ha : 0 < a) (hk : 0 < k)
    (harg : 1 < C * a * k) :
    1 - C * a * k * Real.exp (-(k * (Real.log (C * a * k) / k))) = 0 := by
  have hkT : k * (Real.log (C * a * k) / k) = Real.log (C * a * k) := by
    field_simp
  rw [hkT, Real.exp_neg, Real.exp_log (by nlinarith : (0:ℝ) < C * a * k)]
  field_simp
  ring

end TrainInfer

section TransportEta

/-- If `0 ≤ Ecapt`, `eta ≤ 1`, and `gain ≤ Ecapt * eta`,
then `gain ≤ Ecapt`. -/
theorem highway_gain_transport_bound (Ecapt eta gain : ℝ)
    (hE : 0 ≤ Ecapt) (_heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hgain : gain ≤ Ecapt * eta) :
    gain ≤ Ecapt := by
    nlinarith [hgain, heta1, hE, mul_nonneg hE _heta]

end TransportEta

end Hagi
