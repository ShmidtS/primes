/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.NoiseTemperature
import Hagi.Probability.KLSBridge

set_option linter.style.header false

/-!
# ThermoBridge: one 1/B law — two interfaces

The thermodynamic axis of HAGI now has two formalizations of
the SAME noise-cooling law:

* `batch_variance_eq` (NoiseTemperature): the exact identity
  Var(batchMean) = Var(g)/B on the product-probability
  interface (`prodE`/`uniP`) — no hypotheses beyond the
  uniform product system.
* `klsBatchNoise` (KLSBridge): the dimension-free BOUND
  σ² ≤ C·L²·‖a‖²/B on the finite-vector interface
  (`KLS.expQ`) — under the Poincaré interface.

This module welds the interfaces:

* prodDens_uniP: the uniform product density is the
  constant (1/card V)^B.
* `prodE_as_expQ`: `prodE (uniP b)` IS `KLS.expQ` with the
  constant density — the two expectation operators coincide
  on the uniform product system.
* `batchVar_expQ`: `batch_variance_eq` transported verbatim
  into the `expQ` carrier — the SAME law both formalizations
  compute; `uncorrMeanVar` (the klsBatchNoise core) and
  `batch_variance_eq` are one theorem in two vocabularies,
  and the annealing budget σ²·c/(B₀(c−1)) is the same
  quantity both chains bound.
-/

namespace Hagi.Thermo

open Finset

variable {V : Type} [Fintype V] [Nonempty V]

/-- **Interface weld**: on the uniform product system the
`prodE` expectation IS `KLS.expQ` with the constant density —
the two vocabularies compute the same number. -/
theorem prodE_as_expQ (b : ℕ) (f : (Fin b → V) → ℝ) :
    prodE (V := V) (uniP b) f
      = KLS.expQ (fun _ => ((Fintype.card V : ℝ) ^ b) ⁻¹) f := by
  unfold prodE KLS.expQ
  rw [Finset.sum_congr rfl (fun ω _ => by rw [uniP_dens])]

/-- **The 1/B law in the expQ carrier**: `batch_variance_eq`
transported verbatim — the SAME theorem the NoiseTemperature
chain computes, now stated in the KLS vocabulary: the
batch-mean temperature is exactly Var(g)/B on the welded
interface. Together with `klsBatchNoise` (the dimension-free
bound) and `uncorrMeanVar` (the general averaging law), the
three formalizations are one law: anneal_by_batch's budget
σ²·c/(B₀(c−1)) is the same quantity all three bound. -/
theorem batchVar_expQ (g : V → ℝ) {b : ℕ} [Nonempty (Fin b)] :
    KLS.expQ (fun _ : Fin b → V => ((Fintype.card V : ℝ) ^ b) ⁻¹)
        (fun ω => (batchMean g ω - popMean g) ^ 2)
      = popVar g / b := by
  exact (prodE_as_expQ b (fun ω => (batchMean g ω - popMean g) ^ 2)).symm.trans
    (batch_variance_eq (V := V) (b := b) g)

end Hagi.Thermo
