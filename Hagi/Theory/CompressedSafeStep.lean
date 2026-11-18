/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.StochasticSafeStep
import Hagi.Runtime.TernaryExact
import Hagi.Theory.EFTheory

/-!
# Compression-aware safe step with error budget (C389)

Audit A17 §5.3: the compression penalty lives INSIDE the safe step
— optimization and quantization stop being independent systems.
The controller knows how much of the descent margin is EATEN by
compression, and refuses when nothing survives.

The setting: the stored trajectory is COMPRESSED.  Both endpoints of
each step are quantized states, so the certified descent is measured
on the compressed trajectory — the only one that exists in memory.
Each endpoint pays one Lipschitz transport of the quantization error
`ε_q`, giving the exact additive penalty

  `L(compress(step θ η)) ≤ L(compress θ) − η·A + η²·C + 2·L_lip·ε_q`

(both transports used once, no cross terms dropped).  The penalty is
η-INDEPENDENT, so the optimal step size stays `A / (2C)` and the
certified drop becomes `A²/(4C) − 2·L_lip·ε_q`: the accept rule
requires this to be positive — the compression-aware REFUSAL
(`compressedRefusal`: when `A²/(4C) ≤ 2·L_lip·ε_q`, NO step size has
a positive certified margin; holding the state is the only sound
action, the C363/C388 `Hold` path).

The fractional form `A_eff = A − 2·L_lip·ε_q/η` was considered and
REJECTED as dishonest: the penalty does not scale with `η`; dividing
by `η` creates an artificial singularity at small steps and moves
the argmin for no mathematical reason.  The constant-offset form is
exact.

## EF comparison (C381)

Plain compression pays `2·L_lip·ε_q` per step — linear in the
horizon.  With error feedback the iterate deviation is the EXACT
endpoint identity `xC n − xF n = η•(e n − e 0)`
(`Hagi.Unified.ErrorFeedback.ef_iterate_shadow`, C381), so the
Lipschitz transport pays ONCE, at the endpoints: the penalty is
`L_lip·2·η·√B` under a residual barrier `nrm2 (e t) ≤ B`
(`Hagi.Unified.ThrComp.thrComp_barrier` instantiates
`B = card·τ²` absolutely) — CONSTANT in the horizon.  The crossover
`ef_crossover_ternary_thr`: the EF penalty beats the plain penalty
once `2·η·τ ≤ (s/2)·n` (the `√card` factors cancel exactly).

## Honest ledger: estimated vs derived vs binder

- BINDERS (premise-form, per-model): the Lipschitz constant `L_lip`
  (`transport`, the `gridQ_energy_bound` pattern).  The only PROVED
  Lipschitz law for the CE objective is logit-level
  (`Model.CEQuantized.ceOneHot_le_of_abs_sub_le`: one-hot CE is
  2-Lipschitz in a uniform logit displacement); a parameter-level
  `L_lip` needs the head's logit-map Lipschitz constant and stays a
  per-model premise.  The distance is an abstract symmetric
  pseudometric (`dist`); the Euclidean instantiation `dist2` below
  makes `ε_q = √card·s/2` a THEOREM for `qTern`
  (`ternaryCompress_l2_le`).
- DERIVED: the penalty `2·L_lip·ε_q`, the adjusted certified drop,
  the unchanged step size `A/(2C)`, the EF crossover.
- Integration (documented, not reproved): the C388 stochastic
  central step composes by the same algebra — its accept condition
  `0 < Â−r ∧ 0 < Ĉ+u` with the certified drop
  `(Â−r)²/(4(Ĉ+u))` folds the same constant penalty into the drop
  comparison; the refusal theorem there (`hold_refusal_safe`) covers
  the refusal path verbatim.

## Honest scope

- The compression operator itself is abstract (`compress` with the
  error binder `compress_err`); `ternaryCompress` is the concrete
  ternary instantiation, in-range only (`ternInRange` per
  coordinate — the saturation tail `satTail` is outside).
- The EF theorems take the C381 shadow identity as a premise (cite,
  not reprove — the StochasticSafeStep citing pattern), with the
  proved `thrComp_barrier` as the documented instantiation of the
  residual barrier.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.CompressedSafeStep

open Hagi.Theory.CEChain Hagi.Theory.StochasticSafeStep Hagi.Runtime
open Hagi.Unified.DescentCore

/-! ## Stage 1 — the compressed-parameter carrier -/

/-- The compression data of a safe step (C389): a deterministic
`UniversalSafeStep` carrier (C387) plus a compression operator with
its error budget.  The Lipschitz constant `lip` is a per-model
PREMISE binder (the `gridQ_energy_bound` pattern); the quantization
error `eps_q` bounds the displacement of every compressed state from
its exact state. -/
structure CompressedParams (Θ : Type) where
  /-- The deterministic safe-step carrier (loss, update, A, C, majorizer). -/
  carrier : UniversalSafeStep Θ
  /-- A symmetric pseudo-distance on parameter states. -/
  dist : Θ → Θ → ℝ
  /-- The distance is symmetric. -/
  dist_symm : ∀ a b : Θ, dist a b = dist b a
  /-- The distance is nonnegative. -/
  dist_nonneg : ∀ a b : Θ, 0 ≤ dist a b
  /-- The per-model Lipschitz constant of the loss in `dist`. -/
  lip : ℝ
  /-- The Lipschitz constant is nonnegative. -/
  lip_nonneg : 0 ≤ lip
  /-- The per-step quantization error budget. -/
  eps_q : ℝ
  /-- The error budget is nonnegative. -/
  eps_nonneg : 0 ≤ eps_q
  /-- The compression operator. -/
  compress : Θ → Θ
  /-- Lipschitz transport: the loss moves by at most `lip * dist`. -/
  transport : ∀ a b : Θ,
    carrier.loss a ≤ carrier.loss b + lip * dist a b
  /-- The compressed state is within `eps_q` of the exact state. -/
  compress_err : ∀ θ : Θ, dist θ (compress θ) ≤ eps_q

namespace CompressedParams

/-- One-endpoint Lipschitz transport: compressing a state costs at
most `lip * eps_q` of loss — the price of ONE quantized endpoint. -/
theorem lipschitz_transport (P : CompressedParams Θ) (θ : Θ) :
    P.carrier.loss (P.compress θ) ≤ P.carrier.loss θ + P.lip * P.eps_q := by
  have hbd : P.dist (P.compress θ) θ ≤ P.eps_q := by
    rw [P.dist_symm (P.compress θ) θ]; exact P.compress_err θ
  have hb : P.lip * P.dist (P.compress θ) θ ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left hbd P.lip_nonneg
  have h := P.transport (P.compress θ) θ
  linarith [h, hb]

/-- MAIN THEOREM (C389, audit 5.3): the safe step WITH the
compression penalty folded in.  Executing the step at the exact
state but reading BOTH endpoints from compressed storage, the loss
obeys the universal majorizer law with the exact additive penalty
`2·L_lip·ε_q` — one transport per endpoint, no cross terms.  The
system knows how much descent margin compression eats. -/
theorem compressed_safe_step (P : CompressedParams Θ) (θ : Θ)
    (η : ℝ) (hη : 0 ≤ η) :
    P.carrier.loss (P.compress (P.carrier.step θ η))
      ≤ P.carrier.loss (P.compress θ) - η * P.carrier.alignment θ
        + η ^ 2 * P.carrier.curvature θ + 2 * P.lip * P.eps_q := by
  have hbdS : P.dist (P.compress (P.carrier.step θ η))
      (P.carrier.step θ η) ≤ P.eps_q := by
    rw [P.dist_symm (P.compress (P.carrier.step θ η)) (P.carrier.step θ η)]
    exact P.compress_err (P.carrier.step θ η)
  have hnear0 : P.lip * P.dist θ (P.compress θ) ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left (P.compress_err θ) P.lip_nonneg
  have hnear : P.lip * P.dist (P.compress θ) θ ≤ P.lip * P.eps_q := by
    rw [P.dist_symm (P.compress θ) θ]
    exact hnear0
  have hfar : P.lip * P.dist (P.compress (P.carrier.step θ η))
      (P.carrier.step θ η) ≤ P.lip * P.eps_q :=
    mul_le_mul_of_nonneg_left hbdS P.lip_nonneg
  have h1 := P.transport θ (P.compress θ)
  have h2 := P.carrier.majorizes θ η hη
  have h3 := P.transport (P.compress (P.carrier.step θ η))
    (P.carrier.step θ η)
  linarith [h1, h2, h3, hnear0, hnear, hfar]

/-- The compression-aware certified drop: the universal drop
`A²/(4C)` minus the exact penalty `2·L_lip·ε_q`.  The optimal step
size is UNCHANGED (`universalStepSize`, `A/(2C)`) because the
penalty does not depend on `η`. -/
noncomputable def compressedCertifiedDrop (P : CompressedParams Θ)
    (θ : Θ) : ℝ :=
  (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
    - 2 * P.lip * P.eps_q

/-- The accept path: when the compression-aware certified drop is
positive (the penalty has NOT eaten the descent margin), the optimal
step certifies exactly that drop on the compressed trajectory. -/
theorem compressed_descent (P : CompressedParams Θ) (θ : Θ)
    (hC : 0 < P.carrier.curvature θ)
    (hdrop : 0 < compressedCertifiedDrop P θ) :
    P.carrier.loss (P.compress
        (P.carrier.step θ (universalStepSize P.carrier θ)))
      ≤ P.carrier.loss (P.compress θ) - compressedCertifiedDrop P θ := by
  have hη : 0 ≤ universalStepSize P.carrier θ :=
    div_nonneg (P.carrier.alignment_nonneg θ) (by positivity)
  have h := compressed_safe_step P θ (universalStepSize P.carrier θ) hη
  have hkey : universalStepSize P.carrier θ * P.carrier.alignment θ
      - (universalStepSize P.carrier θ) ^ 2 * P.carrier.curvature θ
      = (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ) := by
    simp only [universalStepSize]
    field_simp
    ring
  unfold compressedCertifiedDrop at hdrop ⊢
  linarith

/-- The REFUSAL direction (compression-aware): when the penalty eats
the whole descent margin (`A²/(4C) ≤ 2·L_lip·ε_q`), NO step size has
a positive certified margin — the guaranteed descent never beats the
penalty, so the controller holds the state entirely (the safe `Hold`
path, C363/C388 `hold_refusal_safe`).  Exactly the audit demand:
ternary compression is enabled only where it provably does not
destroy the descent budget. -/
theorem compressedRefusal (P : CompressedParams Θ) (θ : Θ)
    (hC : 0 < P.carrier.curvature θ)
    (heat : (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
      ≤ 2 * P.lip * P.eps_q) (η : ℝ) (hη : 0 ≤ η) :
    η * P.carrier.alignment θ - η ^ 2 * P.carrier.curvature θ
      ≤ 2 * P.lip * P.eps_q := by
  have hkey : (P.carrier.alignment θ) ^ 2 / (4 * P.carrier.curvature θ)
      - (η * P.carrier.alignment θ
          - η ^ 2 * P.carrier.curvature θ)
      = P.carrier.curvature θ
          * (η - P.carrier.alignment θ / (2 * P.carrier.curvature θ)) ^ 2 := by
    field_simp
    ring
  have hsq : (0:ℝ) ≤ P.carrier.curvature θ
      * (η - P.carrier.alignment θ / (2 * P.carrier.curvature θ)) ^ 2 :=
    mul_nonneg hC.le (sq_nonneg _)
  linarith

end CompressedParams

/-! ## Stage 2 — the ternary instantiation of `ε_q` -/

variable {k : Type} [Fintype k]

/-- The concrete ternary compression operator: coordinate-wise
`qTern s` nearest-grid rounding (the `Runtime.TernaryExact`
quantizer). -/
noncomputable def ternaryCompress (s : ℝ) (θ : k → ℝ) : k → ℝ :=
  fun i => qTern s (θ i)

/-- The Euclidean pseudo-distance on parameter vectors (the
instantiation of `CompressedParams.dist` for coordinate quantizers):
the root of the summed squared coordinate displacement. -/
noncomputable def dist2 (x y : k → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- The ternary error budget is a THEOREM: compressing every
coordinate in range with `qTern` displaces the vector by at most
`√card · s/2` in `dist2` — half a ternary step per coordinate,
squared and summed.  This is the concrete `ε_q` binder for the
ternary instantiation. -/
theorem ternaryCompress_l2_le (s : ℝ) (hs : 0 < s) (θ : k → ℝ)
    (hin : ∀ i, ternInRange s (θ i)) :
    dist2 (ternaryCompress s θ) θ
      ≤ Real.sqrt ((Fintype.card k : ℝ)) * (s / 2) := by
  have hle : ∀ i : k, (qTern s (θ i) - θ i) ^ 2 ≤ (s / 2) ^ 2 :=
    fun i => by
      have h := qTern_error_in s (θ i) hs (hin i)
      have h2 := abs_le.mp h
      nlinarith [h2.1, h2.2, sq_nonneg (s / 2)]
  have hsq : ∑ i, (qTern s (θ i) - θ i) ^ 2
      ≤ (Fintype.card k : ℝ) * (s / 2) ^ 2 := by
    calc ∑ i, (qTern s (θ i) - θ i) ^ 2
        ≤ ∑ i, (s / 2) ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = (Fintype.card k : ℝ) * (s / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : Real.sqrt ((Fintype.card k : ℝ) * (s / 2) ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * (s / 2) := by
    rw [Real.sqrt_mul (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  unfold dist2 ternaryCompress
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq hsplit)

/-! ## Stage 3 — the trajectory bounds: plain vs EF -/

/-- The full (uncompressed) trajectory telescope: each step obeys
the majorizer, so after `n` steps the loss is below the start minus
the summed per-step margins `η·A − η²·C`. -/
theorem full_step_telescope (U : UniversalSafeStep Θ)
    (θF : ℕ → Θ) (η : ℝ) (hη : 0 ≤ η)
    (hstep : ∀ t : ℕ, θF (t + 1) = U.step (θF t) η) (n : ℕ) :
    U.loss (θF n) ≤ U.loss (θF 0)
      - ∑ t ∈ Finset.range n,
          (η * U.alignment (θF t) - η ^ 2 * U.curvature (θF t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstepn : U.loss (θF (n + 1)) = U.loss (U.step (θF n) η) := by
      rw [hstep n]
    have hm := U.majorizes (θF n) η hη
    rw [hstepn, Finset.sum_range_succ]
    linarith

/-- The plain compressed trajectory bound: with the exact
trajectory `θF` following the majorizer steps and EVERY stored
iterate compressed (`hstore`), the penalty is paid at EVERY step —
`2·L_lip·ε_q` per step, LINEAR in the horizon. -/
theorem plain_compressed_trajectory (P : CompressedParams Θ)
    (θF : ℕ → Θ) (η : ℝ) (hη : 0 ≤ η)
    (hstepF : ∀ t : ℕ, θF (t + 1) = P.carrier.step (θF t) η)
    (θq : ℕ → Θ) (hstore : ∀ t : ℕ, θq t = P.compress (θF t))
    (n : ℕ) :
    P.carrier.loss (θq n) ≤ P.carrier.loss (θq 0)
      - ∑ t ∈ Finset.range n,
          (η * P.carrier.alignment (θF t)
            - η ^ 2 * P.carrier.curvature (θF t))
      + 2 * P.lip * P.eps_q * (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstoren : P.carrier.loss (θq (n + 1))
        = P.carrier.loss (P.compress (P.carrier.step (θF n) η)) := by
      rw [hstore (n + 1), hstepF n]
    have hstoren0 : P.carrier.loss (θq n)
        = P.carrier.loss (P.compress (θF n)) := by
      rw [hstore n]
    have hm := CompressedParams.compressed_safe_step P (θF n) η hη
    rw [hstoren, Finset.sum_range_succ]
    rw [hstoren0] at ih
    have hcast : ((n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by norm_num
    rw [hcast]
    linarith

/-- The EF endpoint shadow in `dist2`: if the compressed iterate
deviates from the full one by the C381 identity
`xC n − xF n = η•(e n − e 0)` and the residual carries a barrier
`nrm2 (e t) ≤ B` (instantiated by the PROVED
`Hagi.Unified.ThrComp.thrComp_barrier`), the parameter displacement
is at most `2·η·√B` — CONSTANT in the horizon `n`. -/
theorem ef_shadow_dist2 (η : ℝ) (hη : 0 ≤ η)
    (e : ℕ → k → ℝ) (B : ℝ) (hB : ∀ t : ℕ, nrm2 (e t) ≤ B)
    (xC xF : ℕ → k → ℝ)
    (hshadow : ∀ n : ℕ, xC n - xF n = η • (e n - e 0)) (n : ℕ) :
    dist2 (xC n) (xF n) ≤ 2 * η * Real.sqrt B := by
  have hnrm : ∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2
      = η ^ 2 * nrm2 (e n - e 0) :=
    Hagi.Unified.ThrComp.nrm2_smul (k := k) η (e n - e 0)
  have hcoord : ∀ i : k, (e n i - e 0 i) ^ 2
      ≤ 2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (e n i + e 0 i)]
  have hn0 : (0:ℝ) ≤ nrm2 (e n - e 0) := by
    unfold nrm2
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : nrm2 (e n - e 0) ≤ 4 * B := by
    have h1 : nrm2 (e n - e 0)
        ≤ ∑ i, (2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2) :=
      Finset.sum_le_sum fun i _ => hcoord i
    have h2 : ∑ i, (2 * (e n i) ^ 2 + 2 * (e 0 i) ^ 2)
        = 2 * nrm2 (e n) + 2 * nrm2 (e 0) := by
      unfold nrm2
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]
    have h3 : 2 * nrm2 (e n) + 2 * nrm2 (e 0) ≤ 4 * B := by
      nlinarith [hB n, hB 0]
    linarith [h1, h2, h3]
  have hnn : (0:ℝ) ≤ 4 * B := by nlinarith [hB n, hn0]
  have hfour : Real.sqrt (4 * B) = 2 * Real.sqrt B := by
    have h := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) B
    rw [h]; norm_num
  have hfinal : Real.sqrt (η ^ 2 * nrm2 (e n - e 0))
      ≤ Real.sqrt (η ^ 2 * (4 * B)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsplit : Real.sqrt (η ^ 2 * (4 * B))
      = η * (2 * Real.sqrt B) := by
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hη, hfour]
  unfold dist2
  rw [show ∑ i, (xC n i - xF n i) ^ 2
      = ∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2 from
    Finset.sum_congr rfl fun i _ => by
      rw [show xC n i - xF n i = (xC n - xF n) i from rfl, hshadow n]]
  calc Real.sqrt (∑ i, ((η : ℝ) • (e n - e 0)) i ^ 2)
      = Real.sqrt (η ^ 2 * nrm2 (e n - e 0)) := by rw [hnrm]
    _ ≤ Real.sqrt (η ^ 2 * (4 * B)) := hfinal
    _ = 2 * η * Real.sqrt B := by rw [hsplit]; ring

/-- The EF compressed step bound: with error feedback the Lipschitz
transport pays only at the ENDPOINTS — the total penalty is
`L_lip·2·η·√B`, CONSTANT in the horizon (the C381 exact shadow
identity, cited as the premise `hshadow`; `hdist` instantiates the
abstract distance by `dist2`). -/
theorem ef_compressed_step_bound
    (P : CompressedParams (k → ℝ))
    (hdist : ∀ x y : k → ℝ, P.dist x y ≤ dist2 x y)
    (η : ℝ) (hη : 0 ≤ η)
    (θF : ℕ → k → ℝ)
    (hstepF : ∀ t : ℕ, θF (t + 1) = P.carrier.step (θF t) η)
    (xC : ℕ → k → ℝ) (e : ℕ → k → ℝ)
    (hshadow : ∀ n : ℕ, xC n - θF n = η • (e n - e 0))
    (B : ℝ) (hB : ∀ t : ℕ, nrm2 (e t) ≤ B) (n : ℕ) :
    P.carrier.loss (xC n) ≤ P.carrier.loss (θF 0)
      - ∑ t ∈ Finset.range n,
          (η * P.carrier.alignment (θF t)
            - η ^ 2 * P.carrier.curvature (θF t))
      + P.lip * (2 * η * Real.sqrt B) := by
  have htele := full_step_telescope P.carrier θF η hη hstepF n
  have hd : P.dist (xC n) (θF n) ≤ 2 * η * Real.sqrt B :=
    le_trans (hdist (xC n) (θF n))
      (ef_shadow_dist2 η hη e B hB xC θF hshadow n)
  have htr := P.transport (xC n) (θF n)
  have hpen : P.lip * P.dist (xC n) (θF n)
      ≤ P.lip * (2 * η * Real.sqrt B) :=
    mul_le_mul_of_nonneg_left hd P.lip_nonneg
  linarith

/-- The quantitative EF-vs-plain penalty comparison (abstract form):
when the endpoint shadow displacement `2·η·√B` fits inside `n`
per-step error budgets `ε_q·n`, the EF penalty is below the plain
compression penalty — the abstract crossover. -/
theorem ef_penalty_le_plain (P : CompressedParams Θ)
    (η B : ℝ) (n : ℕ)
    (hcrossover : 2 * η * Real.sqrt B ≤ P.eps_q * (n : ℝ)) :
    P.lip * (2 * η * Real.sqrt B)
      ≤ 2 * P.lip * P.eps_q * (n : ℝ) := by
  have h3 : P.lip * (2 * η * Real.sqrt B)
      ≤ P.lip * (P.eps_q * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hcrossover P.lip_nonneg
  have h5 : P.lip * (P.eps_q * (n : ℝ)) + P.lip * (P.eps_q * (n : ℝ))
      = 2 * P.lip * P.eps_q * (n : ℝ) := by ring
  have hge : (0:ℝ) ≤ P.lip * (P.eps_q * (n : ℝ)) :=
    mul_nonneg P.lip_nonneg
      (mul_nonneg P.eps_nonneg (Nat.cast_nonneg n))
  linarith [h3, h5, hge]

/-- The INSTANTIATED crossover (EF beats plain, both constants are
theorems): with the threshold compressor's absolute residual barrier
`B = card·τ²` (`Hagi.Unified.ThrComp.thrComp_barrier`) and the
ternary budget `ε_q = √card·s/2`
(`ternaryCompress_l2_le`), the `√card` factors cancel and the EF
penalty beats the plain ternary penalty exactly when
`2·η·τ ≤ (s/2)·n` — a half-step of ternary grid per step against
the residual barrier per step. -/
theorem ef_crossover_ternary_thr (P : CompressedParams (k → ℝ))
    (hcard : (Fintype.card k : ℝ) ≠ 0) (η τ s : ℝ)
    (hτ : 0 < τ) (hs : 0 < s) (n : ℕ)
    (hcrossover : 2 * η * τ ≤ (s / 2) * (n : ℝ)) :
    P.lip * (2 * η * Real.sqrt ((Fintype.card k : ℝ) * τ ^ 2))
      ≤ P.lip * (Real.sqrt ((Fintype.card k : ℝ)) * (s / 2))
          * (n : ℝ) := by
  have hcardpos : (0:ℝ) < Fintype.card k := by positivity
  have hsq : Real.sqrt ((Fintype.card k : ℝ) * τ ^ 2)
      = Real.sqrt ((Fintype.card k : ℝ)) * τ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hτ.le]
  rw [hsq]
  have hl : (0:ℝ) ≤ P.lip * Real.sqrt ((Fintype.card k : ℝ)) :=
    mul_nonneg P.lip_nonneg (Real.sqrt_nonneg _)
  calc P.lip * (2 * η * (Real.sqrt ((Fintype.card k : ℝ)) * τ))
      = P.lip * Real.sqrt ((Fintype.card k : ℝ)) * (2 * η * τ) := by
        ring
    _ ≤ P.lip * Real.sqrt ((Fintype.card k : ℝ))
        * ((s / 2) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcrossover hl
    _ = P.lip * (Real.sqrt ((Fintype.card k : ℝ)) * (s / 2))
        * (n : ℝ) := by
        ring

end Hagi.Theory.CompressedSafeStep
