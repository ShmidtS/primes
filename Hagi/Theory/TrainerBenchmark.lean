/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Softmax

/-!
# Certified trainer benchmark

Bench (`--mode vs-trainer` of `scripts/bench_bridge.py`):
mini-HAGI (the certified rational sandwich trainer
family, trained on the LIVE HAGI_v2 `unified_ledger` corpus)
is compared against the real trainer — its holdout models'
measured `ce` labels are predicted by CERTIFIED predictions
(disjoint sandwich intervals), not by point estimates.

## The soundness contract

`certified_forecast_sound`: if the certified sandwich
intervals of the holdout model are pairwise disjoint (the
 separation `hi a / ∑ lo < lo b / ∑ hi`), and the
model-reality (the true softmax) lies inside the certified
band (`BandDescribes`), then the certified forecast — the
argmax of the rational midpoint surrogate — coincides with
the argmax of the true ranking. Both orderings are derived;
no `ε` is needed.

## Honest pin (measurement premise) — CLOSED

`BandDescribes z lo hi` was a MEASUREMENT premise
(`Describes`-type). closes the measurement bridge as a
theorem: it IS implied by the soundness hypotheses of
`Hagi.Theory.RationalSoftmax.rationalSoftmaxCert`
(`lo v ≤ e ^ z v ≤ hi v`) — `bandDescribes_of_pointwise`
below — and the bench bands (Bernoulli shape on
max-shifted logits) satisfy those hypotheses exactly
(`bernoulliBandDescribes`). The theorem's contribution —
disjointness transfers the certified forecast to the true
ranking — is unchanged; the premise is no longer data-
dependent for genuine certified bands. The `--mode
band-check` bench is the empirical drift detector
(implementation vs theorem).

## Numeric example (real holdout)

The run on the live ledger (31 usable models, 25 train
/ 6 holdout, 8 certified training steps) produces for the
holdout model ns_0019 the exact rational sandwich bounds
below; `trainer_benchmark_sep_example` certifies their
disjointness by `norm_num`, and applying
`certified_forecast_sound` yields the certified forecast
(class 0) — the correct label of that model.
-/

set_option linter.style.header false

namespace Hagi.Theory.TrainerBenchmark

open Real Hagi.Prelude Hagi.Theory.RationalSoftmax
open Hagi.Theory.SandwichMonotone

variable {V : Type} [Fintype V] [Nonempty V]

/-- The model-reality-inside-band premise: the true softmax
value of every class lies inside the NORMALIZED certified
sandwich band `[lo v / ∑ hi, hi v / ∑ lo]`. A measurement
(`Describes`-type) premise — see the module docstring. -/
def BandDescribes (z lo hi : V → ℝ) : Prop :=
  ∀ v, lo v / ∑ w, hi w ≤ softDef z v ∧
       softDef z v ≤ hi v / ∑ w, lo w

omit [Nonempty V] in
/-- Certified forecast soundness: pairwise disjoint
certified intervals (separation) plus the
reality-inside-band measurement make the certified forecast
(the rational midpoint argmax) coincide with the argmax of
the true ranking — both the surrogate and the true softmax
orderings put `b` strictly above every competitor. -/
theorem certified_forecast_sound {z lo hi : V → ℝ} {b : V}
    (hband : BandDescribes z lo hi)
    (hsep : ∀ a, a ≠ b →
      hi a / ∑ w, lo w < lo b / ∑ w, hi w) :
    ∀ a, a ≠ b →
      sandwichMid lo hi a < sandwichMid lo hi b ∧
      softDef z a < softDef z b := by
  intro a ha
  obtain ⟨hla, hha⟩ := hband a
  obtain ⟨hlb, hhb⟩ := hband b
  have hsep' := hsep a ha
  -- surrogate: mid a ≤ hi a / ∑ lo < lo b / ∑ hi ≤ mid b,
  -- where the endpoint orderings come from the band itself
  have hmid_le : lo a / ∑ w, hi w ≤ hi a / ∑ w, lo w :=
    le_trans hla hha
  have hmid_ge : lo b / ∑ w, hi w ≤ hi b / ∑ w, lo w :=
    le_trans hlb hhb
  refine ⟨?_, lt_of_le_of_lt hha (lt_of_lt_of_le hsep' hlb)⟩
  unfold sandwichMid
  linarith

/-! ## Numeric example: the real holdout model ns_0019 -/

/-- The exact rational lower sandwich bounds of the holdout
model ns_0019 (run on the live ledger; `z` shifted by
its max, so the class-0 logit bound is exactly `1`). -/
noncomputable def loTB : Bool → ℝ := fun v =>
  if v then 13392445265761 / 16000000000000 else 1

/-- The exact rational upper sandwich bounds of the same
holdout model. -/
noncomputable def hiTB : Bool → ℝ := fun v =>
  if v then 16000000000000 / 18970981313761 else 1

/-- The certified intervals of ns_0019 are disjoint: the
class-1 upper endpoint `hi_1 / (lo_0 + lo_1)` is strictly
below the class-0 lower endpoint `lo_0 / (hi_0 + hi_1)`
(≈ 0.4591 < 0.5425), certified by `norm_num` on the literal
rationals. -/
theorem trainer_benchmark_sep_example :
    hiTB true / ∑ w, loTB w < loTB false / ∑ w, hiTB w := by
  norm_num [loTB, hiTB]

/-- The certified forecast application: given the measured
band premise on the real holdout model ns_0019, the
certified forecast (midpoint argmax) is class `false`, and
it coincides with the argmax of the true ranking. The
measurement premise is a hypothesis — the honest pin of this
module. -/
example (z : Bool → ℝ) (hband : BandDescribes z loTB hiTB) :
    ∀ a, a ≠ false →
      sandwichMid loTB hiTB a < sandwichMid loTB hiTB false ∧
      softDef z a < softDef z false :=
  certified_forecast_sound hband
    (by intro a ha; cases a; exact absurd rfl ha; exact
      trainer_benchmark_sep_example)

/-! ## The measurement bridge: BandDescribes is a theorem

The pinned measurement premise closes one layer down: the
pointwise certified exponential sandwich implies the
normalized band-describes property, and the bench band shape
(bench band builder) is an
instance. -/

/-- Softmax is shift-invariant: subtracting a constant from
 every logit multiplies numerator and denominator by the
 same exponential factor, so `softDef` is unchanged. -/
theorem softDef_shift (z : V → ℝ) (c : ℝ) (v : V) :
    softDef (fun w => z w - c) v = softDef z v := by
  have hsum : ∑ w, Real.exp (z w - c)
      = Real.exp (-c) * ∑ w, Real.exp (z w) := by
    simp only [Real.exp_sub, Real.exp_neg, div_eq_inv_mul,
      Finset.mul_sum]
  show Real.exp (z v - c) / _ = Real.exp (z v) / _
  rw [hsum, Real.exp_sub, Real.exp_neg]
  field_simp

/-- The measurement bridge: if `lo ≤ e ^ (z ·) ≤ hi` holds
POINTWISE (with `0 < lo`), then the normalized certified
band describes the true softmax of EVERY class — exactly the
`BandDescribes` premise of `certified_forecast_sound`, now
derived instead of assumed. -/
theorem bandDescribes_of_pointwise {z lo hi : V → ℝ}
    (hlo : ∀ v, lo v ≤ Real.exp (z v)) (hlo0 : ∀ v, 0 < lo v)
    (hhi : ∀ v, Real.exp (z v) ≤ hi v) :
    BandDescribes z lo hi :=
  fun v => rationalSoftmaxCert hlo hlo0 hhi v

/-- The bench band shape describes: the bands on
max-shifted logits — `lo v = (1 + s v / n) ^ n`,
`hi v = 1 / (1 - s v / n) ^ n` where `s v = z v - z b` and
`b` is any logit maximizer — satisfy the pointwise sandwich
(`expLower_le_exp`, `exp_le_expUpper_inv`), hence
`BandDescribes`. The strict range premise `-n < s v` mirrors
the bench range guard (the cs_terms_nm builder HOLDs outside
it), and
gives `0 < lo`. -/
theorem bernoulliBandDescribes {n : ℕ} (hn : 0 < n)
    {z : V → ℝ} {b : V} (hmax : ∀ w, z w ≤ z b)
    (hgt : ∀ w, -n < z w - z b) :
    BandDescribes z
      (fun v => (1 + (z v - z b) / n) ^ n)
      (fun v => 1 / (1 - (z v - z b) / n) ^ n) := by
  have hnR : (0:ℝ) < n := by positivity
  have key := bandDescribes_of_pointwise
    (z := fun w => z w - z b)
    (fun v => expLower_le_exp hn (by have := hgt v; linarith))
    (fun v => pow_pos (by
      have h := hgt v
      have h2 : (-1:ℝ) < (z v - z b) / n := by
        rw [lt_div_iff₀ hnR]; linarith
      linarith) n)
    (fun v => exp_le_expUpper_inv hn (by
      have hb := hmax v
      linarith))
  unfold BandDescribes at key ⊢
  simpa only [softDef_shift z (z b)] using key

end Hagi.Theory.TrainerBenchmark
