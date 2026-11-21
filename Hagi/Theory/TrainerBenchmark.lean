/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Softmax

/-!
# Certified trainer benchmark (C497)

Roadmap C497 (`--mode vs-trainer` of `scripts/bench_bridge.py`):
mini-HAGI (the certified rational sandwich trainer, C491
family, trained on the LIVE HAGI_v2 `unified_ledger` corpus)
is compared against the real trainer — its holdout models'
measured `ce` labels are predicted by CERTIFIED predictions
(C495: disjoint sandwich intervals), not by point estimates.

## The soundness contract

`certified_forecast_sound`: if the certified sandwich
intervals of the holdout model are pairwise disjoint (the
C495 separation `hi a / ∑ lo < lo b / ∑ hi`), and the
model-reality (the true softmax) lies inside the certified
band (`BandDescribes`), then the certified forecast — the
argmax of the rational midpoint surrogate — coincides with
the argmax of the true ranking. Both orderings are derived;
no `ε` is needed.

## Honest pin (measurement premise)

`BandDescribes z lo hi` is a MEASUREMENT premise
(`Describes`-type): it is not proven here from the data. It
IS implied by the soundness hypotheses of
`Hagi.Theory.RationalSoftmax.rationalSoftmaxCert`
(`lo v ≤ e ^ z v ≤ hi v`), but on the benchmark the band is
accepted as the certified reading of the measured model —
the theorem's contribution is that disjointness then
transfers the certified forecast to the true ranking.

## Numeric example (real holdout)

The C497 run on the live ledger (31 usable models, 25 train
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
certified intervals (C495 separation) plus the
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
model ns_0019 (C497 run on the live ledger; `z` shifted by
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

end Hagi.Theory.TrainerBenchmark
