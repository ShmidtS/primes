/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Runtime.TernaryExact
import Hagi.Benchmarks.TernaryWitness

set_option linter.style.header false

/-!
# Certified ternary quantization jump (C443)

The certified ternary training cycle (scripts/bench_bridge.py
`--mode cert-tern`) runs gradient steps of the C442 rational-CE
surrogate, then ONE ternary quantization jump
`w → s*·roundTern(w/s₀)` with the LS-optimal scale
`s* = (Σ q·w)/(Σ q·q)` (`Hagi.Energy.lsScale_optimal`, exact
`Fraction` arithmetic), and finally certified finetune gradient
steps on the quantized weights.  This module is the proof-level
bridge for the jump:

* `ternJumpStep` — the step record a trainer emits for a jump
  (declared drop = the readout difference `obj − obj'`);
* `ternary_jump_checkStep` — the ACCEPTANCE CRITERION proved
  admissive: the corpus inequality `E' ≤ k·s²/8 < E` (the
  `quantOpt_energy_bound` / `quant_jump_honest` premise form) makes
  the emitted jump step pass the executable checker — the SAME
  inequality the Python trainer evaluates exactly;
* `ternary_jump_energy` — the ℝ-side ceiling restated on `Fin m`:
  under the in-range premise the quantized post-state sits below
  `k·s²/8`, feeding the bridge premise;
* `ternary_hold_rejected` — a rejected jump (HOLD: weights
  unchanged, `drop = 0`) can NEVER pass `checkStep`, which demands
  strict `0 < drop`: the machine-checked reason hold steps are
  excluded from the emitted trajectory and logged separately.

## Honest boundaries (pins)

1. The Python trainer's acceptance is the exact strict drop
   `obj − obj' > 0`; the ceiling `k·s²/8` is reported telemetry
   (corpus-form distortion bound), not an admission input.
2. `lsScale_optimal`-style optimality of `s*` holds for the FIXED
   pattern `q`; joint optimality over `(q, s)` is not claimed.
3. The `ℚ` readouts of a concrete run are exact rationals (the
   trainer computes in `Fraction`), so casting the real-side
   ceiling facts to the executable layer is faithful.
-/

namespace Hagi.Theory.CertTernaryJump

open Hagi.Runtime Hagi.Unified.TernaryWitness Hagi.Unified.DescentCoreQuad

/-! ## The jump step record -/

/-- The step record a trainer emits for a ternary jump: the
declared drop is exactly the readout difference `obj − obj'`
(nothing else is claimed). -/
def ternJumpStep (E E' bud bud' rsk rsk' : ℚ) : CertStepData :=
  ⟨E, E', E - E', bud, bud', rsk, rsk'⟩

/-! ## The acceptance criterion is admissive -/

/-- **Certified ternary jump acceptance**: if the post-jump energy
readout sits below the corpus ceiling `k·s²/8` while the pre-jump
  `quantOpt_energy_bound` / quant_jump_honest premise form, the SAME
  inequality the Python trainer evaluates exactly in `Fraction` — then
  the emitted jump step passes the executable checker (strict positive
  drop included).
The budget/risk readout obligations are the checker's usual
nonnegativity demands. -/
theorem ternary_jump_checkStep {k : ℕ} {s : ℚ}
    {E E' bud bud' rsk rsk' : ℚ} (hbud : 0 ≤ bud') (hrsk : 0 ≤ rsk')
    (hceil : E' ≤ (k : ℚ) * s ^ 2 / 8)
    (hxe : (k : ℚ) * s ^ 2 / 8 < E) :
    checkStep (ternJumpStep E E' bud bud' rsk rsk') = true := by
  have hdrop : 0 < E - E' := by linarith
  simp only [checkStep, ternJumpStep, Bool.and_eq_true]
  exact ⟨⟨⟨decide_eq_true hdrop, by norm_num⟩, decide_eq_true hbud⟩,
    decide_eq_true hrsk⟩

/-! ## The ℝ-side ceiling (corpus link) -/

/-- The corpus ceiling on `Fin m`: under the in-range premise the
ternary-quantized optimum's energy is at most `m·s²/8` —
`quantOpt_energy_bound` restated, i.e. the real-side source of the
`hceil` premise feeding `ternary_jump_checkStep` whenever the
run's energy readouts are rational (they are: `Fraction` trainer). -/
theorem ternary_jump_energy {m : ℕ} (s : ℝ) (hs : 0 < s)
    (a : Fin m → ℝ) (hin : ∀ i, ternInRange s (a i)) :
    quadE a (quantOpt s a) ≤ (Fintype.card (Fin m) : ℝ) * s ^ 2 / 8 :=
  quantOpt_energy_bound s hs a hin

/-! ## Holds can never ride the trajectory -/

/-- A rejected jump is a HOLD: an identity transition with declared
`drop = 0`. The executable checker — which demands strict
`0 < drop` — rejects it: this is the machine-checked reason the
trainer EXCLUDES hold steps from the emitted trajectory and logs
them separately (bench_bridge.py `holds` telemetry). -/
theorem ternary_hold_rejected (E bud rsk : ℚ) :
    checkStep (ternJumpStep E E bud bud rsk rsk) = false := by
  simp [checkStep, ternJumpStep]

end Hagi.Theory.CertTernaryJump
