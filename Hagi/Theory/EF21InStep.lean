/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Optimization.EF21Quantizer

set_option linter.style.header false

/-!
# EF21 in-step quantized training loop (C474)

The certified training cycle (scripts/bench_bridge.py `--mode
ef21-step`) quantizes the update INSIDE every gradient step with
error feedback — unlike the C443 post-hoc jump (`--mode cert-tern`):

  `m_t = g_t + e_t`      exact gradient plus accumulated residual
  `d_t = Q (m_t)`        compressed direction (ternary quantizer)
  `e_{t+1} = m_t − d_t`  error feedback (residual carried forward)
  trial step `θ' = θ − η • d_t`, admitted ONLY by the exact certified
  criterion `drop > 0` (plus the full `checkStep` mirror); a rejected
  trial (drop ≤ 0, possibly NEGATIVE) is a HOLD: weights and residual
  unchanged, the step is excluded from the trajectory.

This module carries the proof-level identities of that loop:

* `ef21_instep_residual` — the recursion identity `e_{t+1} = m_t − d_t`;
* `ef21_instep_telescope` — the EXACT vector telescope (the EF
  promise): `Σ d_t = Σ g_t + e_0 − e_T` — the accumulated compressed
  update equals the accumulated exact gradient plus the endpoint
  residual;
* `ef21_instep_energy_split` / `ef21_instep_sum_energy` — the
  projection-type energy split `Σᵢ (m t i)² ≤ 2·Σᵢ (d t i)² +
  2·Σᵢ (e (t+1) i)²` (a pointwise identity consequence of
  `e_{t+1} = m_t − d_t`, no compressor assumption);
* `ef21_instep_residual_inexact` — the inexact floor: an
  `IsInexactCompressor Q α ε` bounds the residual energy by
  `((1−α)·‖m_t‖₂ + ε)²`;
* `trajObj` + `ef21_bench_valid` — the bench bridge: a trajectory
  passing the executable `checkTrajectory` telescopes — the final
  objective is at most the start minus the sum of declared drops
  (ℚ-level, no system metrics needed);
* `ef21_reject_hold` — a rejected trial (declared `drop ≤ 0`,
  including the negative-drop case) can NEVER pass `checkStep`:
  the machine-checked reason rejected steps are excluded from the
  emitted trajectory and logged as reject telemetry.

## Honest boundaries (pins)

1. The ternary quantizer is NOT contractive for any `α ∈ (0, 1]`
   (`Hagi.Optimization.EF21Quantizer.qTernVec_not_contractive`), so
   the EF21 Lyapunov descent / linear-rate guarantees do NOT
   transfer automatically. This module claims ONLY the exact
   identities above and the inexact floor; no contraction, no rate.
2. The telescope is stated as a CONDITIONAL theorem under the
   recursion hypothesis `hE` — i.e. for the subsequence of executed
   steps. A rejected trial consumes neither weights nor residual, so
   the Python loop's recursion runs on accepted steps only; rejected
   `m_t` are burned (honest reject semantics, logged in telemetry).
3. `ef21_bench_valid` bounds by DECLARED drops; the trainer emits
   `drop = obj − obj'` exactly, and `checkStep` demands
   `drop ≤ obj − obj'`, so declared ≤ actual never helps the trainer.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Hagi.Theory.EF21InStep

open Hagi.Runtime
open Finset

/-! ## The recursion identities (squared-sum carrier `Fin n → ℝ`) -/

variable {n : Type*} [Fintype n]
variable (Q : (n → ℝ) → (n → ℝ)) (g m e d : ℕ → (n → ℝ))

/-- The EF21 in-step recursion residual: under the update
`e_{t+1} = m_t − Q (m_t)` with `d_t = Q (m_t)`, the residual is
exactly the unexecuted part of the message vector. -/
theorem ef21_instep_residual (hE : ∀ t, e (t + 1) = m t - Q (m t))
    (hd : ∀ t, d t = Q (m t)) (t : ℕ) :
    e (t + 1) = m t - d t := by
  rw [hE t, ← hd t]

/-- The EXACT vector telescope of the in-step loop (the EF promise):
if `m_t = g_t + e_t`, `d_t = Q (m_t)` and the residual evolves by
`e_{t+1} = m_t − Q (m_t)`, then the accumulated compressed update
equals the accumulated exact gradient plus the endpoint residual:
`Σ_{t<T} d_t = Σ_{t<T} g_t + e_0 − e_T`.  No compressor assumption —
pure telescoping (the `Hagi.Step.ErrorFeedback.ef_cumulative_exact`
pattern on the squared-sum carrier). -/
theorem ef21_instep_telescope
    (hm : ∀ t, m t = g t + e t)
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (T : ℕ) :
    ∑ t ∈ range T, d t = ∑ t ∈ range T, g t + e 0 - e T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ih, hd T]
    have hE' := hE T
    rw [hm T] at hE'
    have hdT : Q (m T) = g T + e T - e (T + 1) := by
      rw [hE', hm T]; abel
    rw [hdT]
    abel

/-- The projection-type energy split, one step: the message energy
decomposes against the compressed direction and the residual —
`Σᵢ (m_t i)² ≤ 2·Σᵢ (d_t i)² + 2·Σᵢ (e_{t+1} i)²`.  This is the
pointwise identity consequence of `e_{t+1} = m_t − d_t` (i.e.
`(x + y)² ≤ 2x² + 2y²` via `0 ≤ (x − y)²`); NO compressor assumption. -/
theorem ef21_instep_energy_split
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (t : ℕ) :
    ∑ i, (m t i) ^ 2
      ≤ 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2 := by
  have h1 : ∀ i : n, (m t i) ^ 2
      ≤ 2 * (d t i) ^ 2 + 2 * (e (t + 1) i) ^ 2 := by
    intro i
    have hE' := congrFun (hE t) i
    simp only [Pi.sub_apply] at hE'
    have hd' := congrFun (hd t) i
    rw [← hd'] at hE'
    have h2 : m t i = d t i + e (t + 1) i := by
      rw [hE']; ring
    rw [h2]
    nlinarith [sq_nonneg (d t i - e (t + 1) i)]
  calc ∑ i, (m t i) ^ 2
      ≤ ∑ i, (2 * (d t i) ^ 2 + 2 * (e (t + 1) i) ^ 2) :=
        sum_le_sum (fun i _ => h1 i)
    _ = 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2 := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]

/-- The energy split accumulated over the whole loop:
`Σ_{t<T} Σᵢ (m t i)² ≤ 2·Σ_{t<T} Σᵢ (d t i)² +
2·Σ_{t<T} Σᵢ (e (t+1) i)²` — the loop-level form of
`ef21_instep_energy_split`. -/
theorem ef21_instep_sum_energy
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (hd : ∀ t, d t = Q (m t))
    (T : ℕ) :
    ∑ t ∈ range T, ∑ i, (m t i) ^ 2
      ≤ 2 * ∑ t ∈ range T, ∑ i, (d t i) ^ 2
        + 2 * ∑ t ∈ range T, ∑ i, (e (t + 1) i) ^ 2 := by
  have h1 : ∀ t ∈ range T, (∑ i, (m t i) ^ 2
      ≤ 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2) :=
    fun t _ => ef21_instep_energy_split Q m e d hE hd t
  have h2 := sum_le_sum (f := fun t => ∑ i, (m t i) ^ 2)
    (g := fun t => 2 * ∑ i, (d t i) ^ 2 + 2 * ∑ i, (e (t + 1) i) ^ 2)
    h1
  refine le_trans h2 ?_
  simp [Finset.mul_sum, Finset.sum_add_distrib]

/-! ## The inexact floor for the residual -/

/-- The inexact floor: if `Q` is an `IsInexactCompressor Q α ε`
(the `Hagi.Optimization.EF21Quantizer` additive contract — the
honest form available for the ternary quantizer, which is NOT
contractive for any `α ∈ (0, 1]`), then the residual energy is
bounded: `Σᵢ (e_{t+1} i)² ≤ ((1−α)·‖m_t‖₂ + ε)²`.  Instantiated for
the ternary quantizer via `qTernVec_inexact` (`α = 0`, `ε = 0`). -/
theorem ef21_instep_residual_inexact {α ε : ℝ}
    (hC : Hagi.Optimization.EF21Quantizer.IsInexactCompressor Q α ε)
    (hE : ∀ t, e (t + 1) = m t - Q (m t)) (t : ℕ) :
    ∑ i, (e (t + 1) i) ^ 2
      ≤ ((1 - α) * Real.sqrt (∑ i, (m t i) ^ 2) + ε) ^ 2 := by
  have hflip : ∀ i : n, (e (t + 1) i) ^ 2
      = (Q (m t) i - m t i) ^ 2 := by
    intro i
    have hE' := congrFun (hE t) i
    simp only [Pi.sub_apply] at hE'
    rw [hE']; ring
  rw [Finset.sum_congr rfl (fun i _ => hflip i)]
  exact hC (m t)

/-! ## The bench bridge (ℚ certificate trajectory) -/

/-- The final objective of a certificate list: the `obj'` of the last
step, or `start` for the empty list (the executable fold twin of the
trainer's chained readouts). -/
def trajObj (start : ℚ) : List CertStepData → ℚ
  | [] => start
  | d :: ds => trajObj d.obj' ds

/-- The bench-valid bridge: a trajectory passing the executable
`checkTrajectory` telescopes at the rational readout level — the
final objective is at most the start minus the sum of declared
drops.  The trainer emits `drop = obj − obj'` exactly and
`checkStep` demands `drop ≤ obj − obj'`, so this is the honest
descent ledger of the accepted (compressed) steps; rejected steps
never enter the list (`ef21_reject_hold`). -/
theorem ef21_bench_valid (start : ℚ) (ds : List CertStepData)
    (h : checkTrajectory start ds = true) :
    trajObj start ds ≤ start - (ds.map CertStepData.drop).sum := by
  induction ds generalizing start with
  | nil => simp [trajObj]
  | cons d rest ih =>
    rw [checkTrajectory] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hobj, hck⟩, hrest⟩ := h
    have hdesc := (checkStep_spec hck).2.1
    have hsum : ((d :: rest).map CertStepData.drop).sum
        = d.drop + (rest.map CertStepData.drop).sum := by
      simp [List.map_cons]
    rw [trajObj, hsum]
    have hih := ih d.obj' hrest
    linarith

/-! ## Rejected trials can never ride the trajectory -/

/-- A rejected trial is a HOLD: whatever the readouts, a step with
declared `drop ≤ 0` — including the NEGATIVE-drop case of a
compressed step that would climb — can never pass `checkStep`, which
demands strict `0 < drop`.  This is the machine-checked reason the
ef21-step trainer excludes rejected steps from the emitted
trajectory and logs them as reject telemetry (reject-rate). -/
theorem ef21_reject_hold {E E' bud bud' rsk rsk' dr : ℚ}
    (hdr : dr ≤ 0) :
    checkStep ⟨E, E', dr, bud, bud', rsk, rsk'⟩ = false := by
  simp [checkStep, not_lt.mpr hdr]

end Hagi.Theory.EF21InStep
