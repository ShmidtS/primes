/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Unified.StitchingEProcess
import Hagi.Unified.CountableStitching
import Hagi.Deployment.CanaryRamp
set_option linter.style.header false

/-!
# Ville monitor bridge (C341, addendum A13 priority P-2)

The reusable MONITOR interface connecting the existing Ville /
e-process machinery into the runtime harm/gain watcher that the
canary ramp (C324 `Hagi.Deployment.canaryVilleMonitorHold`) and the
audit ledger (C274 harm events via the C264 embedding premise)
cite premise-form. THIN, composition only: the sole new content is
the adapter layer — the identification of the monitor threshold
`1/α` with the Ville threshold `δ⁻¹` at `δ := α` — every
probability statement below is a DIRECT instantiation of a cited
carrier theorem.

* `EProcMonitor` — the monitor state: significance level `α`
  (`α_pos`), current e-value `M`, update record `updates`, and the
  invariant `hM : M = updates.foldr (· * ·) 1` (the e-value is
  exactly the product of the applied factors).
* `monitorUpdate` — multiply the e-value by an increment factor and
  push it on the record (invariant preserved; one `mul_comm`).
* `monitorFires` — the firing predicate `α⁻¹ ≤ M` (the Ville form
  `M_t ≥ 1/α`).
* `monitor_ville_valid` — the firing bound under the null: for a
  nonnegative supermartingale trajectory with `μ[L 0] ≤ 1`,
  `μ.real {∃ t ≤ n, α⁻¹ ≤ L t} ≤ α` for every horizon `n` at once.
  Direct instantiation of
  `Hagi.Unified.ville_anytime_false_alarm` at `δ := α`.
* `monitor_ville_valid_stitched` — the same bound for the finite
  stitched master `Hagi.Unified.stitchedMaster` (C232, exact
  citation of `Hagi.Unified.stitching_eprocess_anytime`).
* `monitor_ville_valid_countable` — the same bound for the
  countable tsum master `Hagi.Unified.stitchedMasterCountable`
  (C295, exact citation of `Hagi.Unified.stitching_countable_ville`).
* `canary_monitor_fires` — the C324 adapter (one line): at
  `thresh = α⁻¹` the premise-form canary contract
  `Hagi.Deployment.canaryVilleMonitorHold` IS the monitor-firing ⇒
  certified-HOLD implication (definitional unfolding). The hold
  witness supply stays premise-form, as in C324.
* `audit_monitor_fires` — the C264/C274 adapter: if every harm
  event `F t` embeds in the monitor crossing (`F t ω → α⁻¹ ≤ L t ω`,
  the exact `Hagi.Contracts.GatePipeline.gate_anytime_valid`
  embedding premise shape), then `μ.real {∃ t ≤ n, F t} ≤ α`.
* `monitorAnchor` / `monitorAnchorQuiet` / `monitor_anchor_fires` /
  `monitor_anchor_quiet` / `monitor_anchor_traj` — numeric anchors:
  factors `2, 2` at `α = 1/4` fire exactly at the crossing
  (`4 ≥ 4`); the single factor `2` stays quiet (`2 < 4`); the
  trajectory `2^t` crosses `(1/4)⁻¹` first at `t = 2`.

Honest scope: anytime validity comes ENTIRELY from the cited
carriers (C232/C295 stitching, the Ville engine beneath them, the
C264 embedding form) — no new concentration, no new supermartingale
closure, no construction of per-expert e-processes. The increment
being a VALID e-process factor is premise-form, carried by the
supermartingale premise of the validity theorems (C232/C295
premise-form convention). The runtime interface is deterministic
bookkeeping; the probability statements live on the Ω-indexed
trajectory the monitor is fed.
-/

open Finset MeasureTheory ProbabilityTheory

namespace Hagi.Contracts.VilleMonitor

/-! ## The monitor state -/

/-- The runtime e-process monitor state: significance level `α`
(threshold `α⁻¹ = 1/α`), current e-value `M` (nonnegative in use;
the null-premise carries the bound), and the update record — the
multiplicative e-process factors applied so far, with `M` exactly
their product (`hM`). -/
structure EProcMonitor where
  /-- Significance level α — the false-alarm budget (Ville δ). -/
  α : ℝ
  /-- The level is positive (Ville `0 < δ`). -/
  α_pos : 0 < α
  /-- The current e-value M (product of the applied factors). -/
  M : ℝ
  /-- The update record: multiplicative increment factors, most
  recent first. -/
  updates : List ℝ
  /-- The e-value is exactly the product of the update record. -/
  hM : M = updates.foldr (· * ·) 1

/-- One monitor update: multiply the e-value by the increment
factor `fac` and push it on the update record. PREMISE-form: `fac`
being a valid e-process factor (nonnegative, conditional mean ≤ 1
under the null) is NOT checked here — it is exactly what the
supermartingale premise of `monitor_ville_valid` carries. -/
def monitorUpdate (mon : EProcMonitor) (fac : ℝ) : EProcMonitor where
  α := mon.α
  α_pos := mon.α_pos
  M := mon.M * fac
  updates := fac :: mon.updates
  hM := by
    rw [List.foldr_cons, ← mon.hM]
    exact mul_comm mon.M fac

/-- The monitor fires: the e-value has reached the Ville threshold
`1/α` (the C232/C295 form `M_t ≥ 1/α`). -/
def monitorFires (mon : EProcMonitor) : Prop := mon.α⁻¹ ≤ mon.M

/-! ## The Ville firing bound (direct carrier instantiations) -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}

/-- **The monitor firing bound (Ville, singleton carrier)**: under
the null — the fed trajectory `L` is a nonnegative supermartingale
with `μ[L 0] ≤ 1` (premise-form e-process) — the monitor fires by
horizon `n` with probability at most `α`, for EVERY horizon `n` at
once. Direct instantiation of
`Hagi.Unified.ville_anytime_false_alarm` at `δ := α`; the adapter
content is exactly that identification. -/
theorem monitor_ville_valid (mon : EProcMonitor)
    {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : μ[L 0] ≤ 1) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), mon.α⁻¹ ≤ L t ω} ≤ mon.α :=
  Hagi.Unified.ville_anytime_false_alarm hL hLnn hL0 n mon.α_pos

/-- The C232 instantiation: the monitor over the finite stitched
master `Hagi.Unified.stitchedMaster w E` (nonnegative weights
summing to ≤ 1 over nonnegative unit-budget supermartingale
experts) fires with probability ≤ α, every horizon at once. Direct
application of `Hagi.Unified.stitching_eprocess_anytime` at
`δ := α`. -/
theorem monitor_ville_valid_stitched (mon : EProcMonitor)
    {k : Type} [Fintype k] [DecidableEq k] [Nonempty k]
    (w : k → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i ≤ 1)
    (E : k → ℕ → Ω → ℝ) (hE : ∀ i, Supermartingale (E i) 𝒢 μ)
    (hEnn : ∀ i, 0 ≤ E i) (hE0 : ∀ i, μ[E i 0] ≤ 1) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      mon.α⁻¹ ≤ Hagi.Unified.stitchedMaster w E t ω} ≤ mon.α :=
  Hagi.Unified.stitching_eprocess_anytime w hw hwsum E hE hEnn hE0
    mon.α_pos n

/-- The C295 instantiation: the monitor over the countable tsum
master `Hagi.Unified.stitchedMasterCountable w E` (summable
nonnegative weights with tsum ≤ 1) fires with probability ≤ α,
every horizon at once. Direct application of
`Hagi.Unified.stitching_countable_ville` at `δ := α`. -/
theorem monitor_ville_valid_countable (mon : EProcMonitor)
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwsumm : Summable w)
    (hwsum : ∑' k, w k ≤ 1)
    (E : ℕ → ℕ → Ω → ℝ) (hE : ∀ k, Supermartingale (E k) 𝒢 μ)
    (hEnn : ∀ k t ω, 0 ≤ E k t ω) (hE0 : ∀ k, μ[E k 0] ≤ 1)
    (hsum : ∀ t ω, Summable fun k => w k * E k t ω) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      mon.α⁻¹ ≤ Hagi.Unified.stitchedMasterCountable w E t ω}
      ≤ mon.α :=
  Hagi.Unified.stitching_countable_ville w E hw hwsumm hwsum hE hEnn hE0
    hsum mon.α_pos n

/-! ## Consumer bridges (one line each) -/

/-- **The C324 canary adapter**: at threshold `thresh = α⁻¹` the
premise-form canary monitor contract
`Hagi.Deployment.canaryVilleMonitorHold` is EXACTLY the
monitor-firing ⇒ certified-HOLD implication — a definitional
unfolding, nothing new. What the bridge discharges is the threshold
IDENTIFICATION; the hold-witness supply `steps` stays premise-form,
as in C324. -/
theorem canary_monitor_fires {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (t : ℕ → S) (eProc : ℕ → ℝ) (mon : EProcMonitor)
    (steps : ∀ j, Hagi.Cert.TransitionStep M obl (t j) (t (j + 1))) :
    Hagi.Deployment.canaryVilleMonitorHold M obl t eProc mon.α⁻¹ steps ↔
      ∀ j, mon.α⁻¹ ≤ eProc j →
        ∃ h : Hagi.Cert.HoldStep M obl (t j) (t (j + 1)),
          steps j = Hagi.Cert.TransitionStep.hold h :=
  Iff.rfl

/-- **The C264/C274 audit adapter**: if every harm event `F t` (the
runtime harm watcher's alarm, C274's Bad-event side) embeds in the
monitor crossing at `t` — the exact `hF` embedding premise shape of
`Hagi.Contracts.GatePipeline.gate_anytime_valid` — then the
probability that ANY harm event fires by horizon `n` is ≤ α.
Proof: `monitor_ville_valid` + monotonicity, the same proof shape
`gate_anytime_valid` uses. Premise-form where the originals are
premise-form: the embedding `hF` and the e-process premises are the
consumer's to discharge. -/
theorem audit_monitor_fires (mon : EProcMonitor)
    {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : μ[L 0] ≤ 1) (n : ℕ) (F : ℕ → Ω → Prop)
    (hF : ∀ t ∈ Finset.range (n + 1), ∀ ω, F t ω → mon.α⁻¹ ≤ L t ω) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1), F t ω} ≤ mon.α := by
  have hmain := monitor_ville_valid mon hL hLnn hL0 n
  refine le_trans ?_ hmain
  refine measureReal_mono ?_ (by finiteness)
  rintro ω ⟨t, ht, hFt⟩
  exact ⟨t, ht, hF t ht ω hFt⟩

/-! ## Numeric anchors -/

/-- The anchor monitor: level `α = 1/4` (threshold `1/α = 4`),
e-value 4 with update record `[2, 2]` (two doubling factors) —
fired exactly at the crossing. -/
noncomputable def monitorAnchor : EProcMonitor where
  α := 1 / 4
  α_pos := by norm_num
  M := 4
  updates := [2, 2]
  hM := by norm_num

/-- The quiet anchor: level `α = 1/4`, e-value 2 with update record
`[2]` (a single doubling factor) — NOT fired. -/
noncomputable def monitorAnchorQuiet : EProcMonitor where
  α := 1 / 4
  α_pos := by norm_num
  M := 2
  updates := [2]
  hM := by norm_num

/-- Anchor (firing at the crossing): two factors `2, 2` at
`α = 1/4` bring the e-value to `4 = 1/α` — the monitor fires
EXACTLY at the crossing step. -/
theorem monitor_anchor_fires : monitorFires monitorAnchor := by
  simp only [monitorFires, monitorAnchor]
  norm_num

/-- Anchor (quiet): a single factor `2` at `α = 1/4` leaves the
e-value at `2 < 4 = 1/α` — the monitor does NOT fire. -/
theorem monitor_anchor_quiet : ¬ monitorFires monitorAnchorQuiet := by
  simp only [monitorFires, monitorAnchorQuiet]
  norm_num

/-- Anchor (trajectory crossing): the e-process trajectory
`t ↦ 2 ^ t` (factors 2 each step) crosses the anchor threshold
`(1/4)⁻¹ = 4` within the first three steps — first at `t = 2`. -/
theorem monitor_anchor_traj :
    ∃ t ∈ Finset.range 3, monitorAnchor.α⁻¹ ≤ (2 : ℝ) ^ t := by
  rw [show monitorAnchor.α = 1 / 4 from rfl]
  exact ⟨2, by norm_num, by norm_num⟩

end Hagi.Contracts.VilleMonitor
