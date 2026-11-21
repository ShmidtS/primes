/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.ExactBypass
import Hagi.Theory.AdapterGrowth
import Hagi.Theory.OEComplete
import Hagi.Probability.EmpiricalBernstein
import Mathlib.Tactic

/-!
# Mini-HAGI full self-improving loop (C547 bench bridge)

Roadmap C546 top-1: the FULL certified-era bench
(`scripts/bench_bridge.py`, `--mode mini-hagi-loop`) — all
components in ONE trace: P1 exact bypass (a symbolic law covers
part of the corpus with EXACTLY zero CE-contribution), P2/P3
certified adapter training and growth (measured drop > 0
admission, neutral-init grow, snap determinism), P4 continual
isolation (per-task adapters, frozen task A keeps its outputs
IDENTICAL — forgetA = 0 bit-exact), P5 OE primitive search with
an EB-gated accept (validation exact; n_EB vs n_Hoeffding as the
C539 cost contrast), P6 final metrics.

`full_loop_sound` is a COMPOSITIONAL WRAPPER: under the phase
hypotheses (each one exactly the hypothesis of an existing
theorem) the composed run preserves every phase invariant —
no new deep facts, no weakening (each conjunct is the component
theorem's conclusion verbatim).

## Honest pins

1. P1 quantizes targets to the snap grid 1/2 (docstring PIN in
   the bridge); "CE-contribution 0" is the bench surrogate MSE
   contribution, the exact-gate semantics (`p x = 1` on covered
   positions) maps to it positionwise.
2. The P5 EB numbers (n_EB vs n_Hoeffding) are float cost
   TELEMETRY; the accept decision in the bench is exact
   (all-or-nothing validation, error == 0 in Fractions).
3. The adapter/continual phases are per-task adapter statements
   (`AdapterGrowth.ContinualIsolation`, C544); this module adds
   only the composition, not new forgetting theory.
-/

namespace Hagi.Theory.MiniHagiLoop

open Hagi.Theory.ExactBypass Hagi.Theory.AdapterGrowth
open Hagi.Theory.OEComplete

/-! ## `full_loop_sound`: the composition -/

section FullLoop

variable {ι V : Type} [Fintype V] [Nonempty V]
    {Prog Obs : Type}
    [DecidableEq Obs] (obsV : Prog → Obs)

/-- **Full-loop soundness (C547)**: one certified full-loop run
preserves ALL phase invariants simultaneously. Each conjunct of
the conclusion is the VERBATIM conclusion of a component theorem
(`exact_gate_sound`, `adapter_step_certified`,
`adapter_isolation_zero_forgetting`, `oe_search_complete`,
`empirical_bernstein_mean_bound`) — the composition adds no
hypotheses and weakens nothing. -/
theorem full_loop_sound {p : ι → ℝ} {cov : List ι}
    (hGate : ExactGate p cov)
    -- P2/P3: a committed certified adapter step
    {S : Type*} {obj : S → ℝ} {s s' : S}
    (hStep : obj s' < obj s)
    -- P4: task A frozen across task B's training
    {r d : Type*} [Fintype r] [Fintype d]
    (sA sA' : ι → AdaptState r d) (a : ι)
    (hFrozen : sA' a = sA a) (x : d → ℝ)
    -- P5: OE search completeness hypothesis
    {pP : Prog} {space : List Prog} (hIn : pP ∈ space)
    -- P5: EB mean bound hypotheses
    (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    -- P1: covered positions contribute EXACTLY zero CE
    ceSum p cov = 0 ∧
    -- P2/P3: the committed step updates and strictly descends
    adapterStep obj s s' = s' ∧
      obj (adapterStep obj s s') < obj s ∧
    -- P4: task A's output is IDENTICAL (zero forgetting)
    perTaskVec sA' a x = perTaskVec sA a x ∧
    -- P5a: the OE-dedup search finds an obs-equivalent program
    (∃ qw ∈ oeFirsts obsV space, obsV qw = obsV pP) ∧
    -- P5b: the EB mean radius bounds the validation mean
    1 - alpha ≤ Hagi.Probability.prodPq (fun _ => q)
      (fun ω => |Hagi.Probability.azumaSum X n ω / (n : ℝ)| <
        Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ))
          + 2 * b * Real.log (2 / alpha) / (n : ℝ)) := by
  obtain ⟨hst, hobj⟩ := adapter_step_certified obj s s' hStep
  obtain ⟨q1, hq1mem, hq1obs⟩ := oe_search_complete obsV hIn
  exact ⟨exact_gate_sound p cov hGate, hst, hobj,
    adapter_isolation_zero_forgetting sA sA' a hFrozen x,
    ⟨q1, hq1mem, hq1obs⟩,
    Hagi.Probability.empirical_bernstein_mean_bound q hq0 hq1
      X b hb hbnd sig hsig hmean hvar n hn alpha halpha1 halpha2⟩

end FullLoop

end Hagi.Theory.MiniHagiLoop
