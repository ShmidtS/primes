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

/-! ## `IterativeLoop` (C549): the self-improvement CYCLE -/

section IterativeLoop

/-- State of the iterative loop after k iterations: the list
of accepted primitive programs (append-only across iterations).
-/ structure IterState (Prog ι : Type) where
  prims : List Prog

/-- The loop's step: an iteration only APPENDS newly accepted
primitives (nothing is ever removed or mutated). -/
def iterStep {Prog ι : Type} (st : IterState Prog ι)
    (new : List Prog) : IterState Prog ι where
  prims := st.prims ++ new

/-- A position is covered by a state iff some accepted primitive
(represented by the abstract predicate `CovP`) covers it. -/
def coversPrim {Prog ι : Type} (CovP : Prog → ι → Prop)
    (st : IterState Prog ι) (i : ι) : Prop :=
  ∃ p ∈ st.prims, CovP p i

/-- **Coverage monotonicity of one iteration (C549)**: an
append-only step preserves every previously covered position. -/
theorem coverage_append_monotone {Prog ι : Type}
    (CovP : Prog → ι → Prop) (st : IterState Prog ι)
    (new : List Prog) (i : ι)
    (h : coversPrim CovP st i) :
    coversPrim CovP (iterStep st new) i := by
  obtain ⟨p, hp, hcov⟩ := h
  exact ⟨p, List.mem_append_left _ hp, hcov⟩

/-- **Iterative loop soundness (C549)**: if EVERY iteration of
an n-iteration run extends the primitive list additively (the
exact-gate is conservative: a position covered by an accepted
primitive stays covered — `coverage_append_monotone`), then the
coverage of the final state contains the coverage of EVERY
earlier state (in particular the initial one). Induction on n.

HONEST PIN: the per-iteration full-loop invariants (gate, adapter
step, isolation, OE, EB) are exactly `full_loop_sound`'s
conclusions, applied per iteration under its own hypotheses;
the NEW mathematical content here is only the monotone-coverage
chain. -/
theorem iterative_loop_sound {Prog ι : Type}
    (CovP : Prog → ι → Prop)
    (n : ℕ) (st : ℕ → IterState Prog ι)
    (hAdd : ∀ k < n, ∃ new, st (k + 1) = iterStep (st k) new)
    (k : ℕ) (hk : k ≤ n) (i : ι)
    (h0 : coversPrim CovP (st k) i) :
    coversPrim CovP (st n) i := by
  have key : ∀ (m k : ℕ), k + m = n →
      coversPrim CovP (st k) i → coversPrim CovP (st n) i := by
    intro m
    induction m with
    | zero =>
      intro k hk h
      have hkn : k = n := by omega
      subst hkn
      exact h
    | succ m ih =>
      intro k hk h
      obtain ⟨new, hstep⟩ := hAdd k (by omega)
      have h1 : coversPrim CovP (st (k + 1)) i := by
        rw [hstep]
        exact coverage_append_monotone CovP (st k) new i h
      exact ih (k + 1) (by omega) h1
  exact key (n - k) k (by omega) h0

end IterativeLoop

/-! ## `UniversalLoop` (C551): the full live corpus -/

section UniversalLoop

/-- **Union-additivity of corpus coverage (C551)**: if a loop
state covers every position of domain list `lA` AND every
position of domain list `lB`, then it covers every position of
the UNION corpus `lA ++ lB`. Extending the corpus by a union of
domains never breaks coverage monotonicity. -/
theorem universal_loop_corpus_mono {Prog ι : Type}
    (CovP : Prog → ι → Prop) (st : IterState Prog ι)
    (lA lB : List ι)
    (hA : ∀ i ∈ lA, coversPrim CovP st i)
    (hB : ∀ i ∈ lB, coversPrim CovP st i) :
    ∀ i ∈ lA ++ lB, coversPrim CovP st i := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact hA i h
  · exact hB i h

end UniversalLoop

end Hagi.Theory.MiniHagiLoop
