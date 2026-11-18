/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Contracts.VilleMonitor
import Hagi.Unified.CountableStitching
import Hagi.Training.MacroStatCert

/-!
# Adaptive anytime validation via stitched Ville (C399, A16/A17)

The adaptive macro-loop route the C380 pin deferred: the loop
EVALUATES CHECKPOINTS ADAPTIVELY (which checkpoint to evaluate, and
whether to commit or roll back, chosen from PAST validation
results), and classical fixed-sample bounds do not transfer to such
reused data. This module lifts the pin through the stitched
Ville masters — C232 `stitching_eprocess_anytime` and C295
`stitching_countable_ville` — at the `MacroStatCert` level: an
anytime-valid commit control over ANY adaptively chosen sequence of
at most `K` evaluations, with the exact stitched constant `K·α`.

Modeling (honest, no new probability — composition only):

* each round `k` carries its own e-process `E k : ℕ → Ω → ℝ` on the
  SAME filtered probability space `(Ω, 𝒢, μ)`;
* the per-round premise is exactly the C232/C295 binder —
  `Supermartingale (E k) 𝒢 μ`, nonnegative, unit initial budget:
  the e-value update has conditional mean ≤ its current value given
  the ENTIRE past filtration `𝒢 t`. This is the "fresh sample drawn
  conditionally on the past" assumption in its weakest usable form;
* ADAPTIVITY IS FREE, honestly: the false-commit event over any —
  even adversarial, non-measurable — selection schedule of ≤ K
  rounds is a SUBSET of the superset event
  `{∃ k < K, ∃ t ≤ n, α⁻¹ ≤ E k t}` bounded by the countable master
  with uniform weights `w k = 1/K`; the bound never consults the
  selection rule. No predictability or stopping-time machinery is
  needed (and none is smuggled: `μ.real` is monotone on arbitrary
  sets, the frozen C380 convention).

Main statements:

* `adaptive_anytime_valid` — MAIN: under the stitched-master
  per-round premise and the C264-style embedding premise (a false
  commit at round `k` embeds in round `k`'s e-process crossing
  `α⁻¹` by the horizon), the false-commit probability over ANY
  adaptively chosen sequence of ≤ K evaluations is ≤ `K·α` (the
  uniform-weight stitched constant: crossing `α⁻¹` at some round
  drives the master to `(1/K)·α⁻¹ = (K·α)⁻¹`, and C295 bounds the
  master crossing at level `δ := K·α`; for `K·α ≥ 1` the bound is
  the honest trivial branch inherited from C295).
* `adaptive_anytime_budget_split` — the Bonferroni view through the
  SAME master: thresholds `(α/K)⁻¹` per round give the total ≤ `α`.
* `adaptive_commit_bridge` — the `MacroStatCert` (C380) bridge: a
  finite family of macro certificates, each under its own C380
  premise bundle, has `μ.real {∃ k, commit k ∧ ¬goodGain k} ≤
  ∑ k, α k` (per-round `commit_sound` + finite union). The frozen
  C380 statement is cited verbatim, not modified.
* `adaptive_commit_bridge_uniform` — the equal-level corollary
  `∑ k, α = K•α`.

Honest scope (pins):

1. **Per-round conditional validity (premise-form)**: the binder
   `Supermartingale (E k) 𝒢 μ` holds when each evaluation consumes
   a FRESH conditional draw given the past. It is STRICTLY WEAKER
   than mutual independence across rounds (dependent increments
   with conditional mean ≤ 1 still qualify) and STRICTLY STRONGER
   than full reuse — see pin 2.
2. **Full-reuse-no-fresh-draws regime NOT covered (negative pin)**:
   if the same data is FULLY reused with no fresh conditional draw,
   the e-process degenerates to a deterministic function of
   already-observed values and NO supermartingale binder is
   derivable — counterexample sketch: the constant process
   `E ≡ 2` at `α = 1/2` crosses the threshold at t = 0 with
   probability 1 while the unit-budget premise `μ[E 0] ≤ 1` fails
   (`μ[E 0] = 2 > 1`); the theorems below are vacuous there. This
   is exactly the A16 acceptance bar: plain Freedman on reused data
   is insufficient, and the honest lift requires per-round
   conditional (fresh-draw) validity — not claimed for full reuse.
3. **Constant honesty**: `K·α` is the stitched uniform constant, not
   an optimality claim; mixture refinements are out of scope (no
   new concentration, the repo convention).
-/

set_option relaxedAutoImplicit false

open Finset MeasureTheory ProbabilityTheory

namespace Hagi.Training

/-! ## The adaptive evaluation trace -/

/-- The adaptive evaluation trace: the macro loop's record of ≤
`numRounds` evaluations. Round `k` runs e-process `E k` up to the
common `horizon` and ends in the per-round commit flag
`committed k ω` — taken AFTER seeing past results, hence
ω-dependent; the validity theorems never need the selection rule's
measurability (the superset event covers every schedule). The level
`α` is the per-round Ville budget. -/
structure AdaptiveEvalTrace (Ω : Type*) [MeasurableSpace Ω] where
  /-- Per-round significance level α (Ville δ). -/
  α : ℝ
  /-- The level is positive. -/
  α_pos : 0 < α
  /-- Number of evaluation rounds K. -/
  numRounds : ℕ
  /-- Round k's e-process on the common filtered space. -/
  E : ℕ → ℕ → Ω → ℝ
  /-- Common horizon for every round's evaluation window. -/
  horizon : ℕ
  /-- Round k ended in a commit (ω-dependent: decided adaptively
  from past results). -/
  committed : ℕ → Ω → Bool

/-! ## The uniform stitched schedule -/

/-- The uniform round schedule: weight `1/K` on rounds `k < K`, 0
beyond — a countable stitch with total mass exactly 1 (C295 binder
at `∑' w ≤ 1`). -/
noncomputable def adaptiveRoundWeights (K : ℕ) (k : ℕ) : ℝ :=
  if k < K then (K : ℝ)⁻¹ else 0

/-- The uniform schedule is nonnegative. -/
theorem adaptiveRoundWeights_nonneg (K : ℕ) (k : ℕ) :
    0 ≤ adaptiveRoundWeights K k := by
  unfold adaptiveRoundWeights
  split <;> positivity

/-- The uniform schedule is summable (finite support inside
`range K`). -/
theorem adaptiveRoundWeights_summable (K : ℕ) :
    Summable (adaptiveRoundWeights K) := by
  refine summable_of_ne_finset_zero (s := Finset.range K) (fun k hk => ?_)
  unfold adaptiveRoundWeights
  have hnk : ¬ k < K := by simpa using hk
  simp [hnk]

/-- The uniform schedule has total mass exactly 1 (K ≥ 1). -/
theorem adaptiveRoundWeights_tsum (K : ℕ) (hK : 0 < K) :
    ∑' k, adaptiveRoundWeights K k = 1 := by
  have hzero : ∀ b ∉ Finset.range K, adaptiveRoundWeights K b = 0 := by
    intro k hk
    unfold adaptiveRoundWeights
    have hnk : ¬ k < K := by simpa using hk
    simp [hnk]
  have hmem : ∀ k ∈ Finset.range K,
      adaptiveRoundWeights K k = (K : ℝ)⁻¹ := by
    intro k hk
    have hk' : k < K := Finset.mem_range.1 hk
    unfold adaptiveRoundWeights
    split
    · rfl
    · next h => exact absurd hk' h
  rw [tsum_eq_sum hzero, Finset.sum_congr rfl hmem, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp

/-- One round's crossing at `α⁻¹` drives the uniform master to
`(K·α)⁻¹` (pointwise; the singleton term of the countable
mixture). -/
private theorem master_cross_of_round_cross {Ω : Type*}
    [MeasurableSpace Ω] {K : ℕ} {α : ℝ}
    (E : ℕ → ℕ → Ω → ℝ) (hEnn : ∀ k t ω, 0 ≤ E k t ω)
    (hsum : ∀ t ω,
      Summable fun k => adaptiveRoundWeights K k * E k t ω)
    (t k : ℕ) (hk : k < K) (ω : Ω) (hcross : α⁻¹ ≤ E k t ω) :
    (K * α)⁻¹ ≤ Hagi.Unified.stitchedMasterCountable
      (adaptiveRoundWeights K) E t ω := by
  have h1 : adaptiveRoundWeights K k = (K : ℝ)⁻¹ := by
    unfold adaptiveRoundWeights
    split
    · rfl
    · next h => exact absurd hk h
  have hterm : (K : ℝ)⁻¹ * α⁻¹
      ≤ adaptiveRoundWeights K k * E k t ω := by
    rw [h1]
    exact mul_le_mul_of_nonneg_left hcross (by positivity)
  have hle : adaptiveRoundWeights K k * E k t ω
      ≤ ∑' j, adaptiveRoundWeights K j * E j t ω := by
    have hsin := (hsum t ω).sum_le_tsum ({k} : Finset ℕ)
      (fun j _ => mul_nonneg (adaptiveRoundWeights_nonneg K j)
        (hEnn j t ω))
    rwa [Finset.sum_singleton] at hsin
  calc (K * α)⁻¹ = (K : ℝ)⁻¹ * α⁻¹ := by
          rw [mul_inv_rev, mul_comm]
    _ ≤ ∑' j, adaptiveRoundWeights K j * E j t ω :=
        le_trans hterm hle

/-! ## Main theorem: adaptive anytime validity -/

/-- **Adaptive anytime validity (MAIN, C399)**: for an adaptive
evaluation trace with `K ≥ 1` rounds at level `α`, under the
stitched-master per-round premise (each round's e-process is a
nonnegative `𝒢`-supermartingale with unit initial budget — the
C232/C295 binder; per-round CONDITIONAL validity given the common
filtration, i.e. a fresh conditional draw per round — full reuse
without fresh draws is NOT covered, see the module pins) and the
C264-style embedding premise (a FALSE commit at round `k` embeds in
round `k`'s e-process crossing `α⁻¹` within the horizon), the
probability of a false commit over ANY adaptively chosen sequence of
≤ K evaluations is at most `K·α` — the exact uniform-weight stitched
constant (`δ := K·α` in `Hagi.Unified.stitching_countable_ville`,
C295). Adaptivity is free: the superset crossing event covers every
selection schedule, measurable or not. For `K·α ≥ 1` the bound is
the honest trivial branch inherited from C295. -/
theorem adaptive_anytime_valid {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    (tr : AdaptiveEvalTrace Ω) (hK : 0 < tr.numRounds)
    (hE : ∀ k, Supermartingale (tr.E k) 𝒢 μ)
    (hEnn : ∀ k t ω, 0 ≤ tr.E k t ω)
    (hE0 : ∀ k, μ[tr.E k 0] ≤ 1)
    (hsum : ∀ t ω,
      Summable fun k => adaptiveRoundWeights tr.numRounds k * tr.E k t ω)
    {falseGain : ℕ → Ω → Prop}
    (hembed : ∀ ω, ∀ k < tr.numRounds,
      (tr.committed k ω = true ∧ falseGain k ω) →
        ∃ t ∈ Finset.range (tr.horizon + 1), tr.α⁻¹ ≤ tr.E k t ω) :
    μ.real {ω | ∃ k < tr.numRounds,
      tr.committed k ω = true ∧ falseGain k ω} ≤ tr.numRounds * tr.α := by
  set K := tr.numRounds with hKdef
  have hsub : {ω | ∃ k < K, tr.committed k ω = true ∧ falseGain k ω} ⊆
      {ω | ∃ t ∈ Finset.range (tr.horizon + 1),
        (K * tr.α)⁻¹ ≤ Hagi.Unified.stitchedMasterCountable
          (adaptiveRoundWeights K) tr.E t ω} := by
    rintro ω ⟨k, hk, hcom, hbad⟩
    obtain ⟨t, ht, hle⟩ := hembed ω k hk ⟨hcom, hbad⟩
    exact ⟨t, ht, master_cross_of_round_cross tr.E hEnn
      hsum t k hk ω hle⟩
  refine le_trans (measureReal_mono hsub (by finiteness)) ?_
  exact Hagi.Unified.stitching_countable_ville
    (adaptiveRoundWeights K) tr.E (adaptiveRoundWeights_nonneg K)
    (adaptiveRoundWeights_summable K)
    (le_of_eq (adaptiveRoundWeights_tsum K hK)) hE hEnn hE0 hsum
    (mul_pos (Nat.cast_pos.2 hK) tr.α_pos) tr.horizon

/-- **The budget-split corollary (Bonferroni through the same
master)**: with per-round thresholds `(α/K)⁻¹` — each round spends
only an `α/K` share of the budget — the total false-commit
probability over any adaptive sequence of ≤ K evaluations is at
most `α`: a round crossing `(α/K)⁻¹` drives the uniform master to
`(1/K)·(α/K)⁻¹ = α⁻¹` EXACTLY, and C295 bounds the master crossing
at `δ := α`. -/
theorem adaptive_anytime_budget_split {Ω : Type*}
    {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    (tr : AdaptiveEvalTrace Ω) (hK : 0 < tr.numRounds)
    (hE : ∀ k, Supermartingale (tr.E k) 𝒢 μ)
    (hEnn : ∀ k t ω, 0 ≤ tr.E k t ω)
    (hE0 : ∀ k, μ[tr.E k 0] ≤ 1)
    (hsum : ∀ t ω,
      Summable fun k => adaptiveRoundWeights tr.numRounds k * tr.E k t ω)
    {falseGain : ℕ → Ω → Prop}
    (hembed : ∀ ω, ∀ k < tr.numRounds,
      (tr.committed k ω = true ∧ falseGain k ω) →
        ∃ t ∈ Finset.range (tr.horizon + 1),
          (tr.α / tr.numRounds)⁻¹ ≤ tr.E k t ω) :
    μ.real {ω | ∃ k < tr.numRounds,
      tr.committed k ω = true ∧ falseGain k ω} ≤ tr.α := by
  set K := tr.numRounds with hKdef
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.2 hK
  have hKeq : (K : ℝ)⁻¹ * (tr.α / K)⁻¹ = tr.α⁻¹ := by
    field_simp
  have hsub : {ω | ∃ k < K, tr.committed k ω = true ∧ falseGain k ω} ⊆
      {ω | ∃ t ∈ Finset.range (tr.horizon + 1),
        tr.α⁻¹ ≤ Hagi.Unified.stitchedMasterCountable
          (adaptiveRoundWeights K) tr.E t ω} := by
    rintro ω ⟨k, hk, hcom, hbad⟩
    obtain ⟨t, ht, hle⟩ := hembed ω k hk ⟨hcom, hbad⟩
    refine ⟨t, ht, ?_⟩
    have h1 : adaptiveRoundWeights K k = (K : ℝ)⁻¹ := by
      unfold adaptiveRoundWeights
      split
      · rfl
      · next h => exact absurd hk h
    have hterm : (K : ℝ)⁻¹ * (tr.α / K)⁻¹
        ≤ adaptiveRoundWeights K k * tr.E k t ω := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hle2 : adaptiveRoundWeights K k * tr.E k t ω
        ≤ ∑' j, adaptiveRoundWeights K j * tr.E j t ω := by
      have hsin := (hsum t ω).sum_le_tsum ({k} : Finset ℕ)
        (fun j _ => mul_nonneg (adaptiveRoundWeights_nonneg K j)
          (hEnn j t ω))
      rwa [Finset.sum_singleton] at hsin
    rw [← hKeq]
    exact le_trans hterm hle2
  refine le_trans (measureReal_mono hsub (by finiteness)) ?_
  exact Hagi.Unified.stitching_countable_ville
    (adaptiveRoundWeights K) tr.E (adaptiveRoundWeights_nonneg K)
    (adaptiveRoundWeights_summable K)
    (le_of_eq (adaptiveRoundWeights_tsum K hK)) hE hEnn hE0 hsum
    tr.α_pos tr.horizon

/-! ## The MacroStatCert bridge (C380, frozen statement cited) -/

/-- **The adaptive commit bridge (C399 → C380)**: a finite family of
macro-cycle certificates `certs : Fin K → MacroStatCert S objective`,
each under its own C380 premise bundle — its monitor trajectory
`L k` is a nonnegative supermartingale with unit initial budget, the
C264-style embedding (a false commit at k embeds in `L k` crossing
the k-th monitor's threshold) and the guard (a fired monitor never
commits) — has total false-commit probability at most the level sum
`∑ k, (certs k).mon.α`. Per round this is EXACTLY the frozen
`Hagi.Training.commit_sound` (C380, cited verbatim); the finite
union is `measureReal_iUnion_fintype_le`. The bound covers ANY
adaptive schedule over the K cycles (the union event does not
consult the schedule), which is the adaptive-data route the C380
module pin deferred to "the stitched masters, pointer only" — this
module is that pointer's target. -/
theorem adaptive_commit_bridge {S : Type*} {objective : S → ℝ}
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    (K : ℕ) (certs : Fin K → MacroStatCert S objective)
    {goodGain : Fin K → Ω → Prop}
    (L : Fin K → ℕ → Ω → ℝ)
    (hL : ∀ k, Supermartingale (L k) 𝒢 μ) (hLnn : ∀ k, 0 ≤ L k)
    (hL0 : ∀ k, μ[L k 0] ≤ 1) (n : ℕ)
    (hembed : ∀ k ω, ¬ goodGain k ω →
      ∃ t ∈ Finset.range (n + 1), (certs k).mon.α⁻¹ ≤ L k t ω)
    (hguard : ∀ k ω, (certs k).decision = MacroDecision.commit →
      ¬ ∃ t ∈ Finset.range (n + 1), (certs k).mon.α⁻¹ ≤ L k t ω) :
    μ.real {ω | ∃ k : Fin K,
      (certs k).decision = MacroDecision.commit ∧ ¬ goodGain k ω}
      ≤ ∑ k : Fin K, (certs k).mon.α := by
  have hper : ∀ k : Fin K, μ.real {ω |
      (certs k).decision = MacroDecision.commit ∧ ¬ goodGain k ω}
      ≤ (certs k).mon.α := fun k =>
    commit_sound (certs k) (hL k) (hLnn k) (hL0 k) n
      (goodGain := goodGain k) (hembed k) (hguard k)
  have hset : {ω | ∃ k : Fin K,
      (certs k).decision = MacroDecision.commit ∧ ¬ goodGain k ω}
      = ⋃ k : Fin K, {ω | (certs k).decision
        = MacroDecision.commit ∧ ¬ goodGain k ω} := by
    ext ω; simp
  rw [hset]
  exact le_trans (measureReal_iUnion_fintype_le
    (fun k : Fin K => {ω | (certs k).decision
      = MacroDecision.commit ∧ ¬ goodGain k ω}))
    (Finset.sum_le_sum (fun k _ => hper k))

/-- The equal-level corollary: K certificates all carrying the same
monitor level `α` have total false-commit probability ≤ `K * α` —
the same stitched constant as `adaptive_anytime_valid`, through
the C380 route. -/
theorem adaptive_commit_bridge_uniform {S : Type*}
    {objective : S → ℝ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℕ m0}
    (K : ℕ) (certs : Fin K → MacroStatCert S objective) (α : ℝ)
    (hlevel : ∀ k : Fin K, (certs k).mon.α = α)
    {goodGain : Fin K → Ω → Prop}
    (L : Fin K → ℕ → Ω → ℝ)
    (hL : ∀ k, Supermartingale (L k) 𝒢 μ) (hLnn : ∀ k, 0 ≤ L k)
    (hL0 : ∀ k, μ[L k 0] ≤ 1) (n : ℕ)
    (hembed : ∀ k ω, ¬ goodGain k ω →
      ∃ t ∈ Finset.range (n + 1), (certs k).mon.α⁻¹ ≤ L k t ω)
    (hguard : ∀ k ω, (certs k).decision = MacroDecision.commit →
      ¬ ∃ t ∈ Finset.range (n + 1), (certs k).mon.α⁻¹ ≤ L k t ω) :
    μ.real {ω | ∃ k : Fin K,
      (certs k).decision = MacroDecision.commit ∧ ¬ goodGain k ω}
      ≤ (K : ℝ) * α := by
  have hsum : ∑ k : Fin K, (certs k).mon.α = (K : ℝ) * α := by
    rw [Finset.sum_congr rfl (fun k _ => hlevel k), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (adaptive_commit_bridge K certs (goodGain := goodGain) L hL
    hLnn hL0 n hembed hguard).trans (le_of_eq hsum)

/-! ## Numeric anchors -/

/-- Anchor (quiet trace): a trace with no false gains has an empty
false-commit event — measure exactly 0, the trivial side of the
honest branch. -/
theorem adaptive_anytime_anchor_quiet {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (tr : AdaptiveEvalTrace Ω) {falseGain : ℕ → Ω → Prop}
    (hfalse : ∀ k ω, ¬ falseGain k ω) :
    μ.real {ω | ∃ k < tr.numRounds,
      tr.committed k ω = true ∧ falseGain k ω} = 0 := by
  have hempty : {ω | ∃ k < tr.numRounds,
      tr.committed k ω = true ∧ falseGain k ω} = ∅ := by
    ext ω
    constructor
    · rintro ⟨k, -, -, hbad⟩
      exact hfalse k ω hbad
    · exact False.elim
  rw [hempty]
  simp

/-- Anchor (constant): the stitched constant at K = 2 rounds of
level α = 1/8 is exactly `2 · (1/8) = 1/4` — a nontrivial (below 1)
instance of `adaptive_anytime_valid`'s bound. -/
theorem adaptive_anytime_anchor_constant :
    (2 : ℝ) * (1 / 8) = 1 / 4 := by norm_num

end Hagi.Training
