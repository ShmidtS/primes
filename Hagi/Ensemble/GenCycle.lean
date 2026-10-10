/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence
import Mathlib

set_option linter.style.header false

/-!
# The generational cycle: when does the recursion die?

The measured facts: the Jensen gap collapses across generations
(gen-0 leaves 0.30 → gen-1 siblings 0.036 — the shared prior ate
the disagreement), and the mean CE compounds (6.120 → 5.875 →
5.694 → 5.621 across levels). The open question: does the
recursion die (each generation's joint step eats more
disagreement than the leaves can recreate) or live (the
specialization field replenishes it)?

**The model.** Each generation is a point `(M, G)` — the mean
child CE `M` and the sibling disagreement `G` (the Jensen gap of
the fresh leaves). One cycle applies two maps:

* mergeJoint: the merge at 1/n + the joint step — by
  `ensemble_ce_le_mean_general` the certified bound moves from
  `M` to the joint-finetuned `M'` (the measured improvement),
  and the disagreement of children *of the merged model* is
  born at most `G' ≤ ρ • G` with `ρ < 1` (the shared prior:
  sibling leaves start closer — `Hagi.consensus_no_gain` is the
  ρ = 0 endpoint);
* specialize: fresh leaves diverge from the new prior — the
  disagreement G'' is replenished by the data-diversity field
  `D ≥ 0` (the *only* external input).

**What the module proves:**

* `genMean_assoc` — the generational merge is associative: the
  mean-of-means equals the flat mean over all leaves — the
  formal ground for the round-21 merge fix (the leaf
  granularity normalization): hierarchical merge with identical
  subgroups is *the same object* as the flat merge, so identity
  and the 1/n scale survive every level (the `3×-identical
  merged == single` test is the N=9 instance).
* `genMean_compound` — the compounding bound: if each cycle
  improves the mean by at least `c > 0` (the measured
  5.875 → 5.694 regime), the mean after k generations is at
  most `M₀ − k • c` — the linear compounding law (as long as
  the per-cycle improvement holds).
* `genGap_decay` — the death law: if the replenishment is
  bounded (`G_next ≤ ρ • G + D` with `0 ≤ ρ < 1`), the
  disagreement sequence is bounded by the fixed point
  `G* = D/(1 − ρ)` — the recursion's *stationary disagreement*.
  The recursion dies iff `G*` is below the resolution floor ε:
  then the per-generation certified gain (which is driven by
  the fresh disagreement) falls under ε and the SATURATED
  verdict fires at the *generational* level.

**Prescription for the code.** The generational verdict for
growth_gate: measure the sibling-disagreement of the *new*
leaves (the same twoGap statistic as the ladder level); the
recursion is alive while `G_new ≥ ε` (the fresh leaves still
disagree measurably) and dies exactly when `G_new < ε` — at
which point the only remaining axis is the data axis
(EXHAUSTED): change the corpus mixture (the field D), not the
architecture. The two constants (`ρ`, `D`) are measured per
generation, and the death threshold is the SAME ε as the
ladder-level SATURATED — one criterion, two scales.

**Distill-back (round 22, P4 — honest scope).** The
expressivity question (can a V·d leaf represent the KL of a
3-leaf ensemble: `min_KL(p_wide ‖ p_leaf)`) is a capacity
question of the *block* architecture vs the ensemble; the
formal side here would need a function-class inclusion
argument, which is out of scope of the current algebraic
toolset. The practical go/no-go stays empirical: train one
distill-back leaf from the gen-1 ensemble and measure — the
element theory (`Hagi.Core/Element`) covers the parameter side
(V·d per leaf vs 3 leaves + merge), and the mean-CE bound
(`ensemble_ce_le_mean_general`) certifies the ensemble target
the distillate must reach. Marked as the honest boundary.
-/

namespace Hagi.Ensemble

section GenCycle

/-- The mean CE of a pool of leaves (any indexing). -/
noncomputable def genMean {ι : Type*} [Fintype ι]
    (ce : ι → ℝ) : ℝ := (∑ i, ce i) / (Fintype.card ι)

/-- **Associativity of the generational mean (the merge-fix
ground).** The hierarchical mean-of-means (merge N groups of
identical-size subgroups, then merge the merged) equals the flat
mean over all leaves — the round-21 granularity fix is the
statement that the *normalization* of the outer merge must be
the leaf count, and this theorem is the formal reason: the flat
mean is the invariant object that both levels must reproduce. -/
theorem genMean_assoc {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ce : ι × κ → ℝ) :
    genMean (fun i => genMean (fun j => ce (i, j)))
      = genMean (fun p => ce p) := by
  have hcard : Fintype.card ι * Fintype.card κ
      = Fintype.card (ι × κ) := by
    rw [Fintype.card_prod]
  have hsum : ∑ p, ce p = ∑ i, ∑ j, ce (i, j) := by
    rw [Fintype.sum_prod_type]
  -- per-i term equality: (Σⱼ/κ)/ι = Σⱼ/(ικ)
  have hterm : ∀ i : ι,
      (∑ j, ce (i, j)) / ((Fintype.card κ : ℝ))
        / ((Fintype.card ι : ℝ))
      = (∑ j, ce (i, j))
          / ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)) := by
    intro i
    field_simp
  -- assemble
  unfold genMean
  rw [hsum]
  rw [Finset.sum_div, Finset.sum_div]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [show ((Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))
      = ((Fintype.card (ι × κ) : ℝ)) from by

    rw [Fintype.card_prod]
    push_cast
    rfl]

/-- **The linear compounding law** (: proof lives in
Foundations.Recurrence; delegation preserves the name). -/
theorem genMean_compound (M₀ c : ℝ) (_hc : 0 < c)
    (step : ℕ → ℝ → ℝ)
    (hstep : ∀ k M, step k M ≤ M - c)
    (iter : ℕ → ℝ) (hiter0 : iter 0 = M₀)
    (hiterS : ∀ k, iter (k + 1) = step k (iter k)) :
    ∀ k : ℕ, iter k ≤ M₀ - (k : ℝ) * c :=
  Hagi.Foundations.genMean_compound M₀ c _hc step hstep iter hiter0 hiterS

/-- **The death law of the recursion** (: proof lives in
Foundations.Recurrence; delegation preserves the name). -/
theorem genGap_decay (ρ D G₀ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (_hD : 0 ≤ D) (G : ℕ → ℝ) (hG0 : G 0 ≤ G₀)
    (hstep : ∀ t, G (t + 1) ≤ ρ * G t + D) :
    ∀ t, G t ≤ ρ ^ t * G₀ + (D * (1 - ρ ^ t)) / (1 - ρ) :=
  Hagi.Foundations.genGap_decay ρ D G₀ hρ hρ1 _hD G hG0 hstep

end GenCycle


end Hagi.Ensemble

namespace Hagi
export Hagi.Ensemble (genMean genMean_assoc genMean_compound genGap_decay)
end Hagi
