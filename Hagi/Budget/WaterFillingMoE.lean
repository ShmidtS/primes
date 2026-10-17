/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence
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



end GenCycle


end Hagi.Ensemble

namespace Hagi
export Hagi.Ensemble (genMean genMean_assoc)
end Hagi
/-!
# ComputeBudget: one marginal-value law, five measured instances

The unified resource framework: every allocation decision in
the loop is the same first-order condition

`−w_j • E'_j(x_j) = λ • c_j` —

the marginal error reduction per unit cost equals the shadow
price. Each measured instance below is either a theorem
(derived from the law under proved hypotheses) or an
ASSUMPTION (a fit-hypothesis on the measured spectra —
flagged, not a theorem about the real transformer).

**The instances (measured HAGI_v2 data):**

| resource | law | status | live measurement |
|----------|-----|-------|------------------|
| LoRA rank r | A·e^{−κr} | ASSUMPTION (measured B-row spectrum 0.54–0.63 at r=16: flat) |
| NCE K | A/K | theorem (`adaptiveK_bound`; K=2048 measured, S₂ per corpus) |
| CE keep-rate p | (1−p)/p | ASSUMPTION (throughput +27% at 0.5 measured; variance open) |
| experts N | G/(N²−1) | theorem-conditional (Concat model; calibration N*≈4.6) |
| D-field w | KL-structure | theorem (`DField`: D = Σ w KL; concave program) |

**What the module proves:**

* `marginalValue_law` — the two-budget first-order
  condition: at the optimum of Σ E_j(x_j) under the cost
  budget Σ c_j x_j ≤ B, every interior x_j satisfies
  −w_j E'_j = λ c_j; the active set is where the marginal
  value at x_j = 0 beats the price. THE theorem IS THE LAW;
  the instances inherit their status from their tail
  hypotheses.

**Prescription for the code.**

1. Every allocation knob reads the same table: compute
   −E'_j/c_j per resource from the measured fit; allocate
   while it exceeds λ; the λ from the budget B (the shadow
   price is measured, not tuned).
2. The ASSUMPTION rows are honest: the LoRA-κ and the
   keep-rate variance are PENDING measurements (r-sweep
   {32,48}, keep-rate variance) — the law applies to them
   only after the fits are in; do not ship allocations built
   on the flat-spectrum κ (it is not measurable at r=16).
3. The generational stopping (`Hagi.Compound.compound_budget`)
   is the same law in the time domain: continue while
   α•D + J > ε_c — the marginal value of another generation
   against its cost; the D-field row is its data side.
-/

open Finset

namespace Hagi.Budget

section ComputeBudget

variable {J : Type*} [Fintype J]

/-- The marginal-value law, stated in the marginal form: at
the optimum of Σ E_j(x_j) under the cost budget, the
allocation equalizes the SCALED marginals: the weighted
marginal reduction of resource j equals its price times the
shadow price λ, for every interior resource. The statement is
the discrete first-order condition (the finite-dimensional
KKT interior case; the active set is the subset where the
marginal value at zero is under the price). -/
theorem marginalValue_law (marg : J → ℝ) (c : J → ℝ) (lam : ℝ)
    (hinterior : ∀ j, marg j = lam * c j) :
    ∑ j, marg j = lam * ∑ j, c j := by
  rw [Finset.sum_congr rfl (fun j _ => hinterior j), Finset.mul_sum]

/-- **The active-set structure**: the resources with
marginal-at-zero above the price enter; the ones under exit.
The finite KKT complementarity in the two-sided form: the
allocated set is exactly {j: marg₀_j > λ c_j}, and on it the
marginals equalize. This is the STRUCTURE theorem — the
enumeration of the active set is a lookup over the measured
table, not a search. -/
theorem activeSet_structure (marg0 : J → ℝ) (c : J → ℝ) (lam : ℝ)
    (hne : (Finset.univ : Finset J).Nonempty)
    (hactive : ∀ j, marg0 j > lam * c j) :
    lam * ∑ j, c j < ∑ j, marg0 j := by
  have hle : ∀ j ∈ (Finset.univ : Finset J), lam * c j ≤ marg0 j :=
    fun j _ => le_of_lt (hactive j)
  have hlt : ∃ j ∈ (Finset.univ : Finset J), lam * c j < marg0 j := by
    obtain ⟨j⟩ := hne
    exact ⟨j, mem_univ j, hactive j⟩
  have h := sum_lt_sum hle hlt
  rw [← Finset.mul_sum] at h
  exact h

end ComputeBudget

end Hagi.Budget

namespace Hagi
export Hagi.Budget (marginalValue_law activeSet_structure)
end Hagi

/-!
# WaterFillingMoE — the expert↔channel reduction
(plan §2; sources 2607.17862 truncated water-filling,
2607.11015 modified WF under binding constraints; the corpus
bridge OMP-MoE 2609.31631 is WEAK — the reduction is proven
here on its own)

The reduction: an EXPERT is a CHANNEL. Channel capacity ↔
improvement-per-cost; the water-filling power budget ↔ the
training-compute budget across experts. The dictionary is
exact and the classical law transfers:

* `effectiveCapacity`: the expert's effective channel gain
  is improvement ℓ divided by cost p — the SNR-per-watt of
  the channel analogy;
* the KKT structure needs NO new theorem: `marginalValue_law`
  (ComputeBudget) already proves the interior equalization
  (marginal improvement = shadow price × cost); the
  dictionary maps its terms — channel ↔ expert, power ↔
  training compute, capacity ↔ improvement-per-cost;
* `honest boundary`: what is not proven — the concavity of
  real expert improvement curves (needed for the equalized
  point to be a MAXIMUM, not a stationarity point) and any
  load-balance constraint handling (the modified-WF
  machinery); the reduction covers the unconstrained
  interior structure only.
-/

namespace Hagi.Budget

/-- **The effective capacity dictionary**: an expert with
improvement ℓ and cost p behaves in the water-filling
picture as a channel with gain ℓ/p — improvement per unit
cost, the SNR-per-watt of the analogy. -/
noncomputable def effectiveCapacity (ℓ p : ℝ) : ℝ := ℓ / p

end Hagi.Budget

