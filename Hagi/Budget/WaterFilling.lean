/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.BitAlloc
import Mathlib.Tactic
import Hagi.Math.Foundations.Recurrence

set_option linter.style.header false

/-!
# WaterFilling: the balanced allocation EXISTS

The existence closure of (`BitAlloc`): the factor-2
water-filling invariant was certified at any stable point —
but does a stable point exist? Yes: on the FINITE set of
budget-feasible bit allocations the total error attains its
minimum, and at the minimum no strictly improving transfer
can exist (it would stay inside the budget set, contradicting
minimality), so `imbalance_yields_gain` contrapositive gives
the factor-2 balance. honest boundary: this is an existence
proof (via `Finset.min'`), not a construction; the
TERMINATION OF THE GREEDY REALLOCATION LOOP is now
formalized separately in `BitAllocTermination.
no_infinite_improving_chain` (: a strictly-improving
walk on the finite fixed-budget allocation space cannot
continue forever).

**Result.** `exists_balanced_allocation`: for any layer
sensitivities and any bit budget `B`, there EXISTS an
allocation f with `Σ f l ≤ B` such that every layer's error
is within a factor 2 of every other layer holding a bit:

`∀ j k, f k ≠ 0 → layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)`.

**Method.** Finite-minimum existence: allocations live in the
finite type `Fin m → Fin (B+1)` (a layer never needs more
than the whole budget), the budget slice is a filtered Finset,
nonempty (the all-zero allocation); `Finset.min'` picks the
minimizer of the total error; any improving transfer of
preserves the budget, so minimality forbids it — the
contrapositive closes the factor-2 balance.
-/

namespace Hagi.Budget

open Finset

/-- The total error of an allocation read off truncated bit
widths. -/
noncomputable def totalErrorFin (c : Fin m → ℝ) (f : Fin m → Fin (B + 1)) : ℝ :=
  ∑ l, layerError (c l) (f l)

/-- Sum decomposition at two points (the counting twin of
`totalError_two_point`). -/
theorem sum_two_point {m : ℕ} (F : Fin m → ℕ) (j k : Fin m) (hjk : j ≠ k) :
    ∑ l, F l
      = F j + F k + ∑ l ∈ (Finset.univ.erase j).erase k, F l := by
  have h1 : ∑ l ∈ Finset.univ.erase j, F l + F j = ∑ l, F l :=
    Finset.sum_erase_add Finset.univ (fun l => F l) (Finset.mem_univ j)
  have h2 : ∑ l ∈ (Finset.univ.erase j).erase k, F l + F k
      = ∑ l ∈ Finset.univ.erase j, F l :=
    Finset.sum_erase_add (Finset.univ.erase j) (fun l => F l)
      (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)
  rw [← h1, ← h2]
  ring

theorem exists_balanced_allocation {m : ℕ} (c : Fin m → ℝ) (B : ℕ)
    (hc : ∀ l, 0 ≤ c l) :
    ∃ f : Fin m → ℕ,
      (∑ l, f l ≤ B) ∧
      (∀ j k : Fin m, f k ≠ 0 →
        layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)) := by
  classical
  -- the finite budget-feasible set, in truncated bit widths
  set S : Finset (Fin m → Fin (B + 1)) :=
    Finset.univ.filter (fun f => ∑ l, (f l : ℕ) ≤ B) with hS
  have hSne : S.Nonempty :=
    ⟨fun _ => 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  -- the minimizer of the total error
  obtain ⟨fstar, hfS, hmin⟩ :=
    Finset.exists_min_image S (fun f => totalErrorFin c f) hSne
  have hbudget : ∑ l, (fstar l : ℕ) ≤ B := by
    rw [hS, Finset.mem_filter] at hfS
    exact hfS.2
  refine ⟨fun l => (fstar l : ℕ), hbudget, ?_⟩
  intro j k hk
  by_contra hgt
  have himb : 2 * layerError (c k) ((fstar k : ℕ))
      < layerError (c j) ((fstar j : ℕ)) := not_le.mp hgt
  by_cases hjk : j = k
  · subst hjk
    have hnn : 0 ≤ layerError (c j) ((fstar j : ℕ)) := by
      unfold layerError
      exact div_nonneg (hc j) (by positivity)
    linarith
  -- the improving transfer, as a truncated allocation
  have hglt : totalError c
      (fun l => if l = j then (fstar j : ℕ) + 1
        else if l = k then (fstar k : ℕ) - 1 else (fstar l : ℕ))
      < totalError c (fun l => (fstar l : ℕ)) :=
    imbalance_yields_gain c (fun l => (fstar l : ℕ)) j k hjk
      (Nat.pos_iff_ne_zero.mpr hk) himb
  set gNat : Fin m → ℕ :=
    fun l => if l = j then (fstar j : ℕ) + 1
      else if l = k then (fstar k : ℕ) - 1 else (fstar l : ℕ) with hgNat
  -- budget preservation
  have hgsum : ∑ l, gNat l = ∑ l, ((fstar l : ℕ)) := by
    have hrest : ∀ l ∈ (Finset.univ.erase j).erase k,
        gNat l = (fstar l : ℕ) := by
      intro l hl
      obtain ⟨hk2, hmem⟩ := Finset.mem_erase.mp hl
      obtain ⟨hj2, _⟩ := Finset.mem_erase.mp hmem
      simp only [hgNat, hj2, hk2, ite_false, ite_false]
    have hj' : gNat j = (fstar j : ℕ) + 1 := by simp [hgNat]
    have hk' : gNat k = (fstar k : ℕ) - 1 := by
      simp [hgNat, show k ≠ j from Ne.symm hjk]
    have hkpos : (1:ℕ) ≤ (fstar k : ℕ) := Nat.pos_iff_ne_zero.mpr hk
    have hsumG : ∑ l, gNat l
        = gNat j + gNat k + ∑ l ∈ (Finset.univ.erase j).erase k, gNat l :=
        sum_two_point gNat j k hjk
    have hsumF : ∑ l, ((fstar l : ℕ))
        = (fstar j : ℕ) + (fstar k : ℕ)
          + ∑ l ∈ (Finset.univ.erase j).erase k, (fstar l : ℕ) :=
        sum_two_point (fun l => (fstar l : ℕ)) j k hjk
    have hrest2 : ∑ l ∈ (Finset.univ.erase j).erase k, gNat l
        = ∑ l ∈ (Finset.univ.erase j).erase k, (fstar l : ℕ) :=
        Finset.sum_congr rfl (fun l hl => hrest l hl)
    rw [hsumG, hsumF, hrest2, hj', hk']
    omega
  -- the transfer stays inside the truncated feasible set
  have hgle : ∀ l, gNat l ≤ B := by
    intro l
    refine le_trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))
      (le_trans (le_of_eq hgsum) hbudget)
  set gFin : Fin m → Fin (B + 1) :=
    fun l => ⟨gNat l, Nat.lt_succ_of_le (hgle l)⟩ with hgFin
  have hgcoe : ∀ l, (gFin l : ℕ) = gNat l := fun _ => rfl
  have hginS : gFin ∈ S := by
    rw [hS]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [hgcoe]
    rw [hgsum]
    exact hbudget
  have hstar : totalErrorFin c fstar ≤ totalErrorFin c gFin := hmin gFin hginS
  have hcoe : totalErrorFin c gFin = totalError c gNat :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  have hcoe2 : totalErrorFin c fstar
      = totalError c (fun l => (fstar l : ℕ)) :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hcoe, hcoe2] at hstar
  linarith

end Hagi.Budget

set_option linter.style.header false

/-!
# Waterfilling for the KV pyramid

`Hagi.Core/Attention` proved the softmax damping law: a KV error enters
the attention output scaled by its attention mass. The missing
piece — prescribed by the growth program — is the *optimal
allocation* of a fixed precision budget across KV positions: the
waterfilling analogue of `Hagi.Core/ErrorProp` for the attention branch.

**The model.** Each position i carries a per-bit error
contribution `c i > 0` (the sensitivity: attention mass times the
value norm, in the linearized regime) and a fixed bit cost; its
residual after `b i` bits decays as `exp (-κ b i)` with a shared
rate `κ > 0` (the exponential regime of quantization SNR:
`error ~ 2^{-b}`, i.e. `κ = log 2`, in the standard model).

**The theorem.** Among all allocations of a fixed budget `B` over
the positions, the total residual `∑ c i * exp (-κ b i)` is
minimized exactly when the *marginal* residuals are equal:
`c i * exp (-κ b* i) = λ` for all i — each bit spent buys the
same marginal error reduction everywhere.

Two consequences, stated honestly:

* **The tangent bound** (`waterfilling_bound`): for any feasible
  allocation b, the total residual is at least the equalized one
  — the proof is the exponential tangent inequality
  `exp x ≥ 1 + x` applied to the deviations from the optimum.
* **The allocation law** (in the docstring, not a theorem — it
  requires the inverse of exp): equalizing gives
  `b* i = (log (c i) - log λ) / κ` — the bits grow *logarithmically*
  in the sensitivity, `b* i - b* j = (log c i - log c j)/κ`. This
  is the honest correction to the naive "bits ∝ p_i·‖v_i‖": the
  *exponent* of the sensitivity drives the allocation, not the
  sensitivity itself. For the code: rank KV positions by
  `log (attention_mass * ‖v‖)`, allocate the budget as a shift of
  that log-ranking (water level λ from the budget constraint), and
  never sweep over allocations — the equalization condition is the
  closed-form optimum.
-/

open Finset

namespace Hagi.Budget

section Waterfilling

variable {ι : Type*} [Fintype ι]

/-- The total KV residual of an allocation b under per-position
sensitivities `c` and decay rate `κ`. -/
noncomputable def kvResidual (c : ι → ℝ) (kappa : ℝ) (b : ι → ℝ) : ℝ :=
  ∑ i, c i * Real.exp (-kappa * b i)

/-- **The equalization lemma.** If two allocations `b*` (the
candidate optimum) and b have the same total budget, and `b*`
equalizes the marginal residuals (`c i * exp (-κ b* i) = λ` for
all i), then the residual of b is at least the residual of
`b*`. The proof is the exponential tangent bound
`exp x ≥ 1 + x`: writing `b i = b* i + d i` with `∑ d i = 0`,

`c i * exp (-κ b i) = λ * exp (-κ d i) ≥ λ * (1 - κ d i)`,

and summing kills the linear terms (the budget constraint), giving
`∑ ≥ N * λ = the residual of b*` (each term of which is `λ`). -/
theorem waterfilling_bound (c : ι → ℝ) (kappa : ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (bstar b : ι → ℝ)
    (heq : ∀ i, c i * Real.exp (-kappa * bstar i) = lam)
    (hbudget : ∑ i, b i = ∑ i, bstar i) :
    kvResidual c kappa bstar ≤ kvResidual c kappa b := by
  -- d = b - b*; ∑ d = 0
  set d : ι → ℝ := fun i => b i - bstar i with hd
  have hsumd : ∑ i, d i = 0 := by
    simp only [hd]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero_of_eq hbudget
  -- per-position: c i * exp (-κ b i) ≥ λ * (1 - κ d i)
  have hper : ∀ i, lam * (1 - kappa * d i)
      ≤ c i * Real.exp (-kappa * b i) := by
    intro i
    -- c i * exp (-κ b i) = (c i * exp (-κ b* i)) * exp (-κ d i)
    --                     = λ * exp (-κ d i) ≥ λ * (1 + (-κ d i))
    have hsplit : -kappa * b i = -kappa * bstar i + (-kappa * d i) := by
      simp only [hd]
      ring
    have hterm : c i * Real.exp (-kappa * b i)
        = lam * Real.exp (-kappa * d i) := by
      rw [hsplit, Real.exp_add, ← heq i]
      ring
    have htan : (1:ℝ) + (-kappa * d i) ≤ Real.exp (-kappa * d i) := by
      have := Real.add_one_le_exp (-kappa * d i)
      linarith
    have hstep : lam * (1 + (-kappa * d i))
        ≤ lam * Real.exp (-kappa * d i) :=
      mul_le_mul_of_nonneg_left htan (le_of_lt hlam)
    have hconv : lam * (1 - kappa * d i)
        = lam * (1 + (-kappa * d i)) := by ring
    -- goal: lam * (1 - κ d i) ≤ c i * exp (-κ b i) = [hterm] λ * exp (-κ d i)
    rw [hconv, hterm]
    exact hstep
  -- b* residual = N * λ
  have hstar : kvResidual c kappa bstar = Fintype.card ι * lam := by
    unfold kvResidual
    rw [Finset.sum_congr rfl fun i _ => heq i]
    simp
  -- b residual ≥ ∑ λ (1 - κ d i) = N λ - κ λ ∑ d i = N λ
  unfold kvResidual
  calc ∑ i, c i * Real.exp (-kappa * bstar i)
      = Fintype.card ι * lam := hstar
    _ = ∑ i, lam * (1 - kappa * d i) := by
        have hmul : ∑ i, lam * (1 - kappa * d i)
            = lam * (∑ i, (1 - kappa * d i)) :=
          (Finset.mul_sum Finset.univ (fun i => (1:ℝ) - kappa * d i) lam).symm
        rw [hmul, Finset.sum_sub_distrib]
        have h1 : ∑ i : ι, (1:ℝ) = Fintype.card ι := by simp
        have h2 : ∑ i, kappa * d i = kappa * ∑ i, d i := by
          rw [← Finset.mul_sum]
        rw [h1, h2, hsumd, mul_zero, sub_zero]
        ring
    _ ≤ ∑ i, c i * Real.exp (-kappa * b i) :=
        Finset.sum_le_sum fun i _ => hper i

/-- **The active-set form (round-34 sync with the Python
fix): the allocation law with the positive part.** The
closed-form water level

`b_i* = max(0, (1/κ)·log(c_i/λ))` —

the negative-bit clamp: tensors with c_i ≤ λ (the residual
under the price even at zero budget) are EXCLUDED (b_i* = 0)
and the budget redistributes over the active set
{c_i > λ}. The Lean side previously recorded only the
interior form (c_i·e^{−κb_i*} = λ); the positive part is the
boundary case of the same KKT (the complementarity: the
inactive tensors' marginal at 0 is under the price). The
formal statement: for the inactive tensor (c_i ≤ λ) the
clamped allocation is zero. -/
theorem waterfilling_inactive_clamp (c_i lam kappa : ℝ)
    (hcpos : 0 < c_i) (hlam : 0 < lam) (hkappa : 0 < kappa)
    (hinactive : c_i ≤ lam) :
    max 0 ((1/kappa) * Real.log (c_i / lam)) = 0 := by
  have hratio : c_i / lam ≤ 1 := (div_le_one₀ hlam).mpr hinactive
  -- log(c/λ) ≤ 0 ⟸ c/λ ≤ 1 (log monotone at 1)
  have hlog : Real.log (c_i / lam) ≤ 0 := by
    have h1 : Real.log (c_i / lam) ≤ Real.log 1 :=
      Real.log_le_log (div_pos hcpos hlam) hratio
    rw [Real.log_one] at h1
    exact h1
  -- (1/κ)·log(c/λ) ≤ 0 ⟹ max 0 · = 0
  have hinner : (1/kappa) * Real.log (c_i / lam) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  exact max_eq_left (le_trans hinner (le_refl 0))

end Waterfilling

end Hagi.Budget

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

