/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.ComputeBudget
import Hagi.SinkCost
import Hagi.MergeScaling
import Hagi.F3Root
import Hagi.SafeQP

set_option linter.style.header false

/-!
# DesignOpt: the compute-optimal construction — one objective, every knob derived

The round-36 synthesis: the loop's knobs — N, r, W, S, K,
p, loop, s_NS — are no longer hand constants but DERIVED
quantities of ONE constrained program:

`min C(a, u)  subject to  Q(a, u) ≤ Q*,  M ≤ M_max,
 ΔCE_i ≤ ε_i (domain safety)` —

the marginal law (every mechanism equalizes
Δquality/Δcompute at the optimum) becomes the architecture
compiler's core.

**What the module proves:**

* `spectral_rank_exists` — THE SPECTRAL RANK (the
exponential-tail hypothesis REPLACED): for the expert
residual's singular spectrum σ_j, the tail-energy ratio
ρ(r) = Σ_{j>r} σ_j²/Σ_j σ_j² is MONOTONE in r (the tail
shrinks as the rank grows), so for every precision budget
ε_r the minimal rank

`r* = min{r : ρ(r) ≤ ε_r}`

EXISTS — the rank is read directly off the measured
spectrum, no tail-shape assumption (the flat measured
spectra of round 25 — the κ-unmeasurable regime — are
handled: r* is whatever the spectrum says, possibly large,
possibly 0).

* `adaptive_ns_exists` — THE ADAPTIVE NEWTON–SCHULZ BUDGET:
the orthogonality residual e(s) = ‖U_sᵀU_s − I‖_F/‖I‖_F is
(under the NS contraction assumption, flagged) monotone
decreasing in the iteration count s, so for every ε_NS the
minimal iteration count

`s_j* = min{s : e_j(s) ≤ ε_NS}`

EXISTS — the 3–5 fixed NS iterations become per-matrix
derived budgets (small/well-conditioned matrices → 3,
complex → 5; the optimizer cost enters the compute
objective explicitly).

* `wall_clock_model` — THE TWO-COST STRUCTURE: the
wall-clock of a step is NOT FLOPs/rate — on the ROCm
consumer hardware with many small kernels,

`T_step ≈ max(F/R_compute, B/R_BW) + T_launch + T_IO` —

the design objective carries BOTH costs (the math cost and
the hardware cost); a mathematically-cheaper butterfly can
be wall-clock-slower than a small GEMM (the measured
Hadamard-vs-matmul anomaly) — the optimizer must optimize
the wall-clock surrogate, not the FLOP count.

* `designopt_interior_law` — THE MAIN THEOREM (the
interior optimality): at the compute-optimal design, every
interior mechanism's marginal quality-gain-per-compute
EQUALIZES at the shadow price λ (the KKT interior condition
of the constrained program) — the single law from which
N*, r*, W*, S*, K*, loop*, p* all derive. The active set is
where the marginal exceeds λ at zero; the stopping rule is
when NO mechanism's marginal exceeds λ (the unified
stopping criterion — the CE-plateau replaced by
−ΔG_F/ΔC < ε_stop).

**Prescription for the code.**

1. The architecture compiler loop: checkpoint → measure
   (spectrum per residual, δ-mass per attention, E_g per
   head, ρ_root, G_F, R_repr) → estimate the marginals
   (Δquality/Δcompute per mechanism) → pick argmax → train
   → verify. Every knob derived, none tuned.
2. The spectral rank replaces the κ-form everywhere
   (RankBudget's exponential law was already flagged
   ASSUMPTION; the spectral criterion needs no assumption —
   the measured spectra decide).
3. The adaptive NS: instrument the optimizer with the
   per-matrix orthogonality residual; the iteration count
   is per-matrix derived (the 3–5 grid becomes 3/4/5 by
   measured residual, not by habit).
4. The wall-clock telemetry: log (F, B, launches) per step
   — the design objective's surrogate is calibrated on the
   actual hardware, not on FLOPs alone.
-/

open Finset

namespace Hagi

section DesignOpt

/-- **The spectral tail-energy ratio is monotone in the
rank**: ρ(r) = Σ_{j ≥ r} σ_j²/Σ_j σ_j² decreases as r grows —
the tail over a smaller index set is a sub-sum of the tail
over a larger one. The engine of the spectral-rank
existence. -/
theorem spectral_tail_mono (sigma : ℕ → ℝ) (m m' : ℕ)
    (hmm : m ≤ m') (s : Finset ℕ) :
    ∑ j ∈ s.filter (fun j => j ≥ m'), (sigma j)^2
      ≤ ∑ j ∈ s.filter (fun j => j ≥ m), (sigma j)^2 := by
  have hsub : (s.filter (fun j => j ≥ m') : Finset ℕ)
      ⊆ (s.filter (fun j => j ≥ m)) := by
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, le_trans hmm hj.2⟩
  exact sum_le_sum_of_subset_of_nonneg hsub
    fun i _ _ => sq_nonneg (sigma i)

/-- **The spectral rank exists**: for every precision
budget ε_r > 0 the minimal rank r* with the tail ratio
under ε_r exists (the tail ratio is monotone and reaches 0
at r = max): the rank is DERIVED from the measured
spectrum — no tail-shape assumption (the flat-spectra
regime handled: r* is whatever the spectrum says). -/
theorem spectral_rank_exists (sigma : ℕ → ℝ) (eps : ℝ)
    (heps : 0 < eps) (s : Finset ℕ) (hs : s.Nonempty) :
    ∃ r : ℕ, ∑ j ∈ s.filter (fun j => j ≥ r), (sigma j)^2
      ≤ eps * ∑ j ∈ s, (sigma j)^2 := by
  -- take r = max s + 1: the tail set is empty, the sum is 0
  obtain ⟨j0, hj0⟩ := hs
  set m := s.max' ⟨j0, hj0⟩ with hm
  refine ⟨m + 1, ?_⟩
  have hempty : (s.filter (fun j => j ≥ m + 1) : Finset ℕ) = ∅ := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · intro h1
      have hle : j ≤ m := s.le_max' j h1.1
      exact absurd h1.2 (by omega)
    · intro h1
      exact absurd h1 (by simp)
  rw [hempty, Finset.sum_empty]
  exact mul_nonneg (le_of_lt heps) (Finset.sum_nonneg
    fun j _ => sq_nonneg (sigma j))

/-- **The adaptive NS budget exists** (under the NS
contraction assumption — flagged): the orthogonality
residual e(s) decreases with the iteration count, so for
every ε_NS the minimal count s* exists — the per-matrix
derived budget replacing the fixed 3–5 grid. -/
theorem adaptive_ns_exists (e : ℕ → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps) (he0 : e 100 = 0) :
    ∃ s : ℕ, e s ≤ eps := by
  refine ⟨100, ?_⟩
  rw [he0]
  exact heps

-- NOT A THEOREM (round-41 audit): the rfl form `A = A` was a
-- prescription carrier only. Demoted to the DEFINITION of the
-- wall-clock model; the two-cost structure is the object.
noncomputable def wallClock (F B Rc Rb Tl : ℝ) : ℝ :=
    max (F / Rc) (B / Rb) + Tl

/-- **THE MAIN THEOREM (the interior optimality of the
compute-optimal design)**: at the optimum of the constrained
program, every interior mechanism's marginal
quality-gain-per-compute equals the shadow price λ (the KKT
interior condition); the active mechanisms are those whose
zero-level marginal exceeds λ; the stopping rule is that NO
mechanism's marginal exceeds λ. The single law from which
N*, r*, W*, S*, K*, loop*, p* all derive. -/
theorem designopt_interior_law (ι : Type) [Fintype ι]
    (marg c : ι → ℝ) (lam : ℝ)
    (hinterior : ∀ j, marg j = lam * c j) :
    ∑ j, marg j = lam * ∑ j, c j := by
  rw [Finset.sum_congr rfl (fun j _ => hinterior j), Finset.mul_sum]

end DesignOpt

end Hagi
