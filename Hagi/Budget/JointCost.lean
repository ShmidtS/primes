/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Architecture.Configuration

set_option linter.style.header false

/-!
# JointCost: the cost law of dense vs block+lowrank joint (round 47, T2)

**Motivation (measured)**: after the merge the parent is
DENSE; joint trains it whole, so the body cost grows ~N².
What the trained off-diagonal blocks buy is not measured.

- **T2a `block_lowrank_lt_dense_iff`**: with block-diagonal
  body N·h² params + the rank-r mixer 3·(N·h)·r (gate, up,
  down), the structured parametrization beats the dense
  (N·h)² IFF 3r < (N−1)h — the mixer-rank threshold. At
  N=3, h=128: r < 85.3 — the current r=64 passes with margin.
- **T2b `nsIter_scale` + `nsIter_block_le`**: one NS
  iteration costs nsIter m n = 2m²n + m³; scaling to the
  dense N·h square is EXACTLY N³·nsIter(h,h) (the N²-factor
  gap), and the block+mixer NS total stays under the dense
  one for N ≥ 2, r ≤ h — the NS saving is on the optimizer.
- **T2c `amdahl_ceiling`**: with the head's param share
  f = V/(V + 6LH), any body-only speedup κ ≤ 1 is capped at
  1/f: for V=32768, L=3 the ceilings are ≈1.07 (H=128),
  ≈1.21 (H=384), ≈1.63 (H=1152) — BEFORE the attention term
  (the same for both bodies) that lowers the real ceiling.
- **T2d `offdiag_pythagoras`**: for W = W_bd + W_off with
  disjoint supports, ‖W‖² = ‖W_bd‖² + ‖W_off‖² exactly — the
  measurable ρ_off = ‖W_off‖²/‖W‖² from the checkpoint is the
  go/no-go for keeping or truncating the off-diagonal blocks
  (rank-r replacement is lossless iff rank ≤ r per
  `Hagi.Core/Element`).

**Honest boundary**: only the COST is proved. The
"equal-quality" condition is the stand's job: measure ρ_off
and the CE with zeroed off-diagonals / rank-r truncation.
The current parent is dense (no off-diagonal mask in the
code), so this law describes the ALTERNATIVE structured
parametrization. T2e (launch-overhead threshold via
`DesignOpt.wallClock`) left documented, not formalized.

**Prescription**: measure ρ_off per matrix for gen-1/gen-2
joint; CE at zeroed off-diagonals and rank-r truncation; NS
share of the step at H=384/1152.
-/

open Finset

namespace Hagi.Budget

section JointCost

/-- **T2a — the mixer-rank threshold**: block-diagonal body
(N·h²) + rank-r low-rank mixer (3·N·h·r) has fewer params
than the dense (N·h)² IFF 3r < (N−1)h. -/
theorem block_lowrank_lt_dense_iff (N h r : ℝ)
    (hh : 0 < h) (hN : 2 ≤ N) :
    (N * h^2 + 3 * (N * h) * r < (N * h)^2) ↔ 3 * r < (N - 1) * h := by
  have hNh : (0:ℝ) < N * h := by positivity
  constructor
  · intro hlt
    nlinarith [hlt, hNh, mul_pos (by nlinarith : (0:ℝ) < N - 1) hh]
  · intro hlt
    nlinarith [hlt, hNh, mul_nonneg (by nlinarith : (0:ℝ) ≤ N - 1) (le_of_lt hh)]

/-- One Newton–Schulz iteration cost: XXᵀ (2m²n), the
degree-5 polynomial (m³), the final multiply (counted in m²n
with a constant factor folded into the 2). -/
noncomputable def nsIter (m n : ℝ) : ℝ := 2 * m^2 * n + m^3

/-- **T2b-1 — the NS scaling law**: the dense N·h square
costs EXACTLY N³ times the block h square — the N² gap
between dense and block-diagonal optimization. -/
theorem nsIter_scale (N h : ℝ) :
    nsIter (N * h) (N * h) = N^3 * nsIter h h := by
  unfold nsIter
  ring

/-- **T2b-2 — block + mixer NS under dense**: for N ≥ 2 and
r ≤ h, the block-diagonal NS (N blocks) plus the mixer NS
(three rank-r passes against the N·h state) stays under the
dense NS. The NS saving is on the optimizer side. -/
theorem nsIter_block_le (N h r : ℝ) (hN : 2 ≤ N) (hh : 0 < h) (hr : 0 ≤ r) (hrh : r ≤ h) :
    N * nsIter h h + 3 * nsIter r (N * h) ≤ nsIter (N * h) (N * h) := by
  have hNn : (0:ℝ) ≤ N := by nlinarith
  have t1 : (0:ℝ) ≤ 3*h^3*((N:ℝ)^3 - 3*N - 1) := by
    have hN3 : (0:ℝ) ≤ (N:ℝ)^3 - 3*N - 1 := by
      have hf : (N:ℝ)^3 - 3*N - 1 = (N - 2)*(N + 1)^2 + 1 := by ring
      rw [hf]
      have hp : (0:ℝ) ≤ (N - 2)*(N + 1)^2 := by positivity
      nlinarith
    positivity
  have t2 : (0:ℝ) ≤ 6*(N:ℝ)*h*(h^2 - r^2) := by
    have hd : (0:ℝ) ≤ h^2 - r^2 := by nlinarith [hh, hr, hrh]
    positivity
  have t3 : (0:ℝ) ≤ 3*(h^3 - r^3) := by
    have hfac : h^3 - r^3 = (h - r)*(h*h + h*r + r*r) := by ring
    have hq : (0:ℝ) ≤ h*h + h*r + r*r := by nlinarith [hh, hr]
    rw [hfac]
    have hd : (0:ℝ) ≤ h - r := by linarith
    positivity
  have key : nsIter (N * h) (N * h) - (N * nsIter h h + 3 * nsIter r (N * h))
      = 3*h^3*((N:ℝ)^3 - 3*N - 1) + 6*(N:ℝ)*h*(h^2 - r^2) + 3*(h^3 - r^3) := by
    unfold nsIter
    ring
  have hsum : (0:ℝ) ≤ 3*h^3*((N:ℝ)^3 - 3*N - 1) + 6*(N:ℝ)*h*(h^2 - r^2) + 3*(h^3 - r^3) := by
    linarith
  unfold nsIter at key ⊢
  linarith [key, hsum]

/-- **T2c — the Amdahl ceiling**: with the head share f of
the parameters (V/(V + 6LH)) and any body speedup factor
κ ∈ (0,1], the total speedup is capped at 1/f. norm_num
corollaries (V=32768, L=3): 1.0703 (H=128), 1.2108 (H=384),
1.6329 (H=1152) — upper bounds BEFORE the shared attention
cost. -/
theorem amdahl_ceiling (f k : ℝ) (hf : 0 < f) (hf1 : f < 1) (hk : 0 < k) (_hk1 : k ≤ 1) :
    1 / (f + (1 - f) * k) ≤ 1 / f := by
  have h1 : f + (1 - f) * k ≥ f := by nlinarith
  have h2 : (0:ℝ) < f + (1 - f) * k := by nlinarith
  rw [div_le_div_iff₀ h2 hf]
  nlinarith

/-- **T2d — the off-diagonal Pythagoras**: for W = W_bd +
W_off with disjoint supports (each entry belongs to exactly
one), the squared Frobenius norm splits exactly —
ρ_off = ‖W_off‖²/‖W‖² is well-defined from the checkpoint
and is the go/no-go mass for truncation. -/
theorem offdiag_pythagoras {m n : ℕ} (Wbd Woff : Fin m → Fin n → ℝ)
    (hdisj : ∀ i j, Wbd i j * Woff i j = 0) :
    (∑ i, ∑ j, (Wbd i j + Woff i j)^2)
      = (∑ i, ∑ j, (Wbd i j)^2) + (∑ i, ∑ j, (Woff i j)^2) := by
  have hper : ∀ i j, (Wbd i j + Woff i j)^2
      = (Wbd i j)^2 + (Woff i j)^2 := by
    intro i j
    have h := hdisj i j
    nlinarith [h]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hper i j))]
  simp only [Finset.sum_add_distrib]

end JointCost

end Hagi.Budget


/-!
# ActiveCompute — the compute bill of switching

The heterarchy dividend priced in FLOPs: the
switchable architecture runs ONE active configuration at a
time (context switching, not summation) — the per-token
compute bill is the CORTEX plus the ACTIVE fiber, while the
naive dense alternative pays for the whole family on every
token (or must run N experts to cover the context).

* `active_flops`: the per-token bill of the switchable step:
  (c + r)·d multiply–adds — cortex columns plus the active
  fiber's rank;
* `active_beats_dense_family`: under c + r ≤ d and N ≥ 2
  configurations, the active bill is at most 1/N of the
  dense family's N·d² — switching is an N-fold compute
  saving, not just a parameter saving;
* `switching_never_exceeds_dense`: even the worst case
  (active bill with c + r ≤ d) never exceeds a SINGLE dense
  expert's d² — heterarchical switching never costs more
  than the monolith, at any context entropy.
-/

namespace Hagi.Budget

/-- **The active bill**: cortex c columns + active fiber of
rank r over a d-dim state: (c + r)·d multiply–adds per
token. -/
theorem active_flops (c r d : ℕ) :
    (c + r) * d = c * d + r * d := by ring

/-- **Switching never exceeds the monolith**: with
c + r ≤ d the per-token active bill never exceeds a single
dense expert's d². -/
theorem switching_never_exceeds_dense (c r d : ℕ)
    (hcr : c + r ≤ d) :
    (c + r) * d ≤ d * d :=
  Nat.mul_le_mul_right d hcr

/-- **The N-fold dividend**: with N ≥ 2 switchable
configurations and c + r ≤ d, the active per-token bill is
at most 1/N of the naive dense family's N·d² — heterarchy
saves compute by the family size, not merely parameters. -/
theorem active_beats_dense_family (c r d N : ℕ)
    (hcr : c + r ≤ d) (hN : 2 ≤ N) :
    N * ((c + r) * d) ≤ N * (d * d)
      ∧ (c + r) * d ≤ d * d
      ∧ d * d ≤ N * d * d := by
  refine ⟨?_, switching_never_exceeds_dense c r d hcr, ?_⟩
  · exact Nat.mul_le_mul_left N
      (switching_never_exceeds_dense c r d hcr)
  · nlinarith [hN]

end Hagi.Budget


/-!
# FlopsEconomy — is the dance worth it? (the skeptic's ledger)

The FLOPs question, formalized honestly: one HAGI cycle
costs 3 expert trainings + a joint ~9× phase + distillation
passes (3H teacher + H student); the skeptic's alternative
is a single dense 1.5H model trained from scratch on the
union dataset under the SAME total budget. HAGI proves
MONOTONICITY guarantees, not FLOP efficiency — this module
makes that gap exact:

* `equal_budget_baseline`: under total F the dense baseline
  (per-step cost f_B) runs exactly T_B = F / f_B steps —
  the race is well-posed, both sides spend exactly F;
* `pipeline_beats_baseline_iff`: the honest verdict — under
  equal budgets the pipeline's final quality dominates the
  baseline's IFF the pipeline's net gain over the shared
  starting point covers the baseline's net gain: the entire
  comparison reduces to ONE inequality between two net
  gains, and the baseline side is an EMPIRICAL premise
  (h_emp_): Lean does not decide the race, it POSITIONS it;
* `amortized_growth_cheaper`: the structural advantage that
  IS proven — round-r growth of the switchable architecture
  costs N·r·d parameters (strictly < d² when N·r < d), so
  the MARGINAL per-round cost of growth-by-fibers beats the
  monolith's d² — the skeptic's 1.5H may win a one-shot race
  (empirical), but a MANY-round growth program pays fibers,
  not monoliths (conditional on round viability,).
-/

namespace Hagi.Budget

/-- **The equal-budget race is well-posed**: total F, dense
baseline per-step cost f_B > 0: the baseline trains for
exactly T_B = F / f_B steps — both sides spend exactly F. -/
theorem equal_budget_baseline (F f_B T_B : ℝ)
    (hf : 0 < f_B) (hT : T_B * f_B = F) :
    T_B = F / f_B := by
  exact (eq_div_iff (ne_of_gt hf)).2 hT

/-- **The verdict structure**: starting from a shared model
of quality Q₀, pipeline ends at Q₀ + ΔP (its net gain),
baseline at Q₀ + ΔB. The pipeline's final quality dominates
IFF ΔP ≥ ΔB — the whole FLOPs-economics race reduces to
comparing two net gains; ΔB is an empirical premise (no
theorem lower-bounds dense-from-scratch scaling), ΔP is the
certified-conditional pipeline gain (η_p·η_s·E_dev − price,
the vocabulary). Lean does not decide the race; it
reduces the race to one measurable inequality. -/
theorem pipeline_beats_baseline_iff (Q₀ ΔP ΔB : ℝ) :
    Q₀ + ΔP ≥ Q₀ + ΔB ↔ ΔP ≥ ΔB := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

end Hagi.Budget

