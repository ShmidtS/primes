/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.CurvatureSafe

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# R105: the derived safe step size for SafeQP (descent lemma, all domains simultaneously)

The last hand-tuned constant of the SafeQP loop is the learning
rate η for the step `θ − η·d*` along the projected direction
`d*` (the `Hagi.Step/SafeQP` minimizer of ½‖d − g‖² over the
safety half-spaces `⟪g_i, d⟫ ≥ −ε_i`). This module REPLACES
the tuning with a formula: the descent lemma for L-Lipschitz
gradients gives, per protected domain i,

`ΔL_i ≤ −η·⟪g_i, d*⟫ + (L_i/2)·η²·‖d*‖²`,   (h_lipline)

and with the SafeQP margin `m_i := ε_i + ⟪g_i, d*⟫ ≥ 0` the
per-domain regression stays within the budget ε_i for every
step size in the window

`η ≤ η_max := min(1, ⨅_i 2·m_i / (L_i·‖d*‖²))`.

**Exact algebra (the audit's constant, corrected).** Plugging
`⟪g_i, d*⟫ = m_i − ε_i` into the descent bound:

`ΔL_i ≤ η·ε_i + η·((L_i/2)·η·‖d*‖² − m_i)`.

The bracket is ≤ 0 exactly when `η ≤ 2·m_i/(L_i·‖d*‖²)`; the
leading `η·ε_i` is ≤ `ε_i` exactly when `η ≤ 1` (for ε_i ≥ 0).
So the audit's bare `min_i 2(ε_i + ⟪g_i,d*⟫)/(L_i‖d*‖²)` is the
correct window ONLY in the unit-step regime η ≤ 1 — the honest
closed form carries the unit clamp, and the clamp is free: no
gradient-descent step in the repo's regime exceeds 1. This is
the R105 companion of `safeqp_second_order` (which fixes ‖d*‖
and frees η; here η is DERIVED from the measured margins).

**What the module proves:**

* `safeqpEtaMax` — the explicit formula
  `min(1, ⨅_i 2(ε_i + ⟪g_i, d*⟫)/(L_i‖d*‖²))` (all inputs
  measurable: ε_i the guard budgets, L_i the measured
  Lipschitz constants, ⟨g_i, d*⟩ one inner product per domain).
* `safeqp_eta_max` — for ANY η ≤ η_max (with d* ≠ 0, L_i > 0,
  ε_i ≥ 0 and the per-domain descent-lemma bound h_lipline),
  NO domain regresses beyond its budget:
  `ΔL_i ≤ ε_i` for ALL i simultaneously.
* `safeqp_eta_zero_direction` — the degenerate case d* = 0:
  the step is the identity, every ΔL_i ≤ 0 ≤ ε_i, any η works
  (the window bound is vacuous, not false).
* `safeqp_eta_max_conflict_free` — the no-conflict corollary
  (⟪g_i, d*⟫ ≥ 0 for all i): the window simplifies to
  `min(1, ⨅_i 2ε_i/(L_i‖d*‖²))` — strictly positive whenever
  every budget is (`safeqpEtaMaxConflictFree_pos`): the
  controller's DERIVED learning rate, no tuning left.

**Prescription for the code:** the LR is not a constant to
sweep (0.01 → 0.001 in the empirical ledger) — it is
`safeqpEtaMax` evaluated on the measured (ε_i, L_i, ‖d*‖,
margins ⟨g_i, d*⟩) of the current step; the sweep disappears
into the descent lemma.
-/

namespace Hagi

open Real InnerProductSpace

section SafeQPStep

variable {K : Type*} [Fintype K] [Nonempty K]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The derived safe step size**: the explicit window

`η_max = min(1, ⨅_i 2(ε_i + ⟪g_i, d⟫)/(L_i·‖d‖²))`

from the descent lemma. All inputs are per-step measurable
quantities: the guard budgets ε_i, the Lipschitz constants L_i,
the projected direction norm ‖d*‖, and the margins
⟪g_i, d*⟫ (one inner product per protected domain). The unit
clamp is the honest correction to the audit's bare
`min_i 2(ε_i + ⟪g_i,d*⟫)/(L_i‖d*‖²)` (which controls the
quadratic bracket but not the `η·ε_i` leading term; see the
module docstring). -/
noncomputable def safeqpEtaMax (g : K → X) (eps L : K → ℝ) (d : X) : ℝ :=
  min 1 (⨅ i, 2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2))

/-- **The window, unpacked**: `η ≤ safeqpEtaMax` iff `η ≤ 1`
and η is under every per-domain threshold
`2(ε_i + ⟪g_i, d⟫)/(L_i·‖d‖²)`. -/
theorem le_safeqpEtaMax_iff (g : K → X) (eps L : K → ℝ) (d : X) {eta : ℝ} :
    eta ≤ safeqpEtaMax g eps L d ↔
      eta ≤ 1 ∧ ∀ i, eta ≤ 2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2) := by
  have hbd : BddBelow (Set.range fun i =>
      2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2)) :=
    Finite.bddBelow_range _
  rw [safeqpEtaMax, le_min_iff, le_ciInf_iff hbd]

/-- **The per-domain descent-lemma window (the scalar core).**
With the descent bound `dL ≤ −η·⟨g, d⟩ + (L/2)η²‖d‖²`
(the h_lipline hypothesis — the descent lemma for an
L-Lipschitz gradient along the direction d at step η), a
nonnegative budget ε, η in the unit window and under the
margin threshold `2(ε + ⟨g, d⟩)/(L·‖d‖²)`, the regression is
within budget: `dL ≤ ε`.

The algebra: with margin `m := ε + ⟨g, d⟩ ≥ 0` (forced by the
threshold itself),
`dL ≤ η·ε + η·((L/2)·η·‖d‖² − m) ≤ η·ε ≤ ε` —
the bracket is nonpositive by the threshold, the leading term
by η ≤ 1 and ε ≥ 0. -/
theorem safeqp_eta_max_domain (inner eps L dsq eta dL : ℝ)
    (hL : 0 < L) (hdsq : 0 < dsq) (heps : 0 ≤ eps)
    (heta : 0 ≤ eta) (hone : eta ≤ 1)
    (h_eta : eta ≤ 2 * (eps + inner) / (L * dsq))
    (h_lipline : dL ≤ -eta * inner + L * eta * eta * dsq / 2) :
    dL ≤ eps := by
  have hpos : 0 < L * dsq := by positivity
  have hmul : eta * (L * dsq) ≤ 2 * (eps + inner) := by
    rwa [le_div_iff₀ hpos] at h_eta
  -- the margin is nonnegative (forced by the window itself)
  have hm : 0 ≤ eps + inner := by
    have h0 : (0:ℝ) ≤ eta * (L * dsq) := mul_nonneg heta hpos.le
    linarith
  -- the quadratic bracket is nonpositive: (L/2)·η·dsq ≤ m
  have hkey : L * eta * eta * dsq / 2 ≤ eta * (eps + inner) := by
    have h2 : eta * (eta * (L * dsq)) ≤ eta * (2 * (eps + inner)) :=
      mul_le_mul_of_nonneg_left hmul heta
    nlinarith [h2]
  -- η·ε ≤ ε (unit step, nonnegative budget)
  have hee : eta * eps ≤ eps := by
    have : eta * eps ≤ 1 * eps :=
      mul_le_mul_of_nonneg_right hone heps
    linarith
  -- assemble: dL ≤ η·ε − η·m + (L/2)η²dsq ≤ ε
  have hsplit : -eta * inner = -eta * (eps + inner) + eta * eps := by ring
  linarith

/-- **The all-domains guarantee.** For the SafeQP direction
`d ≠ 0`, measured Lipschitz constants `L i > 0` and budgets
`ε i ≥ 0`, any step size `0 ≤ η ≤ safeqpEtaMax` under the
per-domain descent bound (h_lipline: the descent lemma for
L_i-Lipschitz gradients along d at step η) keeps EVERY
protected domain within its budget:

`ΔL_i ≤ ε_i for all i simultaneously`. -/
theorem safeqp_eta_max (g : K → X) (eps L : K → ℝ) (d : X) (dL : K → ℝ)
    (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMax g eps L d) :
    ∀ i, dL i ≤ eps i := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  obtain ⟨hone, hthr⟩ := (le_safeqpEtaMax_iff g eps L d).mp h_eta
  intro i
  exact safeqp_eta_max_domain ⟪g i, d⟫_ℝ (eps i) (L i) (‖d‖ ^ 2)
    eta (dL i) (hL i) hdsq (heps i) heta hone (hthr i) (h_lipline i)

/-- **The degenerate case d* = 0**: the step `θ − η·0` is the
identity on θ, and the descent bound collapses to
`ΔL_i ≤ 0 ≤ ε_i` — ANY η works; the window bound of
`safeqp_eta_max` is vacuous here (the direction is zero), not
false. -/
theorem safeqp_eta_zero_direction (g : K → X) (eps L : K → ℝ)
    (dL : K → ℝ) (eta : ℝ)
    (heps : ∀ i, 0 ≤ eps i)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, (0 : X)⟫_ℝ
      + L i * eta * eta * ‖(0 : X)‖ ^ 2 / 2) :
    ∀ i, dL i ≤ eps i := by
  intro i
  have h := h_lipline i
  rw [inner_zero_right, norm_zero] at h
  have h0 : L i * eta * eta * (0:ℝ) ^ 2 / 2 = 0 := by ring
  rw [h0] at h
  rw [mul_zero, add_zero] at h
  linarith [heps i]

/-- **The conflict-free derived LR**: with no conflicts
(`⟪g_i, d⟫ ≥ 0` for all i) every margin `m_i = ε_i + ⟪g_i,d⟫`
dominates the budget ε_i, and the window simplifies to
`min(1, ⨅_i 2ε_i/(L_i·‖d‖²))` — no inner products needed:
the budgets, the Lipschitz constants and the direction norm
alone determine the step. -/
noncomputable def safeqpEtaMaxConflictFree (eps L : K → ℝ) (d : X) : ℝ :=
  min 1 (⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2))

theorem le_safeqpEtaMaxConflictFree_iff (eps L : K → ℝ) (d : X) {eta : ℝ} :
    eta ≤ safeqpEtaMaxConflictFree eps L d ↔
      eta ≤ 1 ∧ ∀ i, eta ≤ 2 * eps i / (L i * ‖d‖ ^ 2) := by
  have hbd : BddBelow (Set.range fun i => 2 * eps i / (L i * ‖d‖ ^ 2)) :=
    Finite.bddBelow_range _
  rw [safeqpEtaMaxConflictFree, le_min_iff, le_ciInf_iff hbd]

/-- **The conflict-free window is strictly positive**: with
strictly positive budgets ε_i > 0, Lipschitz constants L_i > 0
and a nonzero direction, `safeqpEtaMaxConflictFree > 0` — the
derived LR is a genuine step size, not a degenerate zero. -/
theorem safeqpEtaMaxConflictFree_pos (eps L : K → ℝ) (d : X)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 < eps i) (hd : d ≠ 0) :
    0 < safeqpEtaMaxConflictFree eps L d := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  -- every per-domain threshold is strictly positive
  have hthr : ∀ i : K, (0:ℝ) < 2 * eps i / (L i * ‖d‖ ^ 2) := by
    intro i
    have hp : (0:ℝ) < L i * ‖d‖ ^ 2 := by nlinarith [hL i, hdsq]
    exact div_pos (mul_pos two_pos (heps i)) hp
  -- the iInf over a nonempty finite type is attained (the min'
  -- of the image finset); a finite infimum of strictly positive
  -- thresholds is strictly positive
  have hEq : (⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2) : ℝ)
      = ((Finset.univ.image
          fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _)) := by
    classical
    have h1 : ((Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _))
        = (Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).inf'
        (Finset.univ_nonempty.image _) id := rfl
    have h2 : (Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).inf'
        (Finset.univ_nonempty.image _) id
        = Finset.univ.inf' Finset.univ_nonempty
          fun i => 2 * eps i / (L i * ‖d‖ ^ 2) := by
      simp [Finset.inf'_image]
    rw [h1, h2, Finset.inf'_univ_eq_ciInf]
  have hminmem : ((Finset.univ.image
        fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
      (Finset.univ_nonempty.image _))
      ∈ Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2) :=
    Finset.min'_mem _ _
  obtain ⟨i, hi⟩ : ∃ i : K,
      2 * eps i / (L i * ‖d‖ ^ 2)
        = (Finset.univ.image
            fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _) := by
    simpa using hminmem
  have hinf : (0:ℝ) < ⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2) := by
    rw [hEq, ← hi]
    exact hthr i
  rw [safeqpEtaMaxConflictFree, lt_min_iff]
  exact ⟨by norm_num, hinf⟩

/-- **The conflict-free corollary (the controller's derived
LR).** With no conflicts (`⟪g_i, d⟫ ≥ 0` for all i), any
`0 ≤ η ≤ safeqpEtaMaxConflictFree ε L d` keeps every domain
within budget — the learning rate is `min(1, ⨅_i 2ε_i/(L_i‖d‖²))`,
strictly positive by `safeqpEtaMaxConflictFree_pos`: a formula
of the measured (ε_i, L_i, ‖d‖), not a swept constant. -/
theorem safeqp_eta_max_conflict_free (g : K → X) (eps L : K → ℝ)
    (d : X) (dL : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (hnc : ∀ i, 0 ≤ ⟪g i, d⟫_ℝ)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMaxConflictFree eps L d) :
    ∀ i, dL i ≤ eps i := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  obtain ⟨hone, hthr⟩ :=
    (le_safeqpEtaMaxConflictFree_iff eps L d).mp h_eta
  -- every conflict-free threshold implies the margin threshold
  have hmargin : ∀ i, eta ≤ 2 * (eps i + ⟪g i, d⟫_ℝ)
      / (L i * ‖d‖ ^ 2) := by
    intro i
    have hpos : 0 < L i * ‖d‖ ^ 2 := mul_pos (hL i) hdsq
    have hle : 2 * eps i ≤ 2 * (eps i + ⟪g i, d⟫_ℝ) := by
      have : 0 ≤ 2 * ⟪g i, d⟫_ℝ := mul_nonneg two_pos.le (hnc i)
      linarith
    have h1 : eta * (L i * ‖d‖ ^ 2) ≤ 2 * eps i :=
      (le_div_iff₀ hpos).mp (hthr i)
    exact le_trans (hthr i)
      ((div_le_div_iff₀ hpos hpos).mpr (by nlinarith [h1, hle]))
  exact safeqp_eta_max g eps L d dL eta hL heps heta hd h_lipline
    ((le_safeqpEtaMax_iff g eps L d).mpr ⟨hone, hmargin⟩)

end SafeQPStep

end Hagi
