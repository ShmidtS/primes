/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.ComputeToQuality
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Curriculum certificates: phase accounting and dependency chains

The training-curriculum beat (frontier item #2 of
`.omc/analysis/period-c330-c335-analysis.md`): does data ORDERING
provably matter?  The honest answer has two halves, both landed as
theorems:

* ORDER-FREE (the negative result, stated precisely): within
  phase-rate accounting — a fixed two-phase schedule where each phase
  is an interval of certified steps with its OWN uniform drop
  (per-phase descent-rate premise on the C291 carrier's interface,
  composed exactly as C330 `steps_to_quality` does per phase) — the
  total bound is the SYMMETRIC sum `n₁·d₁ + n₂·d₂` and the idealized
  total `curriculumTotal Δ₁ Δ₂ d₁ d₂ = Δ₁/d₁ + Δ₂/d₂` commutes
  (`curriculumTotal_comm`).  The certificate cannot distinguish the
  phase orders (`curriculum_phase_accounting_swap`): ordering per se
  is NOT certified to matter in the sum decomposition.

* DEPENDENCY-ORDERED (where order IS constitutive): the one honest
  mechanism is the warm-up premise — a later phase's rate may be
  certified only GIVEN an earlier phase's endpoint (e.g. C315-style
  margin conditions unlocked at quality `q₁`).  `curriculum_
  dependency_chain` carries phase 2's drop premise as a CONDITIONAL
  (`objective (t n₁) ≤ q₁ → d₂ ≤ drop`), the phase-1 certificate
  discharges it, and phase 2 telescopes from its OWN endpoint (gap
  premise at `t n₁`, not `t 0`).  The REVERSED order is not slower —
  it is UNCERTIFIED: the conditional premise has no discharged
  antecedent.  The certification, not optimality, is the content.

Carriers (all landed, CITED not re-proved): C291
`Hagi.Model.CEDescent` (the descent rate: at the safe step the
certified drop is exactly `2·A²/R²` per `ceOneHot_safeStep_le_
residual` — no constant is baked in here), C278 `Hagi.Cert.CertStepGen`
(the drop field + `trajectory_telescope_gen`), C330
`Hagi.Contracts.ComputeToQuality` (`steps_to_quality`,
`budget_telescope_gen`).

Honest scope: fixed two-phase schedule (no adaptive curriculum
selection — YAGNI: the 2-phase form carries the whole content);
deterministic descent premises only (the C330 interface); no claim
that certified ⇒ empirically better; numbers live in the numeric
`Anchor` lemmas only.
-/

set_option linter.style.header false

namespace Hagi.Contracts.CurriculumCert

variable {S TaskId : Type*}
variable (M : Hagi.Cert.SystemMetrics S TaskId) (obl : Hagi.Cert.StepObligations TaskId)

/-! ## The idealized two-phase total (order-free bookkeeping) -/

/-- **Curriculum total** — the idealized per-phase minimal-witness
bookkeeping functional: phase i contributes `Δᵢ/dᵢ` (its gap over its
uniform certified drop; the C330 `totalComputeProduct` shape per
phase). -/
noncomputable def curriculumTotal (Δ₁ Δ₂ d₁ d₂ : ℝ) : ℝ := Δ₁ / d₁ + Δ₂ / d₂

/-- **The order-free negative result, exact form**: the idealized
two-phase total COMMUTES — `curriculumTotal Δ₁ Δ₂ d₁ d₂ =
curriculumTotal Δ₂ Δ₁ d₂ d₁`. Within the sum decomposition, nothing
distinguishes the phase order: the certificate value of a curriculum
schedule is symmetric (the honest limit of phase-rate accounting). -/
theorem curriculumTotal_comm (Δ₁ Δ₂ d₁ d₂ : ℝ) :
    curriculumTotal Δ₁ Δ₂ d₁ d₂ = curriculumTotal Δ₂ Δ₁ d₂ d₁ := by
  unfold curriculumTotal; ring

/-! ## MAIN 1: phase-rate accounting (order-free) -/

/-- **MAIN 1 — curriculum phase accounting**: a mixed two-phase
curriculum on ONE trajectory (phase 1 = certified steps [0, n₁) with
uniform drop `d₁`; phase 2 = steps [n₁, n₁+n₂) with uniform drop `d₂`)
closes the total gap in the SUM of the per-phase drops: with
`Δ₀ = objective (t 0) − ε ≤ n₁·d₁ + n₂·d₂`, the quality floor is met
after `n₁+n₂` steps. The bound is the symmetric sum — see
`curriculum_phase_accounting_swap` for what that does and does NOT
say about ordering. -/
theorem curriculum_phase_accounting (deltaLevel : S → ℝ)
    (ε d₁ d₂ : ℝ) (n₁ n₂ : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd1 : ∀ j ∈ Finset.range n₁, d₁ ≤ (steps j).drop)
    (hd2 : ∀ j ∈ Finset.range n₂, d₂ ≤ (steps (n₁ + j)).drop)
    (hgap : M.objective (t 0) - ε ≤ n₁ * d₁ + n₂ * d₂) :
    M.objective (t (n₁ + n₂)) ≤ ε := by
  have htel := Hagi.Cert.trajectory_telescope_gen M obl deltaLevel (n₁ + n₂) t steps
  rw [Finset.sum_range_add (fun j => (steps j).drop) n₁ n₂] at htel
  have h1 : n₁ * d₁ ≤ ∑ j ∈ Finset.range n₁, (steps j).drop := by
    calc n₁ * d₁ = ∑ _j ∈ Finset.range n₁, d₁ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range n₁, (steps j).drop := Finset.sum_le_sum hd1
  have h2 : n₂ * d₂ ≤ ∑ j ∈ Finset.range n₂, (steps (n₁ + j)).drop := by
    calc n₂ * d₂ = ∑ _j ∈ Finset.range n₂, d₂ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range n₂, (steps (n₁ + j)).drop := Finset.sum_le_sum hd2
  linarith

/-- **MAIN 1, swap corollary — the honest order-free statement**: the
SAME conclusion holds for the phase-swapped schedule (the `d₂`-steps
first, `n₂` of them, then `n₁` steps of `d₁`) under the swapped
interval premises. The certificate cannot distinguish the two orders:
phase-rate accounting is provably SYMMETRIC — ordering per se is NOT
certified to matter within the sum decomposition (the negative result
of this beat, stated as a theorem rather than hidden). -/
theorem curriculum_phase_accounting_swap (deltaLevel : S → ℝ)
    (ε d₁ d₂ : ℝ) (n₁ n₂ : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd2' : ∀ j ∈ Finset.range n₂, d₂ ≤ (steps j).drop)
    (hd1' : ∀ j ∈ Finset.range n₁, d₁ ≤ (steps (n₂ + j)).drop)
    (hgap : M.objective (t 0) - ε ≤ n₂ * d₂ + n₁ * d₁) :
    M.objective (t (n₂ + n₁)) ≤ ε :=
  curriculum_phase_accounting M obl deltaLevel ε d₂ d₁ n₂ n₁ t steps hd2' hd1' hgap

/-! ## MAIN 2: the dependency chain (where order IS constitutive) -/

/-- **MAIN 2 — curriculum dependency chain**: the dependency-ordered
two-phase certificate. Phase 1 has the UNCONDITIONAL rate `d₁` and
closes to the intermediate gate `q₁` (`objective (t 0) − q₁ ≤ n₁·d₁`
⟹ `objective (t n₁) ≤ q₁`, the C330 `steps_to_quality`). Phase 2's
rate `d₂` is the phase-conditional value `d₂(q₁)` — its drop premise
is certified ONLY UNDER the phase-1 endpoint (`hd2` is a CONDITIONAL
premise: `objective (t n₁) ≤ q₁ → d₂ ≤ drop_j`; the warm-up reading:
e.g. C315-style margin conditions unlocked at quality q₁). The chain
closes by construction: the phase-1 certificate DISCHARGES the
condition, and phase 2 telescopes from its OWN endpoint (the gap
premise is `objective (t n₁) − ε ≤ n₂·d₂`, measured at the phase-1
output, not at `t 0` — the chain bookkeeping).

Honest scope: the REVERSED order is not slower — it is UNCERTIFIED:
with phases reversed the conditional premise has no discharged
antecedent (nothing certifies `objective ≤ q₁` at the new phase
boundary). The certification, not optimality, is the content; the
idealized dependency total `Δ₁/d₁ + Δ₂/d₂(q₁)` is NOT symmetric
against `curriculumTotal_comm`'s — the second term is evaluated at
the achieved quality. -/
theorem curriculum_dependency_chain (deltaLevel : S → ℝ)
    (ε q₁ d₁ d₂ : ℝ) (n₁ n₂ : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd1 : ∀ j ∈ Finset.range n₁, d₁ ≤ (steps j).drop)
    (hgap1 : M.objective (t 0) - q₁ ≤ n₁ * d₁)
    (hd2 : ∀ j ∈ Finset.range n₂,
      M.objective (t n₁) ≤ q₁ → d₂ ≤ (steps (n₁ + j)).drop)
    (hgap2 : M.objective (t n₁) - ε ≤ n₂ * d₂) :
    M.objective (t n₁) ≤ q₁ ∧ M.objective (t (n₁ + n₂)) ≤ ε := by
  refine ⟨Hagi.Contracts.ComputeToQuality.steps_to_quality M obl deltaLevel
    q₁ d₁ n₁ t steps hd1 hgap1, ?_⟩
  exact Hagi.Contracts.ComputeToQuality.steps_to_quality M obl deltaLevel
    ε d₂ n₂ (fun j => t (n₁ + j)) (fun j => steps (n₁ + j))
    (fun j hj => hd2 j hj
      (Hagi.Contracts.ComputeToQuality.steps_to_quality M obl deltaLevel
        q₁ d₁ n₁ t steps hd1 hgap1)) hgap2

/-! ## The packaging certificate -/

/-- **MAIN 3 — the curriculum certificate** (three books, the C330
`compute_budget_certificate` shape): the dependency-ordered schedule
simultaneously closes the INTERMEDIATE gate (`objective (t n₁) ≤ q₁`),
the FINAL floor (`objective (t (n₁+n₂)) ≤ ε`, the chain), and the
compute ledger exactly (`budget (t (n₁+n₂)) = budget (t 0) −
(n₁+n₂)·W`, the C330 `budget_telescope_gen` over the concatenated
schedule). One certificate, three books. -/
theorem curriculum_certificate (deltaLevel : S → ℝ)
    (ε q₁ d₁ d₂ W : ℝ) (n₁ n₂ : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hd1 : ∀ j ∈ Finset.range n₁, d₁ ≤ (steps j).drop)
    (hgap1 : M.objective (t 0) - q₁ ≤ n₁ * d₁)
    (hd2 : ∀ j ∈ Finset.range n₂,
      M.objective (t n₁) ≤ q₁ → d₂ ≤ (steps (n₁ + j)).drop)
    (hgap2 : M.objective (t n₁) - ε ≤ n₂ * d₂)
    (hW : ∀ j ∈ Finset.range (n₁ + n₂), (steps j).budgetSpend = W) :
    M.objective (t n₁) ≤ q₁
      ∧ M.objective (t (n₁ + n₂)) ≤ ε
      ∧ M.budget (t (n₁ + n₂)) = M.budget (t 0) - (n₁ + n₂) * W := by
  refine ⟨(curriculum_dependency_chain M obl deltaLevel ε q₁ d₁ d₂ n₁ n₂ t
    steps hd1 hgap1 hd2 hgap2).1, ?_, ?_⟩
  · exact (curriculum_dependency_chain M obl deltaLevel ε q₁ d₁ d₂ n₁ n₂ t
      steps hd1 hgap1 hd2 hgap2).2
  · have hbt := Hagi.Contracts.ComputeToQuality.budget_telescope_gen M obl
      deltaLevel (n₁ + n₂) t steps
    rw [Finset.sum_congr rfl (fun j hj => hW j hj),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add] at hbt
    exact hbt

/-! ## Numeric anchors: Δ₁ = Δ₂ = 1, d₁ = 0.1, d₂ = 0.05 after q₁ -/

namespace Anchor

/-- The anchor curriculum total: with phase-1 gap 1 at rate 1/10 and
phase-2 gap 1 at the warm-up rate 1/20 (= 0.05, certified only after
q₁), the idealized total is 10 + 20 = 30 certified steps (norm_num). -/
theorem anchor_total : curriculumTotal 1 1 ((1 : ℝ) / 10) ((1 : ℝ) / 20) = 30 := by
  unfold curriculumTotal; norm_num

/-- The anchor, SWAPPED: the order-free accounting gives the SAME
number 30 with the phases exchanged — the symmetry of
`curriculumTotal_comm` at anchor values (norm_num). Note this is the
ACCOUNTING reading only: it does NOT certify the swapped schedule
under the dependency premise `d₂(q₁)` (that certificate does not
transfer — MAIN 2's honesty point). -/
theorem anchor_total_swap :
    curriculumTotal 1 1 ((1 : ℝ) / 20) ((1 : ℝ) / 10) = 30 := by
  unfold curriculumTotal; norm_num

end Anchor

end Hagi.Contracts.CurriculumCert
