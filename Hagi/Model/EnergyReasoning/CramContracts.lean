/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Cert.Core
import Hagi.Energy.SingleCellDescent
import Hagi.Model.EnergyReasoning.PseudolikelihoodLocalField
import Hagi.Model.EnergyReasoning.EnergyStopping

set_option linter.style.header false

/-!
# Typed CRAM transition contracts with Cert-kernel bridge

Track E-bridge B3 (addendum A11 bridge B3): CRAM transitions
become TYPED premise-form contracts over a `CRAMState` carrier
with exact resource laws (budget' = budget − cost, nonnegative
remainder), bridged into the canonical certification kernel
`Hagi.Cert` so the certified telescope applies.

* `MetricDirection` — the typed metric polarity: `UtilityFloor`
  (higher is better; obligations are lower floors) vs
  `LossCeiling` (lower is better — energy/loss descent;
  obligations are upper ceilings).  `MetricDirection.kept` and
  `MetricDirection.improves` are the direction-indexed
  obligation/improvement predicates; the negation bridge
  `MetricDirection.kept_lossCeiling_neg` is THE polarity fix for
  the kernel's floor-form `FloorsKept`: a loss is read by
  negating the objective, typed and explicit instead of confused.
* `CRAMState` — the transition carrier: problem, board, optional
  latent, budgets (search with natural numbers, compute real),
  remaining risk and delta, with componentwise extensionality.
* `CRAMTrainStep` — parameter-training contract on the free-cell
  pseudolikelihood objective: MEASURED-drop premise (no gradient
  proof, no convergence claim) plus exact budget laws;
  `CRAMTrainStep.measured_of_majorizer` is the majorizer entry
  (surrogate anchored at the old parameters).
* `CRAMEnergyDescentStep` — single-cell energy descent from the
  C261 strict-drop margin, with MarginBudget accounting (the
  certified margin is deducted from the risk remainder);
  `strictDrop` reuses `strict_drop_of_positive_margin` verbatim;
  `toLossCeilingDrop` wires the LossCeiling polarity.
* `CRAMExplorationStep` — legal exploration transition: positive
  kernel mass, row-stochastic kernel premise (the C263
  `mixture_rowsum` premise shape), clamps (givens) preserved,
  search budget consumed.  NO DESCENT CLAIM: exploration may
  RAISE the energy (stationarity is not monotonicity).
* `CRAMAcceptedSolution` — production certificate: a
  `ValidityCertificate` (givens preserved + constraints
  satisfied, C263 `EnergyStopping`) agreeing with the board,
  with an OPTIONAL energy bound.
* `CRAMEnergyDescentStep.toKernelCertStep` — the canonical-kernel
  bridge (pattern: `HonestTransition.toKernelCertStep`, C254):
  under explicit metric-readout premises the descent step is a
  `Hagi.Cert.CertStep`, so the kernel telescope applies.
* `HoldStep.cram_state_components` — a kernel hold on the CRAM
  carrier fixes the FULL state (problem, board, latent, budgets,
  risk, delta): Hold = full state equality, documented.

## Honest boundaries

* Train step: the measured drop and the majorizer properties are
  PREMISES; the gradient formula exists
  (`pseudolikelihood_freeCell_B_gradient`) but no descent is
  proven from it here.
* Exploration makes NO descent claim and carries no energy field.
* Accepted solution: validity says nothing about energy (E4
  separation) — the energy bound is optional data.
* The kernel adapter's metric readouts are explicit premises; no
  ambient `SystemMetrics` is postulated for `CRAMState`.
* `MetricDirection.kept_floor_iff` (the reverse direction) needs
  `[Nonempty TaskId]`: with an empty task space the kernel's
  `FloorsKept` is vacuous — the premise is load-bearing, not
  decoration.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (pairwiseEnergy localField)

/-! ## Typed metric polarity -/

/-- The typed metric polarity.  `UtilityFloor`: higher objective
is better, obligations are LOWER floors (`floor ≤ objective`).
`LossCeiling`: lower objective is better — energy/loss descent —
obligations are UPPER ceilings (`objective ≤ ceiling`). -/
inductive MetricDirection where
  /-- Utility polarity: obligations are floors. -/
  | UtilityFloor
  /-- Loss/energy polarity: obligations are ceilings. -/
  | LossCeiling

/-- Direction-indexed kept-obligation predicate: at level `lvl`,
the state `s` keeps its obligation w.r.t. the readout `obj`. -/
def MetricDirection.kept {S : Type*} (dir : MetricDirection)
    (obj : S → ℝ) (lvl : ℝ) (s : S) : Prop :=
  match dir with
  | UtilityFloor => lvl ≤ obj s
  | LossCeiling => obj s ≤ lvl

/-- Direction-indexed improvement: the readout improves from `s`
to `s'` by at least `δ` in the direction's polarity. -/
def MetricDirection.improves {S : Type*} (dir : MetricDirection)
    (obj : S → ℝ) (s s' : S) (δ : ℝ) : Prop :=
  match dir with
  | UtilityFloor => obj s + δ ≤ obj s'
  | LossCeiling => obj s' ≤ obj s - δ

/-- Forward bridge to the kernel floor contract: a kept
UtilityFloor obligation implies the kernel's `FloorsKept` at the
constant floor `lvl` (always, without any premise on the task
space). -/
theorem MetricDirection.kept_floor_forwards {S TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics S TaskId) (lvl : ℝ) (s : S)
    (h : MetricDirection.kept MetricDirection.UtilityFloor
        M.objective lvl s) :
    Hagi.Cert.FloorsKept M { floor := fun _ => lvl } s :=
  fun _ => h

/-- Reverse bridge: the kernel's `FloorsKept` at a constant floor
implies the kept UtilityFloor obligation, PROVIDED a task tag
exists — with an empty task space `FloorsKept` is vacuous, so the
`[Nonempty TaskId]` premise is honest and load-bearing. -/
theorem MetricDirection.kept_floor_iff {S TaskId : Type*}
    [Nonempty TaskId] (M : Hagi.Cert.SystemMetrics S TaskId)
    (lvl : ℝ) (s : S)
    (h : Hagi.Cert.FloorsKept M { floor := fun _ => lvl } s) :
    MetricDirection.kept MetricDirection.UtilityFloor M.objective
        lvl s :=
  h (Classical.arbitrary TaskId)

/-- THE polarity fix, typed: a LossCeiling obligation at ceiling
`c` is exactly a UtilityFloor obligation at floor `−c` for the
NEGATED objective — the canonical kernel's floor-form
`FloorsKept` reads losses by negation, and this Iff makes the
translation explicit instead of confused. -/
theorem MetricDirection.kept_lossCeiling_neg {S : Type*}
    (obj : S → ℝ) (c : ℝ) (s : S) :
    MetricDirection.kept MetricDirection.LossCeiling obj c s
      ↔ MetricDirection.kept MetricDirection.UtilityFloor
          (fun t => -obj t) (-c) s := by
  simp only [MetricDirection.kept]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- Drop-form descent is a typed LossCeiling improvement. -/
theorem MetricDirection.improves_lossCeiling_intro {S : Type*}
    (obj : S → ℝ) (s s' : S) (δ : ℝ)
    (h : obj s' ≤ obj s - δ) :
    MetricDirection.improves MetricDirection.LossCeiling obj s s'
        δ := h

/-! ## CRAM state carrier -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The CRAM transition-state carrier: the problem, the current
board, an optional latent configuration, the search budget
(natural — one exploration step costs units), the compute budget
(real), the remaining risk-margin budget and the remaining delta
(false-commit probability) budget. -/
structure CRAMState (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : Type*) [Fintype α] [DecidableEq α] where
  /-- The CRAM problem (constraint carrier, C266). -/
  problem : CRAMProblem ι α
  /-- The current board configuration. -/
  board : ι → α
  /-- An optional latent configuration (two-phase protocol). -/
  latent : Option (ι → α)
  /-- Search-step budget (consumed by exploration). -/
  searchBudget : ℕ
  /-- Compute budget (consumed by training and descent). -/
  computeBudget : ℝ
  /-- Remaining risk-margin budget (consumed by descent margins). -/
  riskRem : ℝ
  /-- Remaining delta (false-commit) budget. -/
  deltaRem : ℝ

/-- Componentwise equality of CRAM states iff equality. -/
theorem CRAMState.ext_iff (s s' : CRAMState ι α) :
    s = s' ↔ s.problem = s'.problem ∧ s.board = s'.board
      ∧ s.latent = s'.latent ∧ s.searchBudget = s'.searchBudget
      ∧ s.computeBudget = s'.computeBudget ∧ s.riskRem = s'.riskRem
      ∧ s.deltaRem = s'.deltaRem := by
  constructor
  · intro h
    exact ⟨by rw [h], by rw [h], by rw [h], by rw [h], by rw [h],
      by rw [h], by rw [h]⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    cases s
    cases s'
    simp_all

/-! ## CRAMTrainStep: measured-drop / majorizer premise-form -/

/-- Parameter-training contract on the free-cell
pseudolikelihood objective (C266): a MEASURED drop premise — the
new parameters achieve at most the old objective minus the drop —
plus exact resource laws.  Premise-form: no gradient proof and no
convergence claim is made (the gradient FORMULA exists in
`pseudolikelihood_freeCell_B_gradient`; deriving a certified drop
from it is deliberately NOT attempted here). -/
structure CRAMTrainStep (β : ℝ) (K : ι → ι → α → α → ℝ)
    (P : CRAMProblem ι α) (y : ι → α)
    (oldB newB : ι → α → ℝ) (s s' : CRAMState ι α) where
  /-- Certified (measured) drop of the free-cell PL objective. -/
  drop : ℝ
  /-- The drop is nonnegative (a zero drop — a wasted step — is
  allowed; this contract does not claim progress). -/
  drop_nonneg : 0 ≤ drop
  /-- MEASURED drop premise: the new parameters achieve at most
  the old objective minus the drop. -/
  measured : freeCellPseudolikelihood β newB K P y
    ≤ freeCellPseudolikelihood β oldB K P y - drop
  /-- Training does not move the board. -/
  board_next : s'.board = s.board
  /-- Training does not change the problem. -/
  problem_next : s'.problem = s.problem
  /-- Training does not change the latent. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the training step. -/
  searchCost : ℕ
  /-- Exact search-budget law (additive form: no truncated natural
  subtraction). -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the training step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- Training consumes no risk margin. -/
  risk_next : s'.riskRem = s.riskRem
  /-- Training consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-- Majorizer entry into the measured-drop premise
(majorize-minimize, premise-form): if a surrogate is ANCHORED at
the old parameters (equal to the old objective there) and the new
objective beats the surrogate by `drop`, then the measured drop
holds.  The surrogate properties are premises, not derived. -/
theorem CRAMTrainStep.measured_of_majorizer (β : ℝ)
    (K : ι → ι → α → α → ℝ) (P : CRAMProblem ι α) (y : ι → α)
    (oldB newB : ι → α → ℝ) (maj : ℝ) (drop : ℝ)
    (hAnchor : freeCellPseudolikelihood β oldB K P y = maj)
    (hNew : freeCellPseudolikelihood β newB K P y ≤ maj - drop) :
    freeCellPseudolikelihood β newB K P y
      ≤ freeCellPseudolikelihood β oldB K P y - drop := by
  rw [hAnchor]
  exact hNew

/-! ## CRAMEnergyDescentStep: C261 strict drop + MarginBudget -/

/-- Single-cell energy-descent contract: a strictly positive
local-field margin (the C261 form) certifies a strict energy drop
`E(y^{i←a}) < E(y)`; the certified margin is DEDUCTED from the
risk remainder (MarginBudget accounting), the compute budget is
spent exactly, and the board moves by the single-cell update. -/
structure CRAMEnergyDescentStep (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (s s' : CRAMState ι α) where
  /-- Symmetric coupling premise (load-bearing for the C261
  strict-drop theorem; satisfied by the constructive symmetrizer
  `symmetrizeCoupling` of C266). -/
  hK : ∀ i j a b, K i j a b = K j i b a
  /-- The moved cell. -/
  cell : ι
  /-- The new value at the moved cell. -/
  move : α
  /-- The certified local-field margin. -/
  margin : ℝ
  /-- Strictly positive margin, C261 form:
  `L_i(y_i) − L_i(move) > 0`. -/
  margin_pos : 0 < localField B K s.board cell (s.board cell)
    - localField B K s.board cell move
  /-- The board moves by the single-cell update. -/
  board_next : s'.board = Function.update s.board cell move
  /-- The problem is unchanged. -/
  problem_next : s'.problem = s.problem
  /-- The latent is unchanged. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the descent step. -/
  searchCost : ℕ
  /-- Exact search-budget law. -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the descent step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- MarginBudget accounting: the certified margin is deducted
  from the risk remainder. -/
  risk_next : s'.riskRem = s.riskRem - margin
  /-- Nonnegative risk remainder. -/
  risk_nonneg : 0 ≤ s'.riskRem
  /-- Descent consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-- The C261 strict drop, verbatim: a positive local-field margin
gives `E(s'.board) < E(s.board)` — the existing
`strict_drop_of_positive_margin` applied at the board update. -/
theorem CRAMEnergyDescentStep.strictDrop (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) {s s' : CRAMState ι α}
    (h : CRAMEnergyDescentStep B K s s') :
    pairwiseEnergy B K s'.board < pairwiseEnergy B K s.board := by
  rw [h.board_next]
  exact Hagi.Energy.strict_drop_of_positive_margin B K h.hK
    s.board h.cell h.move h.margin_pos

/-- The strict drop packaged as a typed LossCeiling certificate:
the drop `E(s.board) − E(s'.board)` is positive, exact
(energy_next is an equality), and is a `MetricDirection.improves`
LossCeiling improvement — the polarity is wired by typing, not by
convention. -/
noncomputable def CRAMEnergyDescentStep.toLossCeilingDrop (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) {s s' : CRAMState ι α}
    (h : CRAMEnergyDescentStep B K s s') :
    { drop : ℝ // 0 < drop
        ∧ pairwiseEnergy B K s'.board
            = pairwiseEnergy B K s.board - drop
        ∧ MetricDirection.improves MetricDirection.LossCeiling
            (fun t : CRAMState ι α => pairwiseEnergy B K t.board)
            s s' drop } where
  val := pairwiseEnergy B K s.board - pairwiseEnergy B K s'.board
  property :=
    ⟨by linarith [h.strictDrop], by linarith,
      MetricDirection.improves_lossCeiling_intro _ _ _ _ (by linarith)⟩

/-- The canonical-kernel bridge (pattern:
`HonestTransition.toKernelCertStep`, C254): under EXPLICIT
metric-readout premises — the kernel metrics read the board
energy, the compute budget and the risk remainder — a
`CRAMEnergyDescentStep` IS a canonical `Hagi.Cert.CertStep`:
positive drop, real descent, exact budget/risk consumption laws
with nonnegative remainders, floors kept at the post-state.  The
kernel telescope therefore applies to certified CRAM descent
trajectories. -/
noncomputable def CRAMEnergyDescentStep.toKernelCertStep {TaskId : Type*}
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    {s s' : CRAMState ι α} (h : CRAMEnergyDescentStep B K s s')
    (M : Hagi.Cert.SystemMetrics (CRAMState ι α) TaskId)
    (hobj : M.objective = fun t => pairwiseEnergy B K t.board)
    (hbud : M.budget = fun t => t.computeBudget)
    (hrisk : M.risk = fun t => t.riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStep M obl s s' where
  drop := pairwiseEnergy B K s.board - pairwiseEnergy B K s'.board
  drop_pos := by linarith [h.strictDrop]
  descent := by
    simp only [hobj]
    linarith [h.strictDrop]
  budgetSpend := h.computeCost
  budget_next := by simp only [hbud]; exact h.compute_next
  budget_nonneg := by simp only [hbud]; exact h.compute_nonneg
  riskSpend := h.margin
  risk_next := by simp only [hrisk]; exact h.risk_next
  risk_nonneg := by simp only [hrisk]; exact h.risk_nonneg
  floorsKept := hfloors

/-! ## CRAMExplorationStep: legal move, NO descent claim -/

/-- Legal exploration transition: the new board has POSITIVE
kernel mass under a ROW-STOCHASTIC kernel (the C263
`mixture_rowsum` premise shape — the kernel is a premise, e.g.
the focused heat-bath mixture), every given (clamp) is preserved
exactly, and the search budget is CONSUMED (strictly positive
cost).

NO DESCENT CLAIM: this contract deliberately carries no energy
field and proves no decrease — exploration under a stationary
kernel may RAISE the energy (stationarity is not monotonicity;
see `focused_mixture_stationary`).  Descent is claimed ONLY by
`CRAMEnergyDescentStep`. -/
structure CRAMExplorationStep (s s' : CRAMState ι α) where
  /-- The transition kernel (premise-form data; e.g. a focused
  heat-bath mixture of C263). -/
  kernel : (ι → α) → (ι → α) → ℝ
  /-- Legality: the new board has positive transition mass. -/
  legality : 0 < kernel s.board s'.board
  /-- Row-stochasticity premise (C263 `mixture_rowsum` shape):
  every row of the kernel sums to one. -/
  rowStochastic : ∀ y, ∑ z, kernel y z = 1
  /-- Clamps preserved: every given value is intact. -/
  clampsPreserved : ∀ i a, s.problem.givens i = some a →
    s'.board i = a
  /-- The problem is unchanged. -/
  problem_next : s'.problem = s.problem
  /-- The latent is unchanged. -/
  latent_next : s'.latent = s.latent
  /-- Search budget spent by the exploration step. -/
  searchCost : ℕ
  /-- Exploration CONSUMES search budget (strictly). -/
  searchCost_pos : 0 < searchCost
  /-- Exact search-budget law. -/
  search_next : s'.searchBudget + searchCost = s.searchBudget
  /-- Compute budget spent by the exploration step. -/
  computeCost : ℝ
  /-- Exact compute-budget law. -/
  compute_next : s'.computeBudget = s.computeBudget - computeCost
  /-- Nonnegative compute remainder. -/
  compute_nonneg : 0 ≤ s'.computeBudget
  /-- Exploration consumes no risk margin. -/
  risk_next : s'.riskRem = s.riskRem
  /-- Exploration consumes no delta. -/
  delta_next : s'.deltaRem = s.deltaRem

/-! ## CRAMAcceptedSolution: production certificate -/

/-- The production certificate: a `ValidityCertificate` (givens
preserved + constraints satisfied — C263 `EnergyStopping`)
agreeing with the current board, with an OPTIONAL energy bound.
Validity says NOTHING about energy (E4 separation: the bound is
optional data, and an energy threshold alone certifies nothing). -/
structure CRAMAcceptedSolution (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (C : ι → α → Prop)
    (s : CRAMState ι α) where
  /-- The validity certificate (C263). -/
  cert : ValidityCertificate s.problem.givens C
  /-- The certified configuration IS the current board. -/
  board_agrees : ∀ i, cert.y i = s.board i
  /-- An optional certified energy bound (`none` = no claim). -/
  energyBound : Option ℝ
  /-- The energy bound, when present, holds for the certified
  configuration. -/
  energy_ok : ∀ τ, energyBound = some τ →
    pairwiseEnergy B K cert.y ≤ τ

/-! ## Hold: full state equality on the CRAM carrier -/

/-- A kernel hold on the CRAM carrier fixes the FULL state —
problem, board, latent, both budgets, risk and delta remainders
(Hold = full state equality; the kernel `HoldStep` is reused
as-is, `CRAMState.ext_iff` gives the componentwise reading). -/
theorem _root_.Hagi.Cert.HoldStep.cram_state_components {TaskId : Type*}
    (M : Hagi.Cert.SystemMetrics (CRAMState ι α) TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (s s' : CRAMState ι α)
    (h : Hagi.Cert.HoldStep M obl s s') :
    s'.problem = s.problem ∧ s'.board = s.board
      ∧ s'.latent = s.latent ∧ s'.searchBudget = s.searchBudget
      ∧ s'.computeBudget = s.computeBudget ∧ s'.riskRem = s.riskRem
      ∧ s'.deltaRem = s.deltaRem := by
  have e : s' = s := h.hold
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Hagi.Model.EnergyReasoning
