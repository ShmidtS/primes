/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Math.Info.InfoCore
import Hagi.Energy.PairwiseCategorical
import Hagi.Energy.SingleCellDescent
import Hagi.Model.EnergyReasoning.EnergySearch

set_option linter.style.header false

/-!
# Greedy finite termination and the focused-policy invariance audit

Track P1-remainder (addendum A11): the two honest closures of the
greedy single-cell search story on a FINITE configuration space.

* `greedy_strict_search_terminates` — (A6 MAIN) on a finite space a
  strictly-improving trajectory cannot be long: a list of
  configurations along which the energy `H` strictly decreases at
  every pair has length at most the number of DISTINCT energy values
  `Fintype.card (Set.image H univ)` (the ranking bound: an infinite
  strictly-descending chain would produce arbitrarily long such
  lists). No rate or complexity claim is made.
* `greedy_search_terminal_is_coordinate_minimum` — (A6 MAIN) a
  terminal state of strict-improvement greedy search — one where NO
  single-cell move has a positive C261 local-field margin — is a
  COORDINATE minimum (`IsCoordinateMinimum` reused verbatim).
* `focusedDisagreementWeight` — the PRACTICAL focused selection rule
  of A9-supplement §E4: cell `i` is weighted by its OWN disagreement
  `Σ_a max 0 (L_i(y_i) − L_i(a))` (state-dependent through y_i itself).
* `concrete_focus_policy_violates_invariance` — (A7 MAIN, NEGATIVE
  witness) the disagreement weight CHANGES under a move of its own
  cell (fixture: `3 → 0`), so the INVARIANCE premise
  `w(y^{i←a})_i = w(y)_i` of `focused_mixture_stationary` FAILS for
  this policy: stationarity of the practical focused sampler is NOT
  certified — premise-form only.

## Honest boundaries (A11 'not to adopt')

* COORDINATE MINIMUM ≠ GLOBAL MINIMUM ≠ VALID SOLUTION: the terminal
  state of greedy search is only a coordinate minimum (ties allowed;
  witness in `Hagi.Energy.SingleCellDescent`: coordinate-min state
  that is not global); energy says nothing about constraints (E4
  separation in `Hagi.Model.EnergyReasoning.EnergyStopping`).
* The termination bound is a LIST bound on a finite type; no
  measure-theoretic packaging, no mixing-time, no convergence rate.
* A7 is a NEGATIVE result by design: it closes the audit question of
  A11 ("focused-policy invariance check — likely VIOLATES") with a
  concrete witness; it does NOT define an alternative invariant
  policy (a y-minus-i-measurable rule would satisfy the premise —
  that is policy design, out of scope).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section Termination

variable {γ : Type*} [Fintype γ]

omit [Fintype γ] in
/-- The energy values along a pairwise strictly-improving trajectory
are pairwise DISTINCT (strictly decreasing), so the mapped list is
`Nodup`. -/
private theorem nodup_map_energy_of_pairwise {H : γ → ℝ} {l : List γ}
    (h : l.Pairwise (fun a b => H b < H a)) : (List.map H l).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rcases List.pairwise_cons.1 h with ⟨hhead, hchain⟩
    have hnod : (List.map H xs).Nodup := ih hchain
    have hlt : ∀ v ∈ (List.map H xs), v < H x := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      exact hhead b hb
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun hmem => absurd (hlt (H x) hmem) (lt_irrefl (H x)), hnod⟩

/-- (A6 MAIN) Greedy finite termination: on a FINITE configuration
space, a strictly-improving trajectory (a list of configurations
whose energy `H` strictly decreases along every pair — the
transitive closure of the per-step strict drop) has length at most
the number of DISTINCT energy values `Fintype.card (Set.image H
univ)`. An infinite strictly-descending chain would produce
arbitrarily long such lists, so none exists. The bound is the honest
ranking statement; NO rate, complexity or mixing-time claim is made,
and the terminal state claim is `greedy_search_terminal_is_
coordinate_minimum` below. -/
theorem greedy_strict_search_terminates (H : γ → ℝ) (l : List γ)
    (h : l.Pairwise (fun a b => H b < H a)) :
    l.length ≤ Fintype.card (Set.image H (Set.univ : Set γ)) := by
  have himage : ∀ v ∈ (List.map H l), v ∈ Set.image H (Set.univ : Set γ) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ⟨x, Set.mem_univ _, rfl⟩
  have hnodup : (List.map H l).Nodup := nodup_map_energy_of_pairwise h
  let m : List {x // x ∈ Set.image H (Set.univ : Set γ)} :=
    (List.map H l).attach.map (fun p => ⟨p.1, himage p.1 p.2⟩)
  have hml : m.length = l.length := by simp [m, List.length_attach]
  have hmn : m.Nodup :=
    List.Nodup.map
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      (List.nodup_attach.mpr hnodup)
  calc l.length = m.length := hml.symm
    _ ≤ Fintype.card {x // x ∈ Set.image H (Set.univ : Set γ)} :=
        hmn.length_le_card

end Termination

section Terminal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- (A6 MAIN) The terminal state of strict-improvement greedy search
is a COORDINATE minimum: if at `y` NO single-cell move has a strictly
positive C261 local-field margin (`0 < L_i(y_i) − L_i(a)` fails for
every cell `i` and value `a` — strict improvement is unavailable),
then `y` is an `IsCoordinateMinimum` (no single-cell move decreases
the energy; ties allowed). HONEST SCOPE: a coordinate minimum is NOT
the global minimum (witness in `Hagi.Energy.SingleCellDescent`) and
NOT a validity certificate (E4 separation in
`Hagi.Model.EnergyReasoning.EnergyStopping`). -/
theorem greedy_search_terminal_is_coordinate_minimum (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α)
    (h : ∀ (i : ι) (a : α),
      ¬ 0 < localField B K y i (y i) - localField B K y i a) :
    IsCoordinateMinimum B K y := by
  intro i a
  have hd := single_cell_move_energy_delta_symm B K hK y i a
  have hle : localField B K y i (y i) ≤ localField B K y i a := by
    linarith [h i a]
  linarith

end Terminal

section FocusAudit

/-! ## A7: the practical focused selection rule vs the C263
INVARIANCE premise. The rule weights cell `i` by its OWN
disagreement — state-dependent through y_i ITSELF, which is
exactly what the invariance premise forbids. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The PRACTICAL focused selection weight of A9-supplement §E4:
cell `i` is weighted by its own disagreement
`Σ_a max 0 (L_i(y_i) − L_i(a))` with `L` the C261 `localField`.
State-dependent through y_i itself (and through the other cells via the
field). This is the rule the CRAM focused sampler actually uses;
against the C263 `focused_mixture_stationary` premises it satisfies
SUPPORT structurally (heat-bath kernels) but INVARIANCE only as an
UNVERIFIED premise — see the witness below. -/
noncomputable def focusedDisagreementWeight (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) (i : ι) : ℝ :=
  ∑ a, max 0 (localField B K y i (y i) - localField B K y i a)

/-- Local-field anchor on the Fin 2 × Bool fixture (C260 `Bex`/
`Kex`/`xtt`): at cell `0`, whenever `y 1 = true`, the field is
`L_0(c) = if c then 3 else 0` — it depends ONLY on `y 1`, never on
`y 0`. -/
private theorem localField_cell0_fixture (y : Fin 2 → Bool)
    (hy1 : y 1 = true) (c : Bool) :
    localField Bex Kex y 0 c = if c then (3 : ℝ) else 0 := by
  simp only [localField, Bex, Kex]
  fin_cases c <;> norm_num [hy1]

/-- Numeric anchor: at `xtt = (t, t)` the disagreement weight of
cell `0` is `max 0 (3 − 3) + max 0 (3 − 0) = 3`. -/
example : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
  have hL : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  simp only [focusedDisagreementWeight, hL, xtt]
  norm_num

/-- (A7 MAIN, NEGATIVE WITNESS) The practical focused selection rule
VIOLATES the INVARIANCE premise of `focused_mixture_stationary`
(C263): after the greedy move of cell `0` from `t` to `f` (its local
field minimizer on the fixture), the weight of cell `0` DROPS from
`3` to `0` — `w(y^{0←f})_0 ≠ w(y)_0`. The weight depends on y_0
itself through `L_i(y_i)`, which is exactly what the premise
forbids. Consequence, stated honestly: the C263 stationarity
theorem applies to the practical focused sampler ONLY in
premise-form — the INVARIANCE premise is FALSE for this policy, so
NO stationarity claim for the practical focused sampler is certified
here. -/
theorem concrete_focus_policy_violates_invariance :
    focusedDisagreementWeight Bex Kex (Function.update xtt 0 false) 0
      ≠ focusedDisagreementWeight Bex Kex xtt 0 := by
  have hy0 : Function.update xtt 0 false 0 = false :=
    Function.update_self 0 false xtt
  have hL : ∀ c, localField Bex Kex (Function.update xtt 0 false) 0 c
      = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  have hw0 : focusedDisagreementWeight Bex Kex
      (Function.update xtt 0 false) 0 = 0 := by
    simp only [focusedDisagreementWeight, hL, hy0]
    norm_num
  have hw1 : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
    have hL' : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
      intro c
      simp only [localField, Bex, Kex]
      fin_cases c <;> norm_num [xtt]
    simp only [focusedDisagreementWeight, hL', xtt]
    norm_num
  rw [hw0, hw1]
  norm_num

end FocusAudit

section Fixture
/-! ## Fin 2 × Bool fixture: the termination bound closes on a
concrete two-state trajectory (C260 carriers). -/

/-- Bound fixture: the two-state strictly-decreasing trajectory
`[true, false]` under `H = fun b => if b then 1 else 0` has length
`2` at most the cardinality of the two-element energy image. -/
example :
    ([true, false] : List Bool).length ≤
    Fintype.card (Set.image (fun b => if b then (1 : ℝ) else 0)
      (Set.univ : Set Bool)) := by
  refine greedy_strict_search_terminates _ _ ?_
  simp [List.pairwise_cons]

end Fixture

end Hagi.Model.EnergyReasoning
