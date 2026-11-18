/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.SelfDevelopment
import Hagi.Model.StageSemantics
import Mathlib.Tactic
import Hagi.Model.SoftmaxStep
import Hagi.Unified.LogitCert
import Hagi.State.TrainState
import Mathlib.Data.List.MinMax
set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Cycle 70 — finite constrained Pareto execution controller

A well-specified FINITE policy over an explicitly supplied family of
candidate actions: maximize an objective subject to a model-safety
predicate and separate memory / operation-count budget caps, using the
ACTUAL successor function `step : A → S → S` of the mathematical model
(no synthesized "desired effects" records are executed).

Design (plan `cycle70-controller.md`, alternative 3):

* `feasible` reuses `Hagi.Growth.safeCandidates` on
  `safe a ∧ memory a ≤ M ∧ operations a ≤ C`.
* `score` is a nested Mathlib `Prod.Lex` maximum
  `(value (step a s), −memory, −operations)`: quality has lexicographic
  priority, and smaller resources win quality ties WITHOUT arbitrary
  scalarization weights.
* `selection` is a `Classical.choose` witness of `Finset.exists_max_image`
  over the nonempty feasible set; `selectedNext` is its actual successor.

Exact domain limits:

* Non-domination (`selection_pareto`) holds WITHIN the finite supplied
  feasible family only — not over all possible architectures, and not as
  automatic optimality on actual tasks.
* `value`, `memory`, `operations` are declared MODEL objectives and
  model units supplied with the problem, not physical measurements
  (no hardware/IEEE/total-size/universal-training claims).
* The selector uses `Classical.choice` and `ℝ`, so it is exact finite
  mathematical selection; no native executable optimizer is certified.
-/

namespace Hagi.Unified.ParetoExecution

open Prod.Lex

variable {A S : Type*}

/-- A finite feasible controller problem over an explicit candidate
family `A` and state space `S`. All fields are model-level data
declared with the problem (objectives/units), not measurements. -/
structure ControllerProblem (A S : Type*) where
  /-- Model objective to maximize (higher is better). -/
  value : S → ℝ
  /-- Actual successor function of the model: action, state, next state. -/
  step : A → S → S
  /-- Memory cost of an action, in model units. -/
  memory : A → ℕ
  /-- Operation-count cost of an action, in model units. -/
  operations : A → ℕ
  /-- Model-safety predicate (conditional on its model, not physical
  safety). -/
  safe : A → Prop

section Finite

variable {A : Type} {S : Type*} [Fintype A] {s : S}

@[reducible]
private def feasPred (p : ControllerProblem A S) (M C : ℕ) : A → Prop :=
  fun a => p.safe a ∧ p.memory a ≤ M ∧ p.operations a ≤ C

instance {p : ControllerProblem A S} [DecidablePred p.safe] (M C : ℕ) :
    DecidablePred (feasPred p M C) :=
  fun _ => inferInstance

/-- The finite feasible set: `Hagi.Growth.safeCandidates` on safety plus
memory/operation caps. -/
def feasible (p : ControllerProblem A S) (memoryLimit operationLimit : ℕ)
    [DecidablePred p.safe] : Finset A :=
  Hagi.Growth.safeCandidates (feasPred p memoryLimit operationLimit)

@[simp] theorem mem_feasible {p : ControllerProblem A S} [DecidablePred p.safe]
    {M C : ℕ} {a : A} :
    a ∈ feasible p M C ↔ p.safe a ∧ p.memory a ≤ M ∧ p.operations a ≤ C := by
  simp [feasible, feasPred, Hagi.Growth.safeCandidates]

/-- Lexicographic score: quality first, then SMALLER memory, then
smaller operations. Nonnegative integer resource costs are negated so
that `≤` in the max-lex order prefers cheaper actions, without any
arbitrary scalar weights. -/
def score (p : ControllerProblem A S) (s : S) (a : A) : ℝ ×ₗ (ℤ ×ₗ ℤ) :=
  toLex (p.value (p.step a s), toLex (-(p.memory a : ℤ), -(p.operations a : ℤ)))

omit [Fintype A] in
/-- A maximal-`score` action in an explicit nonempty finite set `kept`.
Unlike `selection`, this raw choice needs neither `Fintype A` nor a safety instance. -/
noncomputable def selectionIn
    (p : ControllerProblem A S) (s : S)
    (kept : Finset A) (stay : A) (h_stay : stay ∈ kept) : A :=
  Classical.choose
    (Finset.exists_max_image kept (score p s) ⟨stay, h_stay⟩)

/-- Selected action: a `Classical.choose` max-`score` witness over the
nonempty feasible set (exact finite selection via
`Finset.exists_max_image`; noncomputable because `ℝ` scores are not
decidable in general). -/
noncomputable def selection (p : ControllerProblem A S) [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) : A :=
  selectionIn p s (feasible p M C) stay h_stay

/-- Master specification of the selection: feasibility of the selected
action plus the feasible-set lex maximum property. -/
theorem selection_spec (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    selection p s M C stay h_stay ∈ feasible p M C
      ∧ ∀ a ∈ feasible p M C, score p s a ≤ score p s (selection p s M C stay h_stay) :=
  by
  have h := Classical.choose_spec
    (Finset.exists_max_image (feasible p M C) (score p s) ⟨stay, h_stay⟩)
  exact h

/-- The selected action is feasible (safe and within both resource
caps). -/
theorem selection_admissible (p : ControllerProblem A S) [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) :
    selection p s M C stay h_stay ∈ feasible p M C :=
  (selection_spec p s M C stay h_stay).1

/-- The selected action maximizes the lex score over the feasible set. -/
theorem selection_optimal (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    ∀ a ∈ feasible p M C, score p s a ≤ score p s (selection p s M C stay h_stay) :=
  (selection_spec p s M C stay h_stay).2

/-- Restricting feasible actions to a score-covering subset preserves the
selected score: both selections attain the same lexicographic maximum. -/
theorem selection_score_eq_selectionIn
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ)
    (kept : Finset A) (stay : A)
    (h_stay : stay ∈ kept)
    (hsub : kept ⊆ feasible p M C)
    (hcover : ∀ a ∈ feasible p M C,
      ∃ b ∈ kept, score p s a ≤ score p s b) :
    score p s (selection p s M C stay (hsub h_stay)) =
      score p s (selectionIn p s kept stay h_stay) := by
  have hkept :
      selectionIn p s kept stay h_stay ∈ kept ∧
        ∀ a ∈ kept,
          score p s a ≤ score p s (selectionIn p s kept stay h_stay) :=
    Classical.choose_spec
      (Finset.exists_max_image kept (score p s) ⟨stay, h_stay⟩)
  apply le_antisymm
  · obtain ⟨b, hb_kept, hb_score⟩ :=
      hcover (selection p s M C stay (hsub h_stay))
        (selection_admissible p s M C stay (hsub h_stay))
    exact hb_score.trans (hkept.2 b hb_kept)
  · exact selection_optimal p s M C stay (hsub h_stay)
      (selectionIn p s kept stay h_stay)
      (hsub hkept.1)

/-- Feasible actions weakly dominating some action in kept. -/
noncomputable def scoreDominatingIn
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (kept : Finset A) : Finset A :=
  by
    classical
    exact (feasible p M C).filter
      (fun a => ∃ b ∈ kept, score p s b ≤ score p s a)

/-- The bank-dominating envelope preserves the exact selected score
without a separate coverage hypothesis. -/
theorem selection_score_eq_selectionIn_scoreDominatingIn
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ)
    (kept : Finset A) (stay : A)
    (h_stay : stay ∈ kept)
    (hsub : kept ⊆ feasible p M C) :
    score p s (selection p s M C stay (hsub h_stay)) =
      score p s (selectionIn p s (scoreDominatingIn p s M C kept) stay
        (by
          exact Finset.mem_filter.mpr
            ⟨hsub h_stay, stay, h_stay, le_rfl⟩)) := by
  classical
  let h_new_stay : stay ∈ scoreDominatingIn p s M C kept := by
    exact Finset.mem_filter.mpr ⟨hsub h_stay, stay, h_stay, le_rfl⟩
  have hsub_new : scoreDominatingIn p s M C kept ⊆ feasible p M C := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  apply selection_score_eq_selectionIn p s M C
    (scoreDominatingIn p s M C kept) stay h_new_stay hsub_new
  intro a ha
  let m := selection p s M C stay (hsub h_stay)
  have hm_feasible : m ∈ feasible p M C := by
    exact selection_admissible p s M C stay (hsub h_stay)
  have hm_new : m ∈ scoreDominatingIn p s M C kept := by
    apply Finset.mem_filter.mpr
    refine ⟨hm_feasible, stay, h_stay, ?_⟩
    exact selection_optimal p s M C stay (hsub h_stay) stay (hsub h_stay)
  exact ⟨m, hm_new, selection_optimal p s M C stay (hsub h_stay) a ha⟩

/-- With two feasible actions, a strict objective increase from action `0`
to action `1` forces the lexicographic selection to choose action `1`. -/
theorem selection_eq_one_of_value_lt {S : Type*}
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (w : S) (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (h1 : (1 : Fin 2) ∈ feasible p M C)
    (hvalue : p.value (p.step 0 w) < p.value (p.step 1 w)) :
    selection p w M C 0 h0 = 1 := by
  have hval : (selection p w M C 0 h0).val = 0
      ∨ (selection p w M C 0 h0).val = 1 := by omega
  rcases hval with h | h
  · exfalso
    have hs := selection_optimal p w M C 0 h0 1 h1
    have hsel : selection p w M C 0 h0 = 0 := Fin.ext h
    rw [hsel] at hs
    have hfst : p.value (p.step 1 w) ≤ p.value (p.step 0 w) :=
      Prod.Lex.monotone_fst _ _ hs
    linarith
  · exact Fin.ext h

/-- The actual successor state produced by the selected action. -/
noncomputable def selectedNext (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : S :=
  p.step (selection p s M C stay h_stay) s

/-- Quality optimality within the feasible family: no feasible action's
actual next state has higher objective than the selected next state. -/
theorem selection_quality_optimal (p : ControllerProblem A S)
    [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) :
    ∀ a ∈ feasible p M C,
      p.value (p.step a s) ≤ p.value (selectedNext p s M C stay h_stay) := by
  intro a ha
  exact Prod.Lex.monotone_fst _ _ (selection_optimal p s M C stay h_stay a ha)

/-- If the baseline keeps the state fixed, its quality is met by the
selection. -/
theorem selection_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (s : S) (M C : ℕ)
    (stay : A) (h_stay : stay ∈ feasible p M C) (hid : p.step stay s = s) :
    p.value s ≤ p.value (selectedNext p s M C stay h_stay) := by
  have h := selection_quality_optimal p s M C stay h_stay stay h_stay
  rwa [hid] at h

/-- Resource caps hold for the selected action (from feasibility). -/
theorem selection_memory_le (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : p.memory (selection p s M C stay h_stay) ≤ M :=
  (mem_feasible.mp (selection_admissible p s M C stay h_stay)).2.1

/-- Resource caps hold for the selected action (from feasibility). -/
theorem selection_operations_le (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : p.operations (selection p s M C stay h_stay) ≤ C :=
  (mem_feasible.mp (selection_admissible p s M C stay h_stay)).2.2

/-- **Pareto non-domination within the exact finite feasible set.**
If a feasible competitor matches the selected quality while using no
more memory and no more operations, then all three coordinates are
EQUAL: no feasible action strictly dominates the selection. This is
not a claim about all possible architectures, not a scalarization,
and not automatic optimality on actual tasks. -/
theorem selection_pareto (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) {a : A} (ha : a ∈ feasible p M C)
    (hq : p.value (selectedNext p s M C stay h_stay) ≤ p.value (p.step a s))
    (hm : p.memory a ≤ p.memory (selection p s M C stay h_stay))
    (ho : p.operations a ≤ p.operations (selection p s M C stay h_stay)) :
    p.value (p.step a s) = p.value (selectedNext p s M C stay h_stay)
      ∧ p.memory a = p.memory (selection p s M C stay h_stay)
      ∧ p.operations a = p.operations (selection p s M C stay h_stay) := by
  have hsa : score p s a ≤ score p s (selection p s M C stay h_stay) :=
    selection_optimal p s M C stay h_stay a ha
  have hle1 : p.value (p.step a s) ≤
      p.value (p.step (selection p s M C stay h_stay) s) :=
    Prod.Lex.monotone_fst _ _ hsa
  have hveq : p.value (p.step a s) =
      p.value (p.step (selection p s M C stay h_stay) s) :=
    le_antisymm hle1 hq
  have hlex : p.value (p.step a s) <
      p.value (p.step (selection p s M C stay h_stay) s)
      ∨ (p.value (p.step a s) =
          p.value (p.step (selection p s M C stay h_stay) s)
          ∧ toLex (-(p.memory a : ℤ), -(p.operations a : ℤ))
              ≤ toLex (-(p.memory (selection p s M C stay h_stay) : ℤ),
                  -(p.operations (selection p s M C stay h_stay) : ℤ))) :=
    Prod.Lex.toLex_le_toLex.mp hsa
  rcases hlex with hlt | hval
  · linarith
  · obtain ⟨hval, hinner⟩ := hval
    rcases Prod.Lex.toLex_le_toLex.mp hinner with hlt2 | ⟨heq2, hle2⟩
    · exact absurd hlt2 (by omega)
    · have hmeq : p.memory a = p.memory (selection p s M C stay h_stay) := by
        have hz : (p.memory a : ℤ) = p.memory (selection p s M C stay h_stay) := by
          linarith
        omega
      have hoeq : p.operations a = p.operations (selection p s M C stay h_stay) := by
        have hz : (p.operations a : ℤ) = p.operations (selection p s M C stay h_stay) := by
          have h2 : (p.operations (selection p s M C stay h_stay) : ℤ) ≤ p.operations a := by
            linarith
          have h1 : (p.operations a : ℤ) ≤ p.operations (selection p s M C stay h_stay) := by
            exact_mod_cast ho
          linarith
        omega
      exact ⟨hveq, hmeq, hoeq⟩

/-- **Identity fallback.** If the baseline `stay` is the only feasible
action, the selection is exactly `stay`. -/
theorem selection_fallback (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (honly : ∀ a, a ≠ stay → a ∉ feasible p M C) :
    selection p s M C stay h_stay = stay := by
  by_contra hne
  exact honly _ hne (selection_admissible p s M C stay h_stay)

/-- On fallback with a state-fixing baseline, the executed successor is
exactly the current state: no alternate effect is executed. -/
theorem next_fallback (p : ControllerProblem A S) [DecidablePred p.safe]
    (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (honly : ∀ a, a ≠ stay → a ∉ feasible p M C) (hid : p.step stay s = s) :
    selectedNext p s M C stay h_stay = s := by
  rw [selectedNext, selection_fallback p s M C stay h_stay honly, hid]

end Finite

section Robust

/-! ### Cycle 71 — bounded-estimation robust selection

The frontier beyond exact selection: the controller may only access an
`estimate` of the model objective at successor states, with a uniform
error bound `eps ≥ 0` over the actual successors of the candidate
family. Running the EXACT finite selector on the estimate-updated
problem yields a successor that is `2*eps`-approximately optimal in
the TRUE objective against every feasible competitor — and this is the
best one can claim: within the bound, the estimate-selected successor
may be ACTUALLY worse than the baseline unless further conditions
(`p.safe`, positive gaps) hold. Resource caps stay exact because
feasibility uses the original `memory`/`operations` fields, which the
estimate update does not touch.
-/

variable {A : Type} {S : Type*} [Fintype A]

/-- Record update replacing ONLY the model objective `value` by an
`estimate : S → ℝ`. `step`, `memory`, `operations` and `safe` are
preserved definitionally. Marked reducible so instance search and
`rfl` see the unchanged fields. -/
@[reducible] def withEstimatedValue (p : ControllerProblem A S)
    (estimate : S → ℝ) : ControllerProblem A S := { p with value := estimate }

omit [Fintype A] in
@[simp] theorem withEstimatedValue_step (p : ControllerProblem A S)
    (estimate : S → ℝ) (a : A) (s : S) :
    (withEstimatedValue p estimate).step a s = p.step a s := rfl

/-- Feasibility is untouched by the estimate update: the feasible set
depends only on `safe`/`memory`/`operations`, so budget caps stay
exact under bounded-estimation quality. -/
theorem mem_feasible_withEstimatedValue (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) {M C : ℕ} {a : A} :
    a ∈ feasible (withEstimatedValue p estimate) M C ↔ a ∈ feasible p M C := by
  simp [mem_feasible]

/-- The robust successor: run the exact finite selector on the
estimate-updated problem. Its output is an ACTUAL successor of the
ORIGINAL `p.step` executed by a feasible action of the ORIGINAL
problem (see `robustNext_eq`); nothing in quality estimation changes
resource caps or model safety. -/
noncomputable def robustNext (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) : S :=
  selectedNext (withEstimatedValue p estimate) s M C stay
    ((mem_feasible_withEstimatedValue p estimate).mpr h_stay)

/-- The robust successor is the actual `p.step` successor of a
feasible action of the ORIGINAL problem: exact safety and resource
caps, only the objective was estimated. -/
theorem robustNext_eq (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    ∃ a ∈ feasible p M C, robustNext p estimate s M C stay h_stay = p.step a s := by
  have h' : stay ∈ feasible (withEstimatedValue p estimate) M C :=
    (mem_feasible_withEstimatedValue p estimate).mpr h_stay
  exact ⟨selection (withEstimatedValue p estimate) s M C stay h',
    (mem_feasible_withEstimatedValue p estimate).mp
      (selection_admissible (withEstimatedValue p estimate) s M C stay h'), rfl⟩

/-- **Approximate quality lower bound.** If `estimate` uniformly
approximates the true objective on actual successors within `eps`,
then for EVERY feasible action of the original problem the robust
successor's true quality is at most `2*eps` below that action's:
`q_a ≤ est_a + eps ≤ est_sel + eps ≤ q_sel + 2*eps`. No positive-gap
threshold is required for this approximate guarantee. -/
theorem robust_quality_lower (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) (eps : ℝ) (_heps : 0 ≤ eps)
    (herr : ∀ a : A, |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    ∀ a ∈ feasible p M C,
      p.value (p.step a s) - 2 * eps
        ≤ p.value (robustNext p estimate s M C stay h_stay) := by
  intro a ha
  have h' : stay ∈ feasible (withEstimatedValue p estimate) M C :=
    (mem_feasible_withEstimatedValue p estimate).mpr h_stay
  have hsel := selection_quality_optimal (withEstimatedValue p estimate) s M C stay h' a
    ((mem_feasible_withEstimatedValue p estimate).mpr ha)
  have ha1 := (abs_le.mp (herr a)).1
  have ha2 := (abs_le.mp (herr a)).2
  set sel := selection (withEstimatedValue p estimate) s M C stay h' with hseldef
  have hs1 := (abs_le.mp (herr sel)).1
  have hs2 := (abs_le.mp (herr sel)).2
  have h3 : estimate (p.step a s) ≤ estimate (p.step sel s) := hsel
  change p.value (p.step a s) - 2 * eps ≤ p.value (p.step sel s)
  linarith

/-- A retained-full-proxy-score family keeps the bounded true-quality guarantee. -/
theorem robust_quality_lower_selectionIn
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ)
    (kept : Finset A) (stay : A) (h_stay : stay ∈ kept)
    (hsub : kept ⊆ feasible p M C)
    (hcover : ∀ a ∈ feasible (withEstimatedValue p estimate) M C,
      ∃ b ∈ kept,
        score (withEstimatedValue p estimate) s a ≤
          score (withEstimatedValue p estimate) s b)
    (eps : ℝ) (_heps : 0 ≤ eps)
    (herr : ∀ a : A,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    ∀ a ∈ feasible p M C,
      p.value (p.step a s) - 2 * eps ≤
        p.value (p.step
          (selectionIn (withEstimatedValue p estimate)
            s kept stay h_stay) s) := by
  have hsube : kept ⊆ feasible (withEstimatedValue p estimate) M C :=
    fun _ ha => (mem_feasible_withEstimatedValue p estimate).mpr (hsub ha)
  have hscore := selection_score_eq_selectionIn
    (withEstimatedValue p estimate) s M C kept stay h_stay hsube hcover
  have hfst_le := Prod.Lex.monotone_fst _ _ hscore.le
  have hfst_ge := Prod.Lex.monotone_fst _ _ hscore.ge
  change estimate (p.step (selection (withEstimatedValue p estimate)
      s M C stay (hsube h_stay)) s) ≤
    estimate (p.step (selectionIn (withEstimatedValue p estimate)
      s kept stay h_stay) s) at hfst_le
  change estimate (p.step (selectionIn (withEstimatedValue p estimate)
      s kept stay h_stay) s) ≤
    estimate (p.step (selection (withEstimatedValue p estimate)
      s M C stay (hsube h_stay)) s) at hfst_ge
  have hest := le_antisymm hfst_le hfst_ge
  intro a ha
  have hopt := selection_quality_optimal (withEstimatedValue p estimate)
    s M C stay (hsube h_stay) a
    ((mem_feasible_withEstimatedValue p estimate).mpr ha)
  change estimate (p.step a s) ≤
    estimate (p.step (selection (withEstimatedValue p estimate)
      s M C stay (hsube h_stay)) s) at hopt
  have ha2 := (abs_le.mp (herr a)).2
  have hn1 := (abs_le.mp (herr
    (selectionIn (withEstimatedValue p estimate) s kept stay h_stay))).1
  linarith only [ha2, hopt, hest, hn1]

/-- The bank-dominating envelope keeps the bounded true-quality guarantee
without a separate coverage premise. The envelope's own maximizer covers
the full feasible family by the exact global-versus-restricted score equality. -/
theorem robust_quality_lower_selectionIn_scoreDominatingIn
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ)
    (kept : Finset A) (stay : A) (h_stay : stay ∈ kept)
    (hsub : kept ⊆ feasible p M C)
    (eps : ℝ) (_heps : 0 ≤ eps)
    (herr : ∀ a : A,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    ∀ a ∈ feasible p M C,
      p.value (p.step a s) - 2 * eps ≤
        p.value (p.step
          (selectionIn (withEstimatedValue p estimate)
            s (scoreDominatingIn (withEstimatedValue p estimate)
              s M C kept) stay (by
                exact Finset.mem_filter.mpr
                  ⟨(mem_feasible_withEstimatedValue p estimate).mpr
                    (hsub h_stay), stay, h_stay, le_rfl⟩)) s) := by
  classical
  let pE := withEstimatedValue p estimate
  let E := scoreDominatingIn pE s M C kept
  have hsubE : kept ⊆ feasible pE M C := by
    intro a ha
    exact (mem_feasible_withEstimatedValue p estimate).mpr (hsub ha)
  have hStayE : stay ∈ E := by
    exact Finset.mem_filter.mpr ⟨hsubE h_stay, stay, h_stay, le_rfl⟩
  have hEnvelopeSub : E ⊆ feasible pE M C := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hscore := selection_score_eq_selectionIn_scoreDominatingIn
    pE s M C kept stay h_stay hsubE
  have hrestricted :
      selectionIn pE s E stay hStayE ∈ E :=
    (Classical.choose_spec
      (Finset.exists_max_image E (score pE s) ⟨stay, hStayE⟩)).1
  have hcover : ∀ a ∈ feasible pE M C,
      ∃ b ∈ E, score pE s a ≤ score pE s b := by
    intro a ha
    refine ⟨selectionIn pE s E stay hStayE, hrestricted, ?_⟩
    exact (selection_optimal pE s M C stay (hsubE h_stay) a ha).trans_eq hscore
  have hsubActual : E ⊆ feasible p M C := by
    intro a ha
    exact (mem_feasible_withEstimatedValue p estimate).mp (hEnvelopeSub ha)
  exact robust_quality_lower_selectionIn p estimate s M C E stay hStayE
    hsubActual hcover eps _heps herr

/-- **Elimination of the contradictory gap.** Under the same bounded
error, no feasible candidate's ACTUAL quality can strictly exceed the
robust successor's by more than `2*eps`. This is direct elimination
via `robust_quality_lower`, not a true exact-argmax theorem. -/
theorem robust_quality_gap (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C) (eps : ℝ) (_heps : 0 ≤ eps)
    (herr : ∀ a : A, |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    ∀ a ∈ feasible p M C,
      ¬ (p.value (robustNext p estimate s M C stay h_stay) + 2 * eps
          < p.value (p.step a s)) := by
  intro a ha hcontra
  have h := robust_quality_lower p estimate s M C stay h_stay eps _heps herr a ha
  linarith

/-- **Fallback is corruption-proof.** If the baseline `stay` is the
only feasible action of the ORIGINAL problem and fixes the state, the
robust successor is exactly `s` — even for arbitrarily corrupted
estimates, because all alternatives are infeasible. Note this does
NOT promise actual quality improvement in general: with a corrupted
estimate that admits an upgrade, baseline non-decrease can fail within
the `2*eps` bound unless additional safety/gap conditions hold. -/
theorem robustNext_fallback (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (s : S) (M C : ℕ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (honly : ∀ a, a ≠ stay → a ∉ feasible p M C) (hid : p.step stay s = s) :
    robustNext p estimate s M C stay h_stay = s := by
  have h' : stay ∈ feasible (withEstimatedValue p estimate) M C :=
    (mem_feasible_withEstimatedValue p estimate).mpr h_stay
  have honly' : ∀ a, a ≠ stay → a ∉ feasible (withEstimatedValue p estimate) M C :=
    fun a ha hmem => honly a ha ((mem_feasible_withEstimatedValue p estimate).mp hmem)
  exact next_fallback (withEstimatedValue p estimate) s M C stay h' honly' hid

end Robust

section Stage

variable {A : Type*} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Model adapter from fresh stage inputs to actual successors**:
each action's successor is the existing `Hagi.Model.advance` applied to
a per-action fresh `StageInput`. This maps measured per-cycle inputs to
the actual successor function of the model — it is a mathematical
adapter, not hardware execution. -/
def stageFamily (inputs : A → Hagi.Model.StageInput X) :
    A → Hagi.System.GrowthState X → Hagi.System.GrowthState X :=
  fun a S => Hagi.Model.advance S (inputs a)

/-- The adapter's capability ledger comes verbatim from the cycle input:
fresh per-cycle gains, not a copied effects record. -/
theorem stageFamily_capability (inputs : A → Hagi.Model.StageInput X) (a : A)
    (S : Hagi.System.GrowthState X) :
    (stageFamily inputs a S).capability = S.capability + (inputs a).eff.growGain :=
  Hagi.Model.advance_capability S (inputs a)

end Stage

end Hagi.Unified.ParetoExecution
set_option linter.style.header false

/-!
# Guarded robust selection with baseline non-regression

This additive controller uses the existing robust finite selector only when
some feasible action improves the stay successor's estimated quality by at
least `2 * eps`. Otherwise, it executes the stay successor directly.

Under a pointwise absolute-error bound on all currently feasible successors,
the selected successor's true model quality is no lower than that of the stay
successor. This is a deterministic conditional statement, not a probability,
empirical-performance, or physical-safety claim.
-/

namespace Hagi.Unified.GuardedRobustSelection

open Hagi.Unified.ParetoExecution

variable {A : Type} {S : Type*} [Fintype A]

/-- Some original feasible action has estimated successor quality at least
`2 * eps` above the stay successor's estimated quality. -/
def estimatedUpgrade (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (eps : ℝ) (s : S) (M C : ℕ) (stay : A) : Prop :=
  ∃ a ∈ feasible p M C,
    estimate (p.step stay s) + 2 * eps ≤ estimate (p.step a s)

/-- Use the existing robust successor exactly when `estimatedUpgrade` holds;
otherwise return the actual stay successor. -/
noncomputable def guardedRobustNext (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) : S := by
  classical
  exact if estimatedUpgrade p estimate eps s M C stay then
    robustNext p estimate s M C stay h0
  else
    p.step stay s

/-- Without an estimated upgrade, the wrapper executes the stay successor. -/
theorem guardedRobustNext_of_no_upgrade (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (h : ¬ estimatedUpgrade p estimate eps s M C stay) :
    guardedRobustNext p estimate eps s M C stay h0 = p.step stay s := by
  unfold guardedRobustNext
  exact if_neg h

/-- The guarded successor is the actual successor of an original feasible
action, whether the robust branch or the stay branch is taken. -/
theorem guardedRobustNext_exists (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) :
    ∃ a ∈ feasible p M C,
      guardedRobustNext p estimate eps s M C stay h0 = p.step a s := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · obtain ⟨a, ha, hnext⟩ := robustNext_eq p estimate s M C stay h0
    refine ⟨a, ha, ?_⟩
    unfold guardedRobustNext
    rw [if_pos hup]
    exact hnext
  · exact ⟨stay, h0, guardedRobustNext_of_no_upgrade
      p estimate eps s M C stay h0 hup⟩

/-- Bounded pointwise estimation error and the `2 * eps` upgrade guard imply
true-quality non-regression relative to the actual stay successor. -/
theorem guardedRobustNext_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    p.value (p.step stay s) ≤
      p.value (guardedRobustNext p estimate eps s M C stay h0) := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · have hguard : guardedRobustNext p estimate eps s M C stay h0 =
        robustNext p estimate s M C stay h0 := by
      unfold guardedRobustNext
      rw [if_pos hup]
    obtain ⟨a, ha, hmargin⟩ := hup
    obtain ⟨b, hb, hnext⟩ :=
      guardedRobustNext_exists p estimate eps s M C stay h0
    have hm0 := (mem_feasible_withEstimatedValue p estimate).mpr h0
    have hchoice := selection_quality_optimal (withEstimatedValue p estimate)
      s M C stay hm0 a ((mem_feasible_withEstimatedValue p estimate).mpr ha)
    have hrob : robustNext p estimate s M C stay h0 = p.step b s :=
      hguard.symm.trans hnext
    change estimate (p.step a s) ≤
      estimate (robustNext p estimate s M C stay h0) at hchoice
    rw [hrob] at hchoice
    have hbase := (abs_le.mp (herr stay h0)).2
    have hb_error := (abs_le.mp (herr b hb)).1
    rw [hnext]
    linarith
  · rw [guardedRobustNext_of_no_upgrade p estimate eps s M C stay h0 hup]

end Hagi.Unified.GuardedRobustSelection
set_option linter.style.header false

/-!
# ParetoLogit — конечный Pareto-контроллер на реальной
скалярной логистической цели (цикл 72)

Мост между циклами 70/71 (конечный контроллер над РЕАЛЬНЫМИ
преемниками и робастный отбор с ограниченной ошибкой оценки) и
точной логистической сертификацией циклов 36/42 (`logitCE`,
`descent_step_strict`, `logitStepCertExact`, `certified_loop`):

* `logitProblem eta` — конечная задача `Fin 2 → ℝ` с целью
  `-logitCE`: действие 0 — тождественный шаг, действие 1 —
  РЕАЛЬНЫЙ градиентный шаг `w + eta/(1+exp w)`; память и
  операции — явные модельные единицы (индексы `Fin 2`);
  безопасность каждого действия — фактическое неувеличение CE
  на всех скалярных состояниях (для действия 1 — строгий
  спуск при `eta > 0`, для действия 0 — тождество).
* `logit_selectedNext` — при допустимости обоих действий
  выбранный преемник РОВНО реальный шаг обновления для любого
  состояния и любого `eta > 0`; базовое тождественное действие
  исключается именно строгим улучшением CE.
* `logitEstimate` — детерминированный пессимистичный
  оцениватель `-logitCE w - 1/2` с ТОЧНОЙ ошибкой `1/2`;
  робастный отбор по нему всё равно исполняет реальный шаг
  (порядок оценок совпадает с порядком истинных значений).
  Это НЕ стохастическая калибровка, НЕ IID-модель и НЕ гарантия
  для произвольных искажённых оценок за пределами границы.
* `logit_budget_loop` — многошаговый бюджетный сертификат
  через существующий `certified_loop`/`certified_loop_all`/
  `certified_loop_strict` (без дублирующей индукции):
  полы качества на всех состояниях, точный телескоп CE-спусков,
  неотрицательный остаточный бюджет, строгий спуск при `n ≥ 1`.
* `logit_quadratic_bound` — квадратичная гарантия спуска из
  СУЩЕСТВУЮЩЕЙ `logitCE_trajectory_bound` (без второго
  телескопа) при ограниченных шагах `0 < eta t ≤ 2`.

Все утверждения — о данной одномерной one-example модели и
данном конечном семействе действий; это не глобально
оптимальная скорость обучения, не оптимальный нейрооптимизатор,
не минимальное число операций и не общая теория сходимости.
-/

namespace Hagi.Unified.ParetoLogit

open Hagi.Model Hagi.Unified.ParetoExecution Hagi.Unified.LogitCert
  Hagi.Unified.LinkedQVec Hagi.Unified.CertifiedLoop

/-! ### Конечная задача управления с реальной целью `-logitCE` -/

/-- Реальный преемник: действие 1 исполняет точный скалярный
градиентный шаг `w + eta/(1 + exp w)`, действие 0 — тождество. -/
noncomputable def logitStepFun (eta : ℝ) (a : Fin 2) (w : ℝ) : ℝ :=
  if a = 1 then w + eta / (1 + Real.exp w) else w

@[simp] theorem logitStepFun_zero (eta : ℝ) (w : ℝ) :
    logitStepFun eta 0 w = w := by
  simp [logitStepFun]

@[simp] theorem logitStepFun_one (eta : ℝ) (w : ℝ) :
    logitStepFun eta 1 w = w + eta / (1 + Real.exp w) := by
  simp [logitStepFun]

/-- Безопасность действия — ФАКТИЧЕСКОЕ неувеличение CE
преемника на всех скалярных состояниях (не безусловное
`True`): для действия 1 это строгий спуск при `eta > 0`,
для действия 0 — тождество. -/
def logitSafe (eta : ℝ) (a : Fin 2) : Prop :=
  ∀ w : ℝ, logitCE (logitStepFun eta a w) ≤ logitCE w

theorem logitSafe_zero (eta : ℝ) : logitSafe eta 0 := by
  intro w
  rw [logitStepFun_zero]

theorem logitSafe_one (eta : ℝ) (heta : 0 < eta) : logitSafe eta 1 := by
  intro w
  exact le_of_lt (descent_step_strict w eta heta)

/-- Именованный некомпьютабельный DecidablePred-инстанс
безопасности (через Classical.propDecidable). -/
noncomputable instance logitSafeDecidable (eta : ℝ) :
    DecidablePred (logitSafe eta) :=
  fun _ => Classical.propDecidable _

/-- Конечная задача управления over `Fin 2` и скалярного состояния:
цель в точности `-logitCE`, шаг — реальный преемник модели,
память/операции — явные модельные единицы (счётчики индексов). -/
noncomputable def logitProblem (eta : ℝ) : ControllerProblem (Fin 2) ℝ where
  value := fun w => -logitCE w
  step := logitStepFun eta
  memory := fun a => a.val
  operations := fun a => 2 * a.val
  safe := logitSafe eta

noncomputable instance logitProblemSafeDecidable (eta : ℝ) :
    DecidablePred (logitProblem eta).safe :=
  fun _ => Classical.propDecidable _

@[simp] theorem logitProblem_value (eta w : ℝ) :
    (logitProblem eta).value w = -logitCE w := rfl

@[simp] theorem logitProblem_step (eta : ℝ) (a : Fin 2) (w : ℝ) :
    (logitProblem eta).step a w = logitStepFun eta a w := rfl

/-- Допустимость тождественного действия при любых лимитах. -/
theorem logit_feasible_zero (eta : ℝ) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (logitProblem eta) M C := by
  refine mem_feasible.mpr ⟨logitSafe_zero eta, ?_, ?_⟩ <;>
    simp [logitProblem]

/-- Допустимость реального шага обновления при `eta > 0` и
достаточных лимитах (память 1, операции 2 — модельные
единицы действия 1). -/
theorem logit_feasible_one (eta : ℝ) (heta : 0 < eta) (M C : ℕ)
    (hM : 1 ≤ M) (hC : 2 ≤ C) :
    (1 : Fin 2) ∈ feasible (logitProblem eta) M C := by
  refine mem_feasible.mpr ⟨logitSafe_one eta heta, ?_, ?_⟩ <;>
    simp [logitProblem] <;> omega

/-! ### Точный отбор: преемник — реальный шаг обновления -/

/-- При допустимости обоих действий выбранный преемник РОВНО
реальный шаг `w + eta/(1+exp w)` для ЛЮБОГО состояния `w` и
любого `eta > 0`. Базовое тождественное действие исключается
именно строгим улучшением CE (`descent_step_strict`), а не
схемой перебора. Утверждение — о данном конечном семействе,
не о глобально оптимальной скорости обучения. -/
theorem logit_selection_eq_one (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selection (logitProblem eta) w M C 0 h0 = 1 := by
  apply selection_eq_one_of_value_lt (logitProblem eta) w M C h0 h1
  simp only [logitProblem_value, logitProblem_step, logitStepFun_zero,
    logitStepFun_one]
  have hdesc := descent_step_strict w eta heta
  linarith

/-- Выбранный преемник равен точному реальному шагу
обновления — при всех ресурсных предпосылках, оставшихся
видимыми (`h0`, `h1`). -/
theorem logit_selectedNext (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selectedNext (logitProblem eta) w M C 0 h0
      = w + eta / (1 + Real.exp w) := by
  unfold selectedNext
  rw [logit_selection_eq_one eta heta w M C h0 h1]
  exact logitStepFun_one eta w

/-- Выбранный преемник строго снижает CE (одношаговый отбор
качества общего вида — по любому состоянию, не только по
константному). -/
theorem logit_selected_strict (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    logitCE (selectedNext (logitProblem eta) w M C 0 h0) < logitCE w := by
  rw [logit_selectedNext eta heta w M C h0 h1]
  exact descent_step_strict w eta heta

/-! ### Робастный отбор с детерминированным пессимистичным
оценивателем (ошибка ровно 1/2; не стохастика и не IID) -/

/-- Оцениватель: истинная цель плюс постоянный
пессимистичный сдвиг `-1/2`. Детерминированная функция
состояния; НЕ стохастическая уверенность и НЕ выборка. -/
noncomputable def logitEstimate (w : ℝ) : ℝ := -logitCE w - 1 / 2

/-- Абсолютная ошибка оценивателя ТОЧНО равна `1/2` в каждом
состоянии. -/
theorem logitEstimate_error (w : ℝ) :
    |-logitCE w - logitEstimate w| = 1 / 2 := by
  unfold logitEstimate
  norm_num

/-- Ошибка оценивателя ровно `1/2` на всех преемниках всех
действий задачи (конечное семейство). -/
theorem logitEstimate_error_action (eta : ℝ) (a : Fin 2) (w : ℝ) :
    |(logitProblem eta).value ((logitProblem eta).step a w)
      - logitEstimate ((logitProblem eta).step a w)| = 1 / 2 :=
  logitEstimate_error _

/-- При допустимости обоих действий робастный отбор по
оценивателю с постоянным сдвигом снова исполняет РЕАЛЬНЫЙ
шаг обновления: порядок оценок совпадает с порядком истинных
значений цели. -/
theorem logit_robust_selection_eq_one (eta : ℝ) (heta : 0 < eta)
    (w : ℝ) (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selection (withEstimatedValue (logitProblem eta) logitEstimate)
      w M C 0 ((mem_feasible_withEstimatedValue _ _).mpr h0) = 1 := by
  have hm0 : (0 : Fin 2) ∈ feasible
      (withEstimatedValue (logitProblem eta) logitEstimate) M C :=
    (mem_feasible_withEstimatedValue _ _).mpr h0
  apply selection_eq_one_of_value_lt
    (withEstimatedValue (logitProblem eta) logitEstimate) w M C hm0
    ((mem_feasible_withEstimatedValue _ _).mpr h1)
  change logitEstimate ((logitProblem eta).step 0 w) <
    logitEstimate ((logitProblem eta).step 1 w)
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one]
  unfold logitEstimate
  have hdesc := descent_step_strict w eta heta
  linarith

/-- Робастный преемник — реальный скалярный шаг обновления,
следовательно строгий спуск CE. -/
theorem logit_robustNext (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    robustNext (logitProblem eta) logitEstimate w M C 0 h0
      = w + eta / (1 + Real.exp w) := by
  have hsel := logit_robust_selection_eq_one eta heta w M C h0 h1
  change (withEstimatedValue (logitProblem eta) logitEstimate).step
    (selection (withEstimatedValue (logitProblem eta) logitEstimate) w M C 0
      ((mem_feasible_withEstimatedValue _ _).mpr h0)) w = _
  rw [hsel]
  exact logitStepFun_one eta w

theorem logit_robust_strict (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    logitCE (robustNext (logitProblem eta) logitEstimate w M C 0 h0)
      < logitCE w := by
  rw [logit_robustNext eta heta w M C h0 h1]
  exact descent_step_strict w eta heta

/-- При нулевых лимитах единственно допустимо тождественное
действие: робастный запасной итог — исходное состояние
(независимо от оценивателя; за пределами этих явных лимитов
неубывание базы для произвольных искажённых оценок НЕ
выводится). -/
theorem logit_robustNext_fallback (eta : ℝ) (w : ℝ) :
    robustNext (logitProblem eta) logitEstimate w 0 0 0
      (logit_feasible_zero eta 0 0) = w := by
  refine robustNext_fallback (logitProblem eta) logitEstimate w 0 0 0
    (logit_feasible_zero eta 0 0) ?_ ?_
  · intro a ha hm
    have hlt : a.val < 2 := a.isLt
    have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
    have h1 := (mem_feasible.mp hm).2.1
    simp only [logitProblem] at h1
    omega
  · rw [logitProblem_step]
    exact logitStepFun_zero eta w

/-! ### Многошаговый бюджетный сертификат через certified_loop -/

/-- Локальная (действительно используемая) индукция: из
точного бюджетного телескопа и пошаговых ограничений `eta t ≤ b t`
бюджет неотрицателен на всей цепочке `t ≤ n`. -/
theorem logit_budget_nonneg {n : ℕ} {b eta : ℕ → ℝ} (hb0 : 0 ≤ b 0)
    (htel : ∀ t < n, b (t + 1) = b t - eta t)
    (hle : ∀ t < n, eta t ≤ b t) : ∀ t ≤ n, 0 ≤ b t := by
  intro t
  induction t with
  | zero => intro _; exact hb0
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    have hbt : 0 ≤ b t := ih (by omega)
    rw [htel t htn]
    have := hle t htn
    linarith

/-- Пошаговый сертификат цепочки: реальный переход
`w t → w (t+1)` с точным фактическим спуском, тратой бюджета
`eta t`, нулевым риском и полами `logitCE ≥ 0` (floor 0 на всех
пяти каналах `logitMeasured`). riskLim = 0 равномерно по цепочке. -/
noncomputable def logitTrajCert (n : ℕ) (w eta b : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (hpos : ∀ t < n, 0 < eta t)
    (hbnn : ∀ t ≤ n, 0 ≤ b t)
    (hbd : ∀ t < n, b (t + 1) ≤ b t - eta t) (t : Fin n) :
    StepCert (fun w => logitCE w) logitMeasured (fun _ => 0) 0
      (w t.val) (w (t.val + 1)) (b t.val) (b (t.val + 1)) where
  riskSpend := 0
  budgetSpend := eta t.val
  trans :=
    let core := logitStepCertExact (w t.val) (eta t.val) 0 (eta t.val)
      (b (t.val + 1)) (hpos t.val t.isLt)
      (hbnn (t.val + 1) (Nat.succ_le_of_lt t.isLt)) (le_refl 0)
    { objectiveDrop := core.objectiveDrop,
      objectiveDrop_pos := core.objectiveDrop_pos,
      actualDescent := by
        rw [hrec t.val t.isLt]
        exact core.actualDescent,
      riskBound := le_refl 0,
      budgetBound := hbnn (t.val + 1) (Nat.succ_le_of_lt t.isLt) }
  hriskSpend_nn := le_refl 0
  hbudgetSpend_nn := (hpos t.val t.isLt).le
  hdec := hbd t.val t.isLt
  quality := fun _ => logitCE_nonneg _

/-- **Многошаговый бюджетный сертификат логит-цикла** (через
существующие `certified_loop`, `certified_loop_all`,
`certified_loop_strict`; без дублирующей монотонной индукции).
Для точной рекуррентности `w(t+1) = w t + eta t/(1+exp(w t))`,
`0 < eta t ≤ 2`, `0 ≤ b 0`, `b(t+1) = b t − eta t`, `eta t ≤ b t`:
(a) все пять полей качества `logitMeasured` держатся на всех
фактических состояниях `t ≤ n` (в скалярной форме: `0 ≤ logitCE`);
(b) точный телескоп фактических спусков;
(c) неотрицательный остаточный бюджет и бюджетный телескоп
`b n ≤ b 0 − Σ eta t`;
(d) при `n ≥ 1` строгий спуск CE. -/
theorem logit_budget_loop (n : ℕ) (w eta b : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (heta : ∀ t < n, 0 < eta t ∧ eta t ≤ 2)
    (hb0 : 0 ≤ b 0)
    (htel : ∀ t < n, b (t + 1) = b t - eta t)
    (hle : ∀ t < n, eta t ≤ b t) :
    (∀ t ≤ n, FloorKept logitMeasured (w t) (fun _ => 0))
      ∧ (∀ t ≤ n, 0 ≤ logitCE (w t))
      ∧ (∑ t ∈ Finset.range n, (logitCE (w t) - logitCE (w (t + 1)))
          ≤ logitCE (w 0) - logitCE (w n))
      ∧ (0 ≤ b n ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, eta t)
      ∧ (1 ≤ n → logitCE (w n) < logitCE (w 0)) := by
  have hpos : ∀ t < n, 0 < eta t := fun t ht => (heta t ht).1
  have hbnn := logit_budget_nonneg hb0 htel hle
  have hbd : ∀ t < n, b (t + 1) ≤ b t - eta t :=
    fun t ht => le_of_eq (htel t ht)
  have h₀ : FloorKept logitMeasured (w 0) (fun _ => 0) :=
    fun _ => logitCE_nonneg _
  have hdrops : ∀ t : Fin n,
      (logitCE (w t.val) - logitCE (w (t.val + 1)))
        = (logitTrajCert n w eta b hrec hpos hbnn hbd t).trans.objectiveDrop :=
    fun t => by
      simp only [logitTrajCert, logitStepCertExact, hrec t.val t.isLt]
  have hspends : ∀ t : Fin n, eta t.val
      = (logitTrajCert n w eta b hrec hpos hbnn hbd t).budgetSpend :=
    fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := certified_loop (fun w => logitCE w)
    logitMeasured (fun _ => 0) 0 w b
    (fun t => logitCE (w t) - logitCE (w (t + 1))) eta n
    h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hspends
  refine ⟨certified_loop_all (fun w => logitCE w) logitMeasured
    (fun _ => 0) 0 w b (fun t => logitCE (w t) - logitCE (w (t + 1)))
    eta n h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hspends, ?_, h1, ⟨h3, h4⟩, ?_⟩
  · intro t _
    exact logitCE_nonneg (w t)
  · intro hn
    have hstrict := certified_loop_strict (fun w => logitCE w)
      logitMeasured (fun _ => 0) 0 w b
      (fun t => logitCE (w t) - logitCE (w (t + 1))) n
      h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hn
    exact hstrict.1

/-! ### Квадратичная гарантия из существующего телескопа -/

/-- Квадратичная гарантия спуска для ограниченных шагов
`0 < eta t ≤ 2` — ПРЯМОЕ переиспользование существующей
`Hagi.Model.logitCE_trajectory_bound` с направлением
`d t = 1/(1+exp(w t))` и его точным `hdir`-тождеством (второй
телескоп не доказывается). -/
theorem logit_quadratic_bound (n : ℕ) (w eta : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (heta : ∀ t < n, 0 < eta t ∧ eta t ≤ 2) :
    logitCE (w n) ≤ logitCE (w 0)
      - ∑ t ∈ Finset.range n, eta t * (1 / (1 + Real.exp (w t))) ^ 2 / 2 := by
  have hstep : ∀ t < n, w (t + 1)
      = w t + eta t * (1 / (1 + Real.exp (w t))) := by
    intro t ht
    rw [hrec t ht, mul_one_div]
  have hdir : ∀ t < n, (1 / (1 + Real.exp (w t))) ^ 2
      ≤ (-logitGrad (w t)) * (1 / (1 + Real.exp (w t))) := by
    intro t _
    have hgrad : -logitGrad (w t) = 1 / (1 + Real.exp (w t)) := by
      change -(-1 / (1 + Real.exp (w t))) = 1 / (1 + Real.exp (w t))
      field_simp
    rw [hgrad]
    exact le_of_eq (sq (1 / (1 + Real.exp (w t))))
  exact logitCE_trajectory_bound n w eta
    (fun t => 1 / (1 + Real.exp (w t))) hstep heta hdir

end Hagi.Unified.ParetoLogit
set_option linter.style.header false

/-!
# QualityResourceMin — exact minimum model resources under
an objective floor (cycle 73)

This complements the quality-first `ParetoExecution.selection`:
for a finite candidate family, choose a minimum-cost action whose
ACTUAL successor has `qfloor ≤ p.value (p.step a s)`. Feasibility is
the existing conjunction of model safety and both resource caps.

* `qualityEligible` is exactly the existing `feasible` condition plus
  the objective floor; it is not an externally declared desired effect.
* `resourceCost` is `(memory, operations)` in `ℕ ×ₗ ℕ`, explicitly
  memory-first. No arbitrary scalarization mixes different units.
* `exists_minimum_resource` reuses Mathlib's
  `Finset.exists_min_image`; `minimumResource` is the corresponding
  noncomputable `Classical.choose` witness.
* If the eligible set is empty, no witness can be supplied. The API
  does not fabricate a fallback, a quality improvement, or a feasible
  over-budget action.

This is an exact minimum only within the explicitly supplied finite
family and its model cost/objective. It does not certify a global
architecture optimum, minimal search complexity/FLOPs, physical bytes,
hardware latency, task accuracy, or an executable optimizer over ℝ.
-/

namespace Hagi.Unified.QualityResourceMin

open Prod.Lex Hagi.Unified.ParetoExecution

variable {A : Type} {S : Type*}

/-- The explicit memory-first resource cost in declared model units.
Operations decide only memory ties; no mixed scalar objective. -/
def resourceCost (p : ControllerProblem A S) (a : A) : ℕ ×ₗ ℕ :=
  toLex (p.memory a, p.operations a)

/-- An action is eligible if it belongs to the original finite feasible
family AND its actual successor meets the objective floor. -/
def qualityEligible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a : A) : Prop :=
  a ∈ feasible p M C ∧ qfloor ≤ p.value (p.step a s)

/-- A nonempty eligible finite family has a minimum resource-cost action,
using Mathlib's existing `Finset.exists_min_image`. -/
theorem exists_minimum_resource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∃ a, qualityEligible p s M C qfloor a
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p a ≤ resourceCost p b := by
  classical
  let U := Finset.univ.filter (qualityEligible p s M C qfloor)
  have hne : U.Nonempty :=
    ⟨a0, Finset.mem_filter.mpr ⟨Finset.mem_univ a0, h0⟩⟩
  obtain ⟨a, ha, hmin⟩ :=
    Finset.exists_min_image U (resourceCost p) hne
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)

/-- Exact finite-family selection at minimum declared resource cost.
The eligible witness excludes the empty-family case; the choice is
mathematical selection, not a certified executable search algorithm. -/
noncomputable def minimumResource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) : A :=
  Classical.choose (exists_minimum_resource p s M C qfloor a0 h0)

/-- Full specification: the selected action is eligible, and no other
eligible action has smaller resource cost. Cost order is the explicitly
supplied memory-first lexicographic order, not a universal preference. -/
theorem minimumResource_spec (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    qualityEligible p s M C qfloor (minimumResource p s M C qfloor a0 h0)
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p (minimumResource p s M C qfloor a0 h0)
            ≤ resourceCost p b :=
  Classical.choose_spec (exists_minimum_resource p s M C qfloor a0 h0)

/-- The selected action retains the original model safety and both
exact resource caps; no objective-floor exception is introduced. -/
theorem minimumResource_feasible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    minimumResource p s M C qfloor a0 h0 ∈ feasible p M C :=
  (minimumResource_spec p s M C qfloor a0 h0).1.1

/-- Quality is checked at the ACTUAL successor of the selected action,
not at the witness or at synthesized metadata. -/
theorem minimumResource_next_quality_ge (p : ControllerProblem A S)
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    qfloor ≤ p.value (p.step (minimumResource p s M C qfloor a0 h0) s) :=
  (minimumResource_spec p s M C qfloor a0 h0).1.2

/-- No eligible action has smaller declared resource cost than the
chosen action. This is class-relative, and the cost is not physical
measurement or a claim of minimum search time. -/
theorem minimumResource_cost_min (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∀ b, qualityEligible p s M C qfloor b →
      resourceCost p (minimumResource p s M C qfloor a0 h0)
        ≤ resourceCost p b :=
  (minimumResource_spec p s M C qfloor a0 h0).2

/-- The selected action retains the original model-level safety predicate.
This does not identify that predicate with physical safety. -/
theorem minimumResource_safe (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    p.safe (minimumResource p s M C qfloor a0 h0) :=
  (mem_feasible.mp (minimumResource_feasible p s M C qfloor a0 h0)).1

end Hagi.Unified.QualityResourceMin
set_option linter.style.header false

/-!
# Guarded robust selection for the scalar logistic controller

This is a one-step specialization of `guardedRobustNext` to the actual
`logitProblem`, with `logitEstimate` and guard radius `1 / 2`.  The selected
successor is always an actual feasible logit successor.  Without an estimated
upgrade it is exactly the stay state; in all cases its logistic cross-entropy
is no greater than the stay value.

An exact update requires both feasibility of action `1` and an estimated
upgrade.  The upgrade can alternatively be obtained from an explicit true-CE
drop of at least `1`; smaller drops need not pass the `2 * (1 / 2)` guard.
These are deterministic one-step statements, not probability, generalization,
or parameter-convergence claims.
-/

namespace Hagi.Unified.GuardedRobustLogit

open Hagi.Model
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.ParetoLogit
open Hagi.Unified.LogitCert

/-- The guarded robust successor specialized to the scalar logistic problem. -/
noncomputable def guardedLogitNext (eta : ℝ) (M C : ℕ) (w : ℝ) : ℝ :=
  guardedRobustNext (logitProblem eta) logitEstimate (1 / 2) w M C
    (0 : Fin 2) (logit_feasible_zero eta M C)

/-- The guarded successor is the actual step of some original feasible action. -/
theorem guardedLogitNext_exists (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ a ∈ feasible (logitProblem eta) M C,
      guardedLogitNext eta M C w = logitStepFun eta a w := by
  simpa only [guardedLogitNext, logitProblem_step] using
    (guardedRobustNext_exists (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) (logit_feasible_zero eta M C))

/-- If no feasible action passes the estimate-margin guard, the actual
successor is exactly the stay state. -/
theorem guardedLogitNext_of_no_upgrade (eta : ℝ) (M C : ℕ) (w : ℝ)
    (h : ¬ estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w := by
  unfold guardedLogitNext
  rw [guardedRobustNext_of_no_upgrade (logitProblem eta) logitEstimate (1 / 2)
    w M C (0 : Fin 2) (logit_feasible_zero eta M C) h]
  exact logitStepFun_zero eta w

/-- Unconditional one-step logistic-CE non-regression.  No positivity or
resource assumptions are needed: the error bound holds on every feasible
successor, including the always-feasible stay action. -/
theorem logitCE_guardedLogitNext_le (eta : ℝ) (M C : ℕ) (w : ℝ) :
    logitCE (guardedLogitNext eta M C w) ≤ logitCE w := by
  have h := guardedRobustNext_quality_ge_stay (logitProblem eta) logitEstimate
    (1 / 2) w M C (0 : Fin 2) (logit_feasible_zero eta M C)
    (fun a _ => le_of_eq (logitEstimate_error_action eta a w))
  change -logitCE w ≤ -logitCE (guardedLogitNext eta M C w) at h
  linarith only [h]

/-- A true-CE drop of at least `1` by action `1` supplies the exact
`2 * (1 / 2)` estimated-upgrade margin. -/
theorem estimatedUpgrade_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) := by
  refine ⟨1, logit_feasible_one eta heta M C hM hC, ?_⟩
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one]
  unfold logitEstimate
  norm_num
  linarith only [hdrop]

/-- With action `1` feasible and the estimated-upgrade guard active, the
wrapper executes the existing robust logistic update exactly. -/
theorem guardedLogitNext_eq_update_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  unfold guardedLogitNext guardedRobustNext
  rw [ite_eq_left hup]
  exact logit_robustNext eta heta w M C (logit_feasible_zero eta M C)
    (logit_feasible_one eta heta M C hM hC)

/-- The same exact update follows from an explicit true-CE drop of at least
`1`, rather than from a pre-established estimated-upgrade witness. -/
theorem guardedLogitNext_eq_update_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  exact guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w
    (estimatedUpgrade_of_logitCE_drop eta heta M C hM hC w hdrop)

/-- Under the exact-update resources and an active guard, logistic CE strictly
decreases by the existing scalar descent theorem. -/
theorem logitCE_guardedLogitNext_lt_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    logitCE (guardedLogitNext eta M C w) < logitCE w := by
  rw [guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w hup]
  exact descent_step_strict w eta heta

end Hagi.Unified.GuardedRobustLogit
set_option linter.style.header false

/-!
# RobustResourceMin — minimum declared resources under a
bounded-estimation quality floor (cycle 74)

The exact finite policy of cycle 73 requires the successor's objective
value directly. Here only `estimate` may be available, but every actual
successor has error bounded by a uniform `eps`. Use the conservative
eligibility criterion
`qfloor + eps ≤ estimate (p.step a s)`. It implies the true-objective
floor `qfloor ≤ p.value (p.step a s)` by elementary arithmetic.

`robustMinimumResource` directly reuses `minimumResource` on the existing
`withEstimatedValue` problem. Resource costs and actual successors remain
those of `p`; there is no synthetic effect, second minimization engine or
resource exception at the upgrade boundary. The witness supplies
nonemptiness and the error bound supplies all quantitative claims.

Optimality is ONLY among lower-bound-certified candidates. A cheaper
candidate can meet the TRUE floor yet be excluded because its lower
bound cannot certify it. There is therefore no claim of minimum cost
among all truly floor-eligible actions, nor global/NAS/hardware/search
optimality. The absolute-error premise is deterministic; it is not a
statistical confidence level, calibration claim or physical measurement.
-/

namespace Hagi.Unified.RobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Choose a minimum-resource action in the estimated, conservative
floor class. Safety, caps, and actual step are definitionally unchanged. -/
noncomputable def robustMinimumResource {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) : A :=
  minimumResource (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0

/-- The chosen candidate's estimate meets the shifted floor, and it is
eligible in the original-step / original-resource policy. -/
theorem robustMinimumResource_eligible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    qualityEligible (withEstimatedValue p estimate) s M C (qfloor + eps)
      (robustMinimumResource estimate s M C qfloor eps a0 h0) :=
  (minimumResource_spec (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0).1

/-- The chosen action still has the original model safety and both exact
resource caps, independent of the quality-estimation error. -/
theorem robustMinimumResource_feasible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    robustMinimumResource estimate s M C qfloor eps a0 h0 ∈ feasible p M C := by
  have hf := minimumResource_feasible (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0
  exact (mem_feasible_withEstimatedValue p estimate).mp hf

/-- The actual successor meets the true floor. The only estimate-to-truth
connection is the explicitly supplied uniform absolute-error bound. -/
theorem robustMinimumResource_actual_quality_ge {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0)
    (herr : ∀ a, |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    qfloor ≤ p.value (p.step (robustMinimumResource estimate s M C
      qfloor eps a0 h0) s) := by
  have hq := minimumResource_next_quality_ge (withEstimatedValue p estimate)
    s M C (qfloor + eps) a0 h0
  have he := (abs_le.mp (herr (robustMinimumResource estimate s M C
    qfloor eps a0 h0))).1
  change qfloor + eps ≤ estimate (p.step (robustMinimumResource estimate s M C
    qfloor eps a0 h0) s) at hq
  linarith

/-- No lower-bound-certified competitor has smaller declared resource
cost. This deliberately does NOT quantify over every truly eligible b. -/
theorem robustMinimumResource_cost_min {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    ∀ b, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) b →
      resourceCost p (robustMinimumResource estimate s M C qfloor eps a0 h0)
        ≤ resourceCost p b := by
  intro b hb
  exact minimumResource_cost_min (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0 b hb

/-- With the exact objective as estimator and zero error, this connector
is definitionally the preceding exact minimum-resource selector. No new
algorithm or conservativeness is added in that exact special case. -/
theorem robustMinimumResource_zero_exact {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    robustMinimumResource p.value s M C qfloor 0 a0 (by simpa using h0)
      = minimumResource p s M C qfloor a0 h0 := by
  simp [robustMinimumResource, withEstimatedValue, minimumResource]

end Hagi.Unified.RobustResourceMin
set_option linter.style.header false

/-!
# Guarded minimum-resource selection with baseline protection

When a feasible action has estimated quality at least `2 * eps` above the
stay action, this wrapper uses the existing robust minimum-resource selector.
The explicit one-sided baseline bound `hbase` turns that guard into a
certificate for the actual stay-quality floor. Otherwise it returns `stay`.

Under pointwise error bounds on currently feasible actions, the chosen action
has actual quality no lower than `stay`. Its declared memory-first resource
cost is minimal among the lower-bound-certified competitors specified below,
not among all truly nondecreasing actions or architectures.
-/

namespace Hagi.Unified.GuardedRobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.GuardedRobustSelection Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*} [Fintype A]

/-- An estimated upgrade and the one-sided baseline error bound certify the
actual stay-quality floor for the original feasible action `a`. -/
theorem baselineCertificate_of_margin (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay a : A) (ha : a ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (hmargin : estimate (p.step stay s) + 2 * eps ≤ estimate (p.step a s)) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) a := by
  refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr ha, ?_⟩
  change p.value (p.step stay s) + eps ≤ estimate (p.step a s)
  linarith

/-- Use the existing robust minimum-resource action when an estimated upgrade
exists, and otherwise stay. The baseline bound supplies the eligibility
certificate; no additional action or optimization engine is introduced. -/
noncomputable def guardedMinimumResource (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) : A := by
  classical
  have _ := h0
  exact if h_up : estimatedUpgrade p estimate eps s M C stay then
    robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
      (Classical.choose h_up)
      (baselineCertificate_of_margin p estimate eps s M C stay
        (Classical.choose h_up) (Classical.choose_spec h_up).1 hbase
        (Classical.choose_spec h_up).2)
  else
    stay

/-- Without an estimated upgrade, the guarded action is exactly `stay`. -/
theorem guardedMinimumResource_of_no_upgrade (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h : ¬ estimatedUpgrade p estimate eps s M C stay) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase = stay := by
  classical
  rw [guardedMinimumResource, dite_eq_right]
  exact h

/-- The guarded action remains feasible for the original problem in both the
upgrade and fallback branches. -/
theorem guardedMinimumResource_feasible (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase ∈
      feasible p M C := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · unfold guardedMinimumResource
    rw [dite_eq_left]
    · exact robustMinimumResource_feasible _ _ _ _ _ _ _ _
    · exact hup
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]
    exact h0

/-- With estimation errors bounded on currently feasible actions, the guarded
minimum-resource action has actual quality at least that of `stay`. -/
theorem guardedMinimumResource_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    p.value (p.step stay s) ≤ p.value (p.step
      (guardedMinimumResource p estimate eps s M C stay h0 hbase) s) := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · let a0 := Classical.choose hup
    let hcert := baselineCertificate_of_margin p estimate eps s M C stay a0
      (Classical.choose_spec hup).1 hbase (Classical.choose_spec hup).2
    have hquality : p.value (p.step stay s) ≤ p.value (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) := by
      have hfeasible := robustMinimumResource_feasible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert
      have hq := (robustMinimumResource_eligible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert).2
      have he := (abs_le.mp (herr _ hfeasible)).1
      change p.value (p.step stay s) + eps ≤ estimate (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) at hq
      linarith
    unfold guardedMinimumResource
    rw [dite_eq_left]
    exact hquality
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]

/-- For any feasible competitor whose actual quality exceeds the stay quality
by at least `2 * eps`, the guarded upgrade has no greater declared resource
cost. This is the existing certified-class minimum, not global optimality. -/
theorem guardedMinimumResource_cost_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h_up : estimatedUpgrade p estimate eps s M C stay)
    (b : A) (hb : b ∈ feasible p M C)
    (hgain : p.value (p.step stay s) + 2 * eps ≤ p.value (p.step b s))
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    resourceCost p (guardedMinimumResource p estimate eps s M C stay h0 hbase) ≤
      resourceCost p b := by
  classical
  have hb_upper := (abs_le.mp (herr b hb)).2
  have hbCert : qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) b := by
    refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr hb, ?_⟩
    change p.value (p.step stay s) + eps ≤ estimate (p.step b s)
    linarith
  unfold guardedMinimumResource
  rw [dite_eq_left]
  · exact robustMinimumResource_cost_min _ _ _ _ _ _ _ _ b hbCert
  · exact h_up

end Hagi.Unified.GuardedRobustResourceMin
set_option linter.style.header false

/-!
# RobustCostSensitivity — uncertainty radius and least certified
resource cost (cycle 75)

Increasing epsilon shifts the estimator floor UP, hence shrinks the
lower-bound-certified finite class. If both radius levels have eligible
witnesses, the minimum declared resource cost cannot decrease: the
small-radius minimum can be compared with the selected large-radius
candidate, whose eligibility transfers into the smaller class.

The order remains the explicit `(memory, operations)` Prod.Lex order.
Memory itself is monotone; neither strict monotonicity nor a separate
operations-time/FLOPs monotonicity follows. Both witness hypotheses stay
visible because sufficiently high uncertainty may make the class empty.
This does not optimize over the wider truly-eligible class and does not
measure physical resources or make a statistical confidence assertion.
-/

namespace Hagi.Unified.RobustCostSensitivity

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*}

/-- Larger radius implies membership in the smaller-radius certified
class. The actual feasibility component is unchanged. -/
theorem robustEligible_mono_epsilon {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ)
    (h_eps : eps1 ≤ eps2) {a : A}
    (ha : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a := by
  exact ⟨ha.1, by linarith [ha.2]⟩

/-- Minimum declared resource cost is nondecreasing as the robustness
radius grows. Both eligible witnesses are required; this is not an
existence assertion for empty certified classes. -/
theorem robustMinimumResource_cost_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    resourceCost p (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ resourceCost p
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  apply robustMinimumResource_cost_min estimate s M C qfloor eps1 a1 h_small
    (robustMinimumResource estimate s M C qfloor eps2 a2 h_large)
  exact robustEligible_mono_epsilon estimate s M C qfloor eps1 eps2 h_eps
    (robustMinimumResource_eligible estimate s M C qfloor eps2 a2 h_large)

/-- The first memory coordinate is nondecreasing under the same witness
premises. No separate operations monotone claim is made. -/
theorem robustMinimumResource_memory_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    p.memory (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ p.memory
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  have hcost := robustMinimumResource_cost_mono estimate s M C qfloor
    eps1 eps2 a1 a2 h_eps h_small h_large
  exact Prod.Lex.monotone_fst _ _ hcost

end Hagi.Unified.RobustCostSensitivity
set_option linter.style.header false

/-!
# RobustRadius — exact boundary for estimator-floor admissibility
(cycle 76)

For a given objective floor, the lower-bound-certified class is nonempty
precisely when `eps ≤ maxEstimate − qfloor`, where `maxEstimate` is the
existing finite selector's estimated value on its ACTUAL successor.
The boundary is included; a larger radius has no eligible action.

This reuses `ParetoExecution.selection` over `withEstimatedValue`.
`h_stay` supplies only the nonempty original feasible set, not arbitrary
robust-floor feasibility. Resource caps remain original and no minimum
resource or search-time engine is duplicated.

The scalar margin is not a conic/MIP robust-feasibility-radius algorithm,
an architecture optimum, physical resource certification or statistical
confidence. Actual objective-floor quality still requires the separate
absolute-error hypothesis from the previous connector.
-/

namespace Hagi.Unified.RobustRadius

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Maximum estimated value on an actual successor, computed by the
existing finite selector. Only its value estimate matters in the margin. -/
noncomputable def estimatedMaxValue {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C) : ℝ :=
  (withEstimatedValue p estimate).value
    (selectedNext (withEstimatedValue p estimate) s M C stay
      ((mem_feasible_withEstimatedValue p estimate).mpr h_stay))

/-- The selected maximum dominates the estimated value on each actual
successor of every original-feasible candidate. -/
theorem estimatedMaxValue_upper {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C)
    {a : A} (ha : a ∈ feasible p M C) :
    estimate (p.step a s) ≤ estimatedMaxValue estimate s M C stay h_stay := by
  have h := selection_quality_optimal (withEstimatedValue p estimate)
    s M C stay ((mem_feasible_withEstimatedValue p estimate).mpr h_stay)
    a ((mem_feasible_withEstimatedValue p estimate).mpr ha)
  exact h

/-- Exact admissibility criterion for existence of a conservative
floor-certified action. Boundary point included. -/
theorem robust_eligible_iff_radius_le_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    (∃ a, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a) ↔
      eps ≤ estimatedMaxValue estimate s M C stay h_stay - qfloor := by
  constructor
  · rintro ⟨a, hfe, hq⟩
    have hb := estimatedMaxValue_upper estimate s M C stay h_stay hfe
    exact sub_nonneg.mp (by linarith : 0 ≤
      estimatedMaxValue estimate s M C stay h_stay - qfloor - eps)
  · intro he
    let hse : stay ∈ feasible (withEstimatedValue p estimate) M C :=
      (mem_feasible_withEstimatedValue p estimate).mpr h_stay
    refine ⟨selection (withEstimatedValue p estimate) s M C stay hse,
      selection_admissible (withEstimatedValue p estimate) s M C stay hse, ?_⟩
    change qfloor + eps ≤ estimate (p.step
      (selection (withEstimatedValue p estimate) s M C stay hse) s)
    dsimp [estimatedMaxValue, selectedNext] at he
    linarith

/-- After the maximum estimated margin, no candidate can be eligible. -/
theorem no_robust_eligible_above_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (h_eps : estimatedMaxValue estimate s M C stay h_stay - qfloor < eps) :
    ∀ a, ¬ qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a := by
  intro a ha
  have hb := estimatedMaxValue_upper estimate s M C stay h_stay ha.1
  have hq := ha.2
  linarith

end Hagi.Unified.RobustRadius
set_option linter.style.header false

/-!
# Executable finite selection with logical guard and relation counters
(cycle 77)

This module instruments the existing `List.filter` and `List.argmin`
algorithms. It does not implement another minimum engine. Logical
composite-guard and pair-relation calls are counted, not physical
instructions, wall time, FLOPs, or allocations. In particular, a
comparison may evaluate its cost function more than once, and a
short-circuiting guard need not evaluate every field or successor.
-/

namespace Hagi.Unified.ExecutableSelection

/-- Filter a finite list while counting logical composite-guard calls. -/
def auditedFilter {α : Type*} (guard : α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: as =>
      let (accepted, n) := auditedFilter guard as
      (if guard a then a :: accepted else accepted, n + 1)

/-- The instrumented filter retains precisely the ordinary filter's
candidates. -/
theorem auditedFilter_fst {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).1 = as.filter guard := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Every supplied action is inspected by one logical composite guard. -/
theorem auditedFilter_snd {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).2 = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Same step as the library argmin fold, plus one counter increment
when there is an incumbent and hence a relation call. -/
private def argminStep {α R : Type*} [LinearOrder R] (cost : α → R)
    (incumbent : Option α × ℕ) (a : α) : Option α × ℕ :=
  (List.argAux (fun b c => cost b < cost c) incumbent.1 a,
    incumbent.2 + if incumbent.1.isSome then 1 else 0)

/-- Audited finite minimum. The second component counts relation cells
visited by the fold; it is not a measurement of run-time instructions. -/
def auditedArgmin {α R : Type*} [LinearOrder R] (cost : α → R) (as : List α) :
    Option α × ℕ :=
  as.foldl (argminStep cost) (none, 0)

private theorem foldl_argminStep_fst {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (best : Option α) (n : ℕ) :
    (as.foldl (argminStep cost) (best, n)).1 =
      as.foldl (List.argAux fun b c => cost b < cost c) best := by
  induction as generalizing best n with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih _ _

private theorem foldl_argminStep_snd_some {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (a : α) (n : ℕ) :
    (as.foldl (argminStep cost) (some a, n)).2 = n + as.length := by
  induction as generalizing a n with
  | nil => rfl
  | cons b as ih =>
      simp only [List.foldl_cons]
      by_cases h : cost b < cost a
      · have hi := ih b (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega
      · have hi := ih a (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega

private theorem foldl_argminStep_snd_none_cons {α R : Type*} [LinearOrder R]
    (cost : α → R) (a : α) (as : List α) (n : ℕ) :
    ((a :: as).foldl (argminStep cost) (none, n)).2 = n + as.length := by
  simp only [List.foldl_cons]
  simpa [argminStep, List.argAux] using foldl_argminStep_snd_some cost as a n

/-- The audited fold selects exactly the same candidate as `List.argmin`;
its first-on-tie and all minimum properties are inherited, not duplicated. -/
theorem auditedArgmin_fst {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).1 = List.argmin cost as := by
  exact foldl_argminStep_fst cost as none 0

/-- Zero comparisons for no candidates; otherwise exactly one fewer than
the number of admitted candidates. This follows from the fold itself. -/
theorem auditedArgmin_snd {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).2 = as.length - 1 := by
  cases as with
  | nil => rfl
  | cons a as =>
      simpa [auditedArgmin] using foldl_argminStep_snd_none_cons cost a as 0

end Hagi.Unified.ExecutableSelection


/-!
# Executable discrete finite resource selection (cycle 77)

A supplied action list is filtered by a concrete Bool guard, then the
existing `List.argmin` chooses minimum memory-first resource cost among
quality-eligible actions **in that list**. No `Classical.choose`, default
action, physical-safety claim, or arbitrary real-valued search is added.

The point-model adapter casts integer quality into the old real-valued
controller interface. Its guard equivalence and equality with the old
minimum cost use that cast model; they do not execute arbitrary real CE.
Completeness of the input list is a separate explicit premise whenever
whole-Fintype minimality is claimed. Instrumented counts are logical
guard and pair-relation calls, not hardware instructions or latency.
-/

namespace Hagi.Unified.ExecutableController

open Hagi.Unified.ExecutableSelection
open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

/-- A supplied discrete point model with the old controller's `A : Type`
action carrier. `safetyGuard` is only the model's Boolean admission
guard, not evidence of physical safety. -/
structure DiscreteProgram (A : Type) (S : Type*) where
  actions : List A
  state : S
  step : A → S → S
  quality : S → ℤ
  safetyGuard : A → S → Bool
  memory : A → ℕ
  operations : A → ℕ
  memoryCap : ℕ
  operationsCap : ℕ
  qualityFloor : ℤ

/-- Total executable admission at the supplied state. Quality is checked
at the actual successor. Boolean short-circuiting means that a rejected
prefix need not evaluate every later field or successor. -/
def admissionGuard {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) : Bool :=
  p.safetyGuard a p.state && decide (p.memory a ≤ p.memoryCap) &&
    decide (p.operations a ≤ p.operationsCap) &&
    decide (p.qualityFloor ≤ p.quality (p.step a p.state))

theorem admissionGuard_eq_true {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      p.safetyGuard a p.state = true ∧
        p.memory a ≤ p.memoryCap ∧ p.operations a ≤ p.operationsCap ∧
        p.qualityFloor ≤ p.quality (p.step a p.state) := by
  simp [admissionGuard, and_assoc]

/-- Adapter of the supplied point model into the old real-valued
controller. Only the quality value is cast; `step` and resources are
unchanged. `safe` captures the guard at the fixed supplied state. -/
@[reducible] def toController {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    ControllerProblem A S where
  value s := (p.quality s : ℝ)
  step := p.step
  memory := p.memory
  operations := p.operations
  safe a := p.safetyGuard a p.state = true

instance {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    DecidablePred (toController p).safe :=
  fun a => inferInstanceAs (Decidable (p.safetyGuard a p.state = true))

/-- The executable guard is exactly old eligibility in the integer-cast
controller. Both directions cover arbitrary signs of integer quality. -/
theorem admissionGuard_iff_qualityEligible {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      qualityEligible (p := toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a := by
  rw [admissionGuard_eq_true, qualityEligible, mem_feasible (p := toController p)]
  constructor
  · rintro ⟨hsafe, hmemory, hoperations, hquality⟩
    refine ⟨⟨hsafe, hmemory, hoperations⟩, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ)
    exact_mod_cast hquality
  · rintro ⟨⟨hsafe, hmemory, hoperations⟩, hquality⟩
    refine ⟨hsafe, hmemory, hoperations, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ) at hquality
    exact_mod_cast hquality

/-- Selection result together with its explicit logical work counters.
These are model counts, not an automatically generated native profile. -/
structure SelectionReport (A : Type) where
  selected : Option A
  guardCalls : ℕ
  comparisons : ℕ

/-- One guarded filter and one existing argmin fold. Both are inspected
only through the audited kernel; no second minimum algorithm is used. -/
def selectionReport {A : Type} {S : Type*} (p : DiscreteProgram A S) : SelectionReport A :=
  let admitted := auditedFilter (admissionGuard p) p.actions
  let best := auditedArgmin (fun a => resourceCost (toController p) a) admitted.1
  { selected := best.1
    guardCalls := admitted.2
    comparisons := best.2 }

/-- The executable selection as an option; no artificial default action. -/
def finiteSelection {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option A :=
  (selectionReport p).selected

/-- Actual successor of the returned action at the supplied state. -/
def selectedNext {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option S :=
  (finiteSelection p).map (fun a => p.step a p.state)

private theorem finiteSelection_eq_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p =
      List.argmin (fun a => resourceCost (toController p) a)
        (p.actions.filter (admissionGuard p)) := by
  unfold finiteSelection selectionReport
  simp only [auditedArgmin_fst, auditedFilter_fst]

private theorem finiteSelection_mem_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ List.argmin (fun a => resourceCost (toController p) a)
      (p.actions.filter (admissionGuard p)) := by
  rw [← finiteSelection_eq_argmin]
  simp [ha]

/-- A returned action really occurs in the supplied list and passed the
complete composite guard. -/
theorem finiteSelection_mem {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ p.actions ∧ admissionGuard p a = true := by
  exact List.mem_filter.mp (List.argmin_mem (finiteSelection_mem_argmin p ha))

/-- Minimum memory-first resource cost over all eligible input-list
members. Nothing is claimed about unlisted candidates. -/
theorem finiteSelection_minimum {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) (b : A)
    (hb : b ∈ p.actions) (hguard : admissionGuard p b = true) :
    resourceCost (toController p) a ≤ resourceCost (toController p) b := by
  exact List.le_of_mem_argmin (List.mem_filter.mpr ⟨hb, hguard⟩)
    (finiteSelection_mem_argmin p ha)

/-- No returned action precisely when every input action fails the guard.
There is no fallback witness, and no physical state unchanged theorem. -/
theorem finiteSelection_none_iff {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p = none ↔
      ∀ a ∈ p.actions, admissionGuard p a = false := by
  rw [finiteSelection_eq_argmin, List.argmin_eq_none, List.filter_eq_nil_iff]
  constructor
  · intro h a ha
    have hg := h a ha
    cases hb : admissionGuard p a <;> simp_all
  · intro h a ha
    have hb := h a ha
    simp [hb]

/-- The optional successor is the actual `step`, not an effects record. -/
theorem selectedNext_eq_some {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    selectedNext p = some (p.step a p.state) := by
  simp [selectedNext, ha]

/-- Guard counter is exactly the number of supplied actions, including
when the filtered candidate list is empty. -/
theorem selectionReport_guardCalls {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).guardCalls = p.actions.length := by
  simpa [selectionReport] using auditedFilter_snd (admissionGuard p) p.actions

/-- Pair-relation comparisons are one fewer than admitted candidates,
or zero if there is no admitted candidate. -/
theorem selectionReport_comparisons {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons =
      (p.actions.filter (admissionGuard p)).length - 1 := by
  simpa [selectionReport, auditedFilter_fst] using
    auditedArgmin_snd (fun a => resourceCost (toController p) a)
      (auditedFilter (admissionGuard p) p.actions).1

/-- Model relation-call count is bounded by total inputs, but this is
not minimum CPU, FLOPs, wall time, or a universal search lower bound. -/
theorem selectionReport_comparisons_le {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons ≤ p.actions.length := by
  rw [selectionReport_comparisons]
  exact (Nat.sub_le _ _).trans (List.length_filter_le _ _)

/-- Equality with the old mathematical minimum cost in the cast model,
provided the input list covers every action. The concrete selected
actions may differ under cost ties; only their resource costs are equal. -/
theorem finiteSelection_cost_eq_minimumResource {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) {a : A} (ha : finiteSelection p = some a)
    (hcomplete : ∀ b, b ∈ p.actions) :
    resourceCost (toController p) a = resourceCost (toController p)
      (minimumResource (toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a
        ((admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2)) := by
  let hquality : qualityEligible (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a :=
    (admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2
  change resourceCost (toController p) a = resourceCost (toController p)
    (minimumResource (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a hquality)
  have hmin := minimumResource_spec (toController p) p.state p.memoryCap
    p.operationsCap (p.qualityFloor : ℝ) a hquality
  exact le_antisymm
    (finiteSelection_minimum p ha _ (hcomplete _)
      ((admissionGuard_iff_qualityEligible p _).mpr hmin.1))
    (hmin.2 a hquality)

end Hagi.Unified.ExecutableController
set_option linter.style.header false



/-!
# Guarded robust trajectories with fresh estimates

At every time step, the recursive path applies the existing guarded robust
selector to the actual current state, using that step's estimate and error
radius. If the stay action fixes every state and every feasible successor
satisfies the supplied pointwise error bound, actual model quality is monotone.
An upper bound on actual quality then gives convergence to its conditional
supremum.

The actual successive quality gains are nonnegative, telescope exactly, and
are summable with total at most the supplied quality bound minus initial
quality. These are deterministic statements about model quality only. They do
not assert convergence of states or parameters, estimator calibration,
optimality, stochastic performance, or physical safety.
-/

namespace Hagi.Unified.GuardedRobustTrajectory

open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Filter Topology

variable {A : Type} {S : Type*} [Fintype A]

/-- The guarded recursive path from `s0`, with fresh `estimate t` and `eps t`
used for the successor selected at time `t`. -/
noncomputable def guardedRobustPath (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) : ℕ → S
  | 0 => s0
  | t + 1 => guardedRobustNext p (estimate t) (eps t)
      (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0

@[simp] theorem guardedRobustPath_zero (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) :
    guardedRobustPath p estimate eps M C stay h0 s0 0 = s0 := rfl

@[simp] theorem guardedRobustPath_succ (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) :
    guardedRobustPath p estimate eps M C stay h0 s0 (t + 1) =
      guardedRobustNext p (estimate t) (eps t)
        (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0 := rfl

/-- Every recursive successor is the actual successor of an original feasible
action at the actual current path state. -/
theorem guardedRobustPath_succ_exists (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) :
    ∃ a ∈ feasible p M C,
      guardedRobustPath p estimate eps M C stay h0 s0 (t + 1) =
        p.step a (guardedRobustPath p estimate eps M C stay h0 s0 t) := by
  rw [guardedRobustPath_succ]
  exact guardedRobustNext_exists p (estimate t) (eps t)
    (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0

/-- Fresh feasible-successor error bounds and an identity stay action imply
that actual model quality does not decrease at any recursive step. -/
theorem guardedRobustPath_quality_step (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) (t : ℕ) :
    p.value (guardedRobustPath p estimate eps M C stay h0 s0 t) ≤
      p.value (guardedRobustPath p estimate eps M C stay h0 s0 (t + 1)) := by
  rw [guardedRobustPath_succ]
  have hstay := guardedRobustNext_quality_ge_stay p (estimate t) (eps t)
    (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0
    (h_bounds t)
  rwa [hid] at hstay

/-- Actual quality along the guarded recursive path is monotone. -/
theorem guardedRobustPath_quality_monotone (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) :
    Monotone (fun t => p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t)) :=
  monotone_nat_of_le_succ
    (guardedRobustPath_quality_step p estimate eps M C stay h0 s0 hid h_bounds)

/-- Bounded monotone actual quality converges to its conditional supremum;
the supremum is not asserted to equal the supplied bound or a global optimum. -/
theorem guardedRobustPath_quality_tendsto_ciSup (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Tendsto (fun t => p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t)) atTop
      (𝓝 (⨆ t, p.value (guardedRobustPath
        p estimate eps M C stay h0 s0 t))) := by
  apply tendsto_atTop_ciSup
    (guardedRobustPath_quality_monotone p estimate eps M C stay h0 s0 hid h_bounds)
  refine ⟨B, ?_⟩
  rintro x ⟨t, rfl⟩
  exact hB t

/-- The actual one-step gain along the guarded recursive path. -/
noncomputable def guardedRobustGain (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) : ℝ :=
  p.value (guardedRobustPath p estimate eps M C stay h0 s0 (t + 1)) -
    p.value (guardedRobustPath p estimate eps M C stay h0 s0 t)

/-- Every actual one-step quality gain is nonnegative. -/
theorem guardedRobustGain_nonneg (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) (t : ℕ) :
    0 ≤ guardedRobustGain p estimate eps M C stay h0 s0 t :=
  sub_nonneg.mpr
    (guardedRobustPath_quality_step p estimate eps M C stay h0 s0 hid h_bounds t)

/-- Finite actual gains telescope exactly to final minus initial quality. -/
theorem guardedRobustGain_sum_range (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (T : ℕ) :
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t =
      p.value (guardedRobustPath p estimate eps M C stay h0 s0 T) -
        p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) := by
  simpa only [guardedRobustGain] using
    Finset.sum_range_sub
      (fun t => p.value (guardedRobustPath p estimate eps M C stay h0 s0 t)) T

/-- The supplied upper quality bound bounds every finite actual gain sum. -/
theorem guardedRobustGain_sum_range_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) (T : ℕ) :
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t ≤
      B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) := by
  calc
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t =
        p.value (guardedRobustPath p estimate eps M C stay h0 s0 T) -
          p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
      guardedRobustGain_sum_range p estimate eps M C stay h0 s0 T
    _ ≤ B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
      sub_le_sub_right (hB T) _

/-- Nonnegative actual gains with uniformly bounded partial sums are summable. -/
theorem guardedRobustGain_summable (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Summable (guardedRobustGain p estimate eps M C stay h0 s0) :=
  summable_of_sum_range_le
    (guardedRobustGain_nonneg p estimate eps M C stay h0 s0 hid h_bounds)
    (guardedRobustGain_sum_range_le p estimate eps M C stay h0 s0 B hB)

/-- Infinite-time summability forces actual one-step quality gains to zero;
this does not imply stationary states or parameters. -/
theorem guardedRobustGain_tendsto_zero (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Tendsto (guardedRobustGain p estimate eps M C stay h0 s0) atTop (𝓝 0) :=
  (guardedRobustGain_summable p estimate eps M C stay h0 s0 hid h_bounds
    B hB).tendsto_atTop_zero

/-- Total actual quality gain is at most the supplied bound minus initial
quality; no convergence of the underlying state or parameters is claimed. -/
theorem guardedRobustGain_tsum_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    ∑' t, guardedRobustGain p estimate eps M C stay h0 s0 t ≤
      B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
  (guardedRobustGain_summable p estimate eps M C stay h0 s0 hid h_bounds
    B hB).tsum_le_of_sum_range_le
      (guardedRobustGain_sum_range_le p estimate eps M C stay h0 s0 B hB)

end Hagi.Unified.GuardedRobustTrajectory

set_option relaxedAutoImplicit false

/-!
# Discrete progress for fixed-bias two-action guarded paths

For a two-action controller whose stay action is the identity, the estimate
`value - 1 / 2` and guard radius `1 / 2` give a deterministic discrete
alternative: every actual one-step value gain is zero or at least one. The
number of positive gains is therefore bounded by any supplied upper value
bound minus the initial value. A gap below one freezes the path; in general,
gains tending to zero imply eventual constancy and convergence to the eventual
state.

These are finite-model quality statements only. They do not assert a global
optimum, estimator calibration, physical resource bounds, or convergence for
an arbitrary finite action family.
-/

namespace Hagi.Unified.FixedBiasBinaryProgress

open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.GuardedRobustTrajectory
open Filter Topology

variable {S : Type*}

/-- The true controller value with the constant pessimistic bias `-1 / 2`. -/
noncomputable def fixedBiasBinaryValueEstimate (p : ControllerProblem (Fin 2) S)
    (s : S) : ℝ :=
  p.value s - 1 / 2

/-- The absolute pointwise error of the fixed-bias estimate is exactly `1/2`. -/
theorem fixedBiasBinaryValueEstimate_error (p : ControllerProblem (Fin 2) S)
    (s : S) :
    |p.value s - fixedBiasBinaryValueEstimate p s| = 1 / 2 := by
  unfold fixedBiasBinaryValueEstimate
  norm_num

/-- The parent guarded robust path with the same fixed-bias estimate and
constant radius at every step. No new path recursion is introduced. -/
noncomputable def fixedBiasBinaryPath (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) : ℕ → S :=
  guardedRobustPath p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0

@[simp] theorem fixedBiasBinaryPath_zero (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) :
    fixedBiasBinaryPath p M C h0 s0 0 = s0 := by
  simp only [fixedBiasBinaryPath, guardedRobustPath_zero]

@[simp] theorem fixedBiasBinaryPath_succ (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
        (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2) h0 := by
  simp only [fixedBiasBinaryPath, guardedRobustPath_succ]

/-- The parent actual value gain for the fixed-bias path. -/
noncomputable def fixedBiasBinaryGain (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) : ℝ :=
  guardedRobustGain p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0 t

/-- The fixed-bias gain is the actual successor value minus current value. -/
theorem fixedBiasBinaryGain_eq_sub (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) :
    fixedBiasBinaryGain p M C h0 s0 t =
      p.value (fixedBiasBinaryPath p M C h0 s0 (t + 1)) -
        p.value (fixedBiasBinaryPath p M C h0 s0 t) := rfl

private theorem fixedBiasBinaryPath_error_bound
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (t : ℕ) (a : Fin 2) (_ha : a ∈ feasible p M C) :
    |p.value (p.step a (fixedBiasBinaryPath p M C h0 s0 t)) -
      fixedBiasBinaryValueEstimate p
        (p.step a (fixedBiasBinaryPath p M C h0 s0 t))| ≤ 1 / 2 :=
  le_of_eq (fixedBiasBinaryValueEstimate_error p _)

private theorem fixedBiasBinaryPath_quality_monotone
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) :
    Monotone (fun t => p.value (fixedBiasBinaryPath p M C h0 s0 t)) := by
  exact guardedRobustPath_quality_monotone p
    (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
    M C (0 : Fin 2) h0 s0 hid
    (fixedBiasBinaryPath_error_bound p M C h0 s0)

private theorem fixedBiasBinaryGain_nonneg
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    0 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
  exact guardedRobustGain_nonneg p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0 hid
    (fixedBiasBinaryPath_error_bound p M C h0 s0) t

private theorem twoActionUpgrade_spec
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (estimate : S → ℝ) (eps : ℝ) (M C : ℕ) (s : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (heps : 0 < eps)
    (hup : estimatedUpgrade p estimate eps s M C (0 : Fin 2)) :
    (1 : Fin 2) ∈ feasible p M C ∧
      estimate (p.step (0 : Fin 2) s) + 2 * eps ≤
        estimate (p.step (1 : Fin 2) s) := by
  obtain ⟨a, ha, hmargin⟩ := hup
  have ha_one : a = 1 := by
    have hval : a.val = 0 ∨ a.val = 1 := by omega
    rcases hval with hzero | hone
    · exfalso
      have ha_zero : a = 0 := Fin.ext hzero
      subst a
      rw [hid] at hmargin
      linarith only [hmargin, heps]
    · exact Fin.ext hone
  subst a
  exact ⟨ha, hmargin⟩

/-- In two actions, an active fixed-bias upgrade is precisely an action-one
witness with actual value gain at least one over the identity stay state. -/
private theorem fixedBiasBinaryUpgrade_spec
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (s : S) (hid : ∀ s, p.step (0 : Fin 2) s = s)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2)) :
    (1 : Fin 2) ∈ feasible p M C ∧
      1 ≤ p.value (p.step (1 : Fin 2) s) - p.value s := by
  obtain ⟨ha, hmargin⟩ := twoActionUpgrade_spec p
    (fixedBiasBinaryValueEstimate p) (1 / 2) M C s hid (by norm_num) hup
  refine ⟨ha, ?_⟩
  rw [hid] at hmargin
  unfold fixedBiasBinaryValueEstimate at hmargin
  linarith

private theorem twoActionNext_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (estimate : S → ℝ) (eps : ℝ) (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (heps : 0 < eps)
    (hup : estimatedUpgrade p estimate eps s M C (0 : Fin 2)) :
    guardedRobustNext p estimate eps s M C (0 : Fin 2) h0 =
      p.step (1 : Fin 2) s := by
  have hup := hup
  obtain ⟨ha, hmargin⟩ := twoActionUpgrade_spec
    p estimate eps M C s hid heps hup
  have hm0 := (mem_feasible_withEstimatedValue p estimate).mpr h0
  have hm1 := (mem_feasible_withEstimatedValue p estimate).mpr ha
  have hvalue : estimate (p.step (0 : Fin 2) s) <
      estimate (p.step (1 : Fin 2) s) := by
    linarith only [hmargin, heps]
  have hselection := selection_eq_one_of_value_lt
    (withEstimatedValue p estimate) s M C hm0 hm1 hvalue
  unfold guardedRobustNext
  rw [ite_eq_left hup]
  change p.step (selection (withEstimatedValue p estimate)
    s M C (0 : Fin 2) hm0) s = p.step (1 : Fin 2) s
  rw [hselection]

private theorem fixedBiasBinaryNext_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2)) :
    guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2) h0 = p.step (1 : Fin 2) s := by
  exact twoActionNext_eq_step_one_of_upgrade p
    (fixedBiasBinaryValueEstimate p) (1 / 2) M C h0 s hid
    (by norm_num) hup

private theorem fixedBiasBinaryPath_succ_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      p.step (1 : Fin 2) (fixedBiasBinaryPath p M C h0 s0 t) := by
  rw [fixedBiasBinaryPath_succ]
  exact fixedBiasBinaryNext_eq_step_one_of_upgrade p M C h0 _ hid hup

private theorem fixedBiasBinaryPath_succ_eq_current_of_no_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : ¬ estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      fixedBiasBinaryPath p M C h0 s0 t := by
  rw [fixedBiasBinaryPath_succ,
    guardedRobustNext_of_no_upgrade p (fixedBiasBinaryValueEstimate p)
      (1 / 2) _ M C (0 : Fin 2) h0 hup, hid]

/-- Every actual fixed-bias path gain is either zero or at least one. -/
theorem fixedBiasBinaryGain_eq_zero_or_one_le
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    fixedBiasBinaryGain p M C h0 s0 t = 0 ∨
      1 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
  classical
  by_cases hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)
  · right
    rw [fixedBiasBinaryGain_eq_sub,
      fixedBiasBinaryPath_succ_eq_step_one_of_upgrade p M C h0 s0 hid t hup]
    exact (fixedBiasBinaryUpgrade_spec p M C _ hid hup).2
  · left
    rw [fixedBiasBinaryGain_eq_sub,
      fixedBiasBinaryPath_succ_eq_current_of_no_upgrade p M C h0 s0 hid t hup,
      sub_self]

private theorem fixedBiasBinaryNext_eq_current_of_gain_lt_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hlt : fixedBiasBinaryGain p M C h0 s0 t < 1) :
    guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2) h0 =
        fixedBiasBinaryPath p M C h0 s0 t := by
  classical
  by_cases hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)
  · exfalso
    have hone : 1 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
      rw [fixedBiasBinaryGain_eq_sub,
        fixedBiasBinaryPath_succ_eq_step_one_of_upgrade p M C h0 s0 hid t hup]
      exact (fixedBiasBinaryUpgrade_spec p M C _ hid hup).2
    linarith only [hlt, hone]
  · rw [guardedRobustNext_of_no_upgrade p (fixedBiasBinaryValueEstimate p)
      (1 / 2) _ M C (0 : Fin 2) h0 hup, hid]

/-- Number of outer steps with strictly positive actual value gain. This is
not a count of estimator evaluations, operations, or wall-clock work. -/
noncomputable def fixedBiasBinaryProgressCount
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (T : ℕ) : ℕ := by
  classical
  exact {t ∈ Finset.range T | 0 < fixedBiasBinaryGain p M C h0 s0 t}.card

/-- The real-valued positive-gain count is at most the supplied upper value
bound minus the actual initial path value. -/
theorem fixedBiasBinaryProgressCount_le
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) (T : ℕ) :
    (fixedBiasBinaryProgressCount p M C h0 s0 T : ℝ) ≤
      B - p.value (fixedBiasBinaryPath p M C h0 s0 0) := by
  classical
  have hcard : fixedBiasBinaryProgressCount p M C h0 s0 T =
      ∑ t ∈ Finset.range T,
        if 0 < fixedBiasBinaryGain p M C h0 s0 t then 1 else 0 := by
    unfold fixedBiasBinaryProgressCount
    exact (Finset.sum_boole
      (fun t => 0 < fixedBiasBinaryGain p M C h0 s0 t) (Finset.range T)).symm
  rw [hcard, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ t ∈ Finset.range T,
        if 0 < fixedBiasBinaryGain p M C h0 s0 t then (1 : ℝ) else 0) ≤
        ∑ t ∈ Finset.range T, fixedBiasBinaryGain p M C h0 s0 t := by
      apply Finset.sum_le_sum
      intro t _ht
      by_cases hpos : 0 < fixedBiasBinaryGain p M C h0 s0 t
      · rw [ite_eq_left hpos]
        rcases fixedBiasBinaryGain_eq_zero_or_one_le p M C h0 s0 hid t with
          hzero | hone
        · linarith only [hpos, hzero]
        · exact hone
      · rw [ite_eq_right hpos]
        exact fixedBiasBinaryGain_nonneg p M C h0 s0 hid t
    _ = p.value (fixedBiasBinaryPath p M C h0 s0 T) -
        p.value (fixedBiasBinaryPath p M C h0 s0 0) := by
      exact guardedRobustGain_sum_range p
        (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
        M C (0 : Fin 2) h0 s0 T
    _ ≤ B - p.value (fixedBiasBinaryPath p M C h0 s0 0) :=
      sub_le_sub_right (hB T) _

/-- If the supplied value gap is below one, every step stays at the initial
state. This uses monotonicity and the discrete gain floor, not resource caps. -/
theorem fixedBiasBinaryPath_forall_eq_of_gap_lt_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B)
    (hsmall : B - p.value (fixedBiasBinaryPath p M C h0 s0 0) < 1) :
    ∀ t, fixedBiasBinaryPath p M C h0 s0 t = s0 := by
  intro t
  induction t with
  | zero => exact fixedBiasBinaryPath_zero p M C h0 s0
  | succ t ih =>
      have hinitial : p.value (fixedBiasBinaryPath p M C h0 s0 0) ≤
          p.value (fixedBiasBinaryPath p M C h0 s0 t) :=
        fixedBiasBinaryPath_quality_monotone p M C h0 s0 hid (Nat.zero_le t)
      have hgain : fixedBiasBinaryGain p M C h0 s0 t < 1 := by
        rw [fixedBiasBinaryGain_eq_sub]
        have hnext := hB (t + 1)
        linarith only [hinitial, hnext, hsmall]
      rw [fixedBiasBinaryPath_succ,
        fixedBiasBinaryNext_eq_current_of_gain_lt_one p M C h0 s0 hid t hgain]
      exact ih

/-- Actual gains tending to zero force every sufficiently late successor to
stay at its current state. -/
theorem fixedBiasBinaryPath_eventually_succ_eq
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N,
      fixedBiasBinaryPath p M C h0 s0 (t + 1) =
        fixedBiasBinaryPath p M C h0 s0 t := by
  have htendsto : Tendsto (fixedBiasBinaryGain p M C h0 s0) atTop (𝓝 0) := by
    exact guardedRobustGain_tendsto_zero p
      (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
      M C (0 : Fin 2) h0 s0 hid (fixedBiasBinaryPath_error_bound p M C h0 s0)
      B hB
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htendsto) 1 zero_lt_one
  have hgain : ∀ t ≥ N, fixedBiasBinaryGain p M C h0 s0 t < 1 := by
    intro t ht
    have hdist := hN t ht
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (fixedBiasBinaryGain_nonneg p M C h0 s0 hid t)] at hdist
    exact hdist
  refine ⟨N, fun t ht => ?_⟩
  rw [fixedBiasBinaryPath_succ]
  exact fixedBiasBinaryNext_eq_current_of_gain_lt_one p M C h0 s0 hid t
    (hgain t ht)

/-- A fixed-bias guarded path is eventually equal to one of its own states. -/
theorem fixedBiasBinaryPath_eventually_eq
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N, fixedBiasBinaryPath p M C h0 s0 t =
      fixedBiasBinaryPath p M C h0 s0 N := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_succ_eq p M C h0 s0 hid B hB
  refine ⟨N, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [hN n hmn]
      exact ih

/-- With any topology on the state space, the path converges to its eventual
state. No identification with a global optimum is made. -/
theorem fixedBiasBinaryPath_tendsto_eventual_value [TopologicalSpace S]
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, Tendsto (fixedBiasBinaryPath p M C h0 s0) atTop
      (𝓝 (fixedBiasBinaryPath p M C h0 s0 N)) := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_eq p M C h0 s0 hid B hB
  refine ⟨N, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with t ht
  exact (hN t ht).symm

/-- A positive objective scaling changes only the model value. -/
@[reducible] noncomputable def inverseScaledController (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) : ControllerProblem (Fin 2) S where
  value := fun s => δ⁻¹ * p.value s
  step := p.step
  memory := p.memory
  operations := p.operations
  safe := p.safe

private theorem feasible_inverseScaledController_iff
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe] (δ : ℝ)
    (M C : ℕ) (a : Fin 2) :
    a ∈ feasible p M C ↔ a ∈ feasible (inverseScaledController p δ) M C := by
  simp only [mem_feasible]

/-- The estimate whose absolute error is exactly `δ/2` for positive `δ`. -/
noncomputable def scaledBiasBinaryValueEstimate
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (s : S) : ℝ :=
  p.value s - δ / 2

/-- The estimate has the claimed deterministic error for positive `δ`. -/
theorem scaledBiasBinaryValueEstimate_error
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ) (s : S) :
    |p.value s - scaledBiasBinaryValueEstimate p δ s| = δ / 2 := by
  have hrhs : p.value s - scaledBiasBinaryValueEstimate p δ s = δ / 2 := by
    unfold scaledBiasBinaryValueEstimate
    ring
  rw [hrhs, abs_of_pos (by positivity)]

/-- The original guarded path with scaled threshold `δ`. -/
noncomputable def scaledBiasBinaryPath (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) [DecidablePred p.safe] (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) : ℕ → S :=
  guardedRobustPath p (fun _ => scaledBiasBinaryValueEstimate p δ)
    (fun _ => δ / 2) M C (0 : Fin 2) h0 s0

@[simp] theorem scaledBiasBinaryPath_zero (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) [DecidablePred p.safe] (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) :
    scaledBiasBinaryPath p δ M C h0 s0 0 = s0 := rfl

@[simp] theorem scaledBiasBinaryPath_succ (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) [DecidablePred p.safe] (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (t : ℕ) :
    scaledBiasBinaryPath p δ M C h0 s0 (t + 1) =
      guardedRobustNext p (scaledBiasBinaryValueEstimate p δ) (δ / 2)
        (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2) h0 := rfl

/-- The scaled guarded path is monotone in actual model quality. -/
theorem scaledBiasBinaryPath_quality_step
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤
      p.value (scaledBiasBinaryPath p δ M C h0 s0 (t + 1)) := by
  exact guardedRobustPath_quality_step p
    (fun _ => scaledBiasBinaryValueEstimate p δ) (fun _ => δ / 2)
    M C (0 : Fin 2) h0 s0 hid
    (fun i a _ha => le_of_eq (scaledBiasBinaryValueEstimate_error p δ hδ _)) t

/-- Exact gain of the original objective on the scaled-threshold path. -/
noncomputable def scaledBiasBinaryGain (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) [DecidablePred p.safe] (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (t : ℕ) : ℝ :=
  guardedRobustGain p (fun _ => scaledBiasBinaryValueEstimate p δ)
    (fun _ => δ / 2) M C (0 : Fin 2) h0 s0 t

@[simp] theorem scaledBiasBinaryGain_eq_sub (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) [DecidablePred p.safe] (M C : ℕ)
    (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (t : ℕ) :
    scaledBiasBinaryGain p δ M C h0 s0 t =
      p.value (scaledBiasBinaryPath p δ M C h0 s0 (t + 1)) -
        p.value (scaledBiasBinaryPath p δ M C h0 s0 t) := rfl

private lemma scaled_bias_gap_iff (x y δ : ℝ) (hδ : 0 < δ) :
    x + δ / 2 ≤ y - δ / 2 ↔ δ⁻¹ * x + 1 / 2 ≤ δ⁻¹ * y - 1 / 2 := by
  have hin : 0 < δ⁻¹ := inv_pos.mpr hδ
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hin.le
    have hl : δ⁻¹ * (x + δ / 2) = δ⁻¹ * x + 1 / 2 := by field_simp
    have hr : δ⁻¹ * (y - δ / 2) = δ⁻¹ * y - 1 / 2 := by field_simp
    rwa [hl, hr] at hmul
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hδ.le
    have hl : δ * (δ⁻¹ * x + 1 / 2) = x + δ / 2 := by field_simp
    have hr : δ * (δ⁻¹ * y - 1 / 2) = y - δ / 2 := by field_simp
    rwa [hl, hr] at hmul

private theorem estimatedUpgrade_scaled_iff (p : ControllerProblem (Fin 2) S)
    (δ : ℝ) (hδ : 0 < δ) [DecidablePred p.safe] (M C : ℕ) (s : S) :
    estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ) (δ / 2)
        s M C (0 : Fin 2) ↔
      estimatedUpgrade (inverseScaledController p δ)
        (fixedBiasBinaryValueEstimate (inverseScaledController p δ)) (1 / 2)
        s M C (0 : Fin 2) := by
  constructor
  · rintro ⟨a, ha, hmargin⟩
    refine ⟨a, ha, ?_⟩
    have hsc : δ⁻¹ * p.value (p.step (0 : Fin 2) s) + 1 / 2 ≤
        δ⁻¹ * p.value (p.step a s) - 1 / 2 :=
      (scaled_bias_gap_iff _ _ _ hδ).mp (by
        unfold scaledBiasBinaryValueEstimate at hmargin
        linarith only [hmargin])
    unfold fixedBiasBinaryValueEstimate inverseScaledController
    convert hsc using 1; ring
  · rintro ⟨a, ha, hmargin⟩
    refine ⟨a, ha, ?_⟩
    have hnorm : δ⁻¹ * p.value (p.step (0 : Fin 2) s) + 1 / 2 ≤
        δ⁻¹ * p.value (p.step a s) - 1 / 2 := by
      unfold fixedBiasBinaryValueEstimate inverseScaledController at hmargin
      convert hmargin using 1; ring
    have hsc := (scaled_bias_gap_iff (p.value (p.step (0 : Fin 2) s))
      (p.value (p.step a s)) δ hδ).mpr hnorm
    unfold scaledBiasBinaryValueEstimate at ⊢
    linarith only [hsc]

private theorem fixedScaledBiasPath_eq_scaledBiasPath
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 t =
      scaledBiasBinaryPath p δ M C h0 s0 t := by
  have hid_scaled : ∀ s, (inverseScaledController p δ).step (0 : Fin 2) s = s :=
    hid
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [fixedBiasBinaryPath_succ, scaledBiasBinaryPath_succ, ih]
      by_cases hup : estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ)
          (δ / 2) (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2)
      · have hup_scaled := (estimatedUpgrade_scaled_iff p δ hδ M C
          (scaledBiasBinaryPath p δ M C h0 s0 t)).mp hup
        rw [twoActionNext_eq_step_one_of_upgrade
          (inverseScaledController p δ)
          (fixedBiasBinaryValueEstimate (inverseScaledController p δ))
          (1 / 2) M C ((feasible_inverseScaledController_iff p δ M C
            (0 : Fin 2)).mp h0) _ hid_scaled (by norm_num) hup_scaled,
          twoActionNext_eq_step_one_of_upgrade p
          (scaledBiasBinaryValueEstimate p δ) (δ / 2) M C h0 _ hid
          (by positivity) hup]
      · have hup_scaled : ¬ estimatedUpgrade (inverseScaledController p δ)
            (fixedBiasBinaryValueEstimate (inverseScaledController p δ))
            (1 / 2) (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2) := by
          rw [← estimatedUpgrade_scaled_iff p δ hδ M C]
          exact hup
        rw [guardedRobustNext_of_no_upgrade p
          (scaledBiasBinaryValueEstimate p δ) (δ / 2) _ M C
          (0 : Fin 2) h0 hup,
          guardedRobustNext_of_no_upgrade (inverseScaledController p δ)
          (fixedBiasBinaryValueEstimate (inverseScaledController p δ))
          (1 / 2) _ M C (0 : Fin 2) ((feasible_inverseScaledController_iff p δ
            M C (0 : Fin 2)).mp h0) hup_scaled, hid]

private lemma fixedScaledBiasGain_eq_scaledBiasGain
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    fixedBiasBinaryGain (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 t =
      δ⁻¹ * scaledBiasBinaryGain p δ M C h0 s0 t := by
  rw [fixedBiasBinaryGain_eq_sub, scaledBiasBinaryGain_eq_sub]
  change δ⁻¹ * p.value (fixedBiasBinaryPath (inverseScaledController p δ)
      M C ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0)
      s0 (t + 1)) -
    δ⁻¹ * p.value (fixedBiasBinaryPath (inverseScaledController p δ)
      M C ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0)
      s0 t) = _
  rw [fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid (t + 1),
    fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t]
  ring

/-- A unit gain after normalization is exactly a gain `δ` before it. -/
theorem scaledBiasBinaryGain_eq_zero_or_delta_le
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    scaledBiasBinaryGain p δ M C h0 s0 t = 0 ∨
      δ ≤ scaledBiasBinaryGain p δ M C h0 s0 t := by
  have hid_scaled : ∀ s, (inverseScaledController p δ).step (0 : Fin 2) s = s :=
    hid
  rcases fixedBiasBinaryGain_eq_zero_or_one_le
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0)
      s0 hid_scaled t with hzero | hone
  · left
    have hg := hzero
    rw [fixedScaledBiasGain_eq_scaledBiasGain p δ hδ M C h0 s0 hid t] at hg
    exact (mul_eq_zero.mp hg).resolve_left (inv_ne_zero (ne_of_gt hδ))
  · right
    rw [fixedScaledBiasGain_eq_scaledBiasGain p δ hδ M C h0 s0 hid t] at hone
    have hmul := mul_le_mul_of_nonneg_left hone hδ.le
    calc
      δ = δ * 1 := by ring
      _ ≤ δ * (δ⁻¹ * scaledBiasBinaryGain p δ M C h0 s0 t) := hmul
      _ = scaledBiasBinaryGain p δ M C h0 s0 t := by field_simp

/-- Strictly positive original gains of the scaled-threshold path. -/
noncomputable def scaledBiasBinaryProgressCount
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (T : ℕ) : ℕ := by
  classical
  exact {t ∈ Finset.range T | 0 < scaledBiasBinaryGain p δ M C h0 s0 t}.card

@[simp] theorem scaledBiasBinaryProgressCount_succ
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (T : ℕ) :
    scaledBiasBinaryProgressCount p δ M C h0 s0 (T + 1) =
      scaledBiasBinaryProgressCount p δ M C h0 s0 T +
        if 0 < scaledBiasBinaryGain p δ M C h0 s0 T then 1 else 0 := by
  have hcard : ∀ N : ℕ,
      scaledBiasBinaryProgressCount p δ M C h0 s0 N =
        ∑ t ∈ Finset.range N,
          if 0 < scaledBiasBinaryGain p δ M C h0 s0 t then 1 else 0 := by
    intro N
    unfold scaledBiasBinaryProgressCount
    exact (Finset.sum_boole
      (fun t => 0 < scaledBiasBinaryGain p δ M C h0 s0 t) (Finset.range N)).symm
  rw [hcard (T + 1), hcard T, Finset.sum_range_succ]

private theorem fixedScaledBiasCount_eq_scaledCount
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (T : ℕ) :
    fixedBiasBinaryProgressCount (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 T =
      scaledBiasBinaryProgressCount p δ M C h0 s0 T := by
  classical
  unfold fixedBiasBinaryProgressCount scaledBiasBinaryProgressCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t _ht
  rw [fixedScaledBiasGain_eq_scaledBiasGain p δ hδ M C h0 s0 hid t]
  exact mul_pos_iff_of_pos_left (inv_pos.mpr hδ)

private theorem fixedScaledBiasPath_upper
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) :
    ∀ t, (inverseScaledController p δ).value
      (fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 t) ≤
        δ⁻¹ * B := by
  intro t
  change δ⁻¹ * p.value
    (fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 t) ≤ δ⁻¹ * B
  rw [fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t]
  exact mul_le_mul_of_nonneg_left (hB t) (inv_nonneg.mpr hδ.le)

/-- The unit-floor count bound normalized to a positive threshold `δ`. -/
theorem scaledBiasBinaryProgressCount_mul_le
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) (T : ℕ) :
    δ * (scaledBiasBinaryProgressCount p δ M C h0 s0 T : ℝ) ≤
      B - p.value (scaledBiasBinaryPath p δ M C h0 s0 0) := by
  rw [← fixedScaledBiasCount_eq_scaledCount p δ hδ M C h0 s0 hid T]
  have hcount := fixedBiasBinaryProgressCount_le
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 hid (δ⁻¹ * B)
    (fixedScaledBiasPath_upper p δ hδ M C h0 s0 hid B hB) T
  have hmul := mul_le_mul_of_nonneg_left hcount hδ.le
  calc
    δ * (fixedBiasBinaryProgressCount (inverseScaledController p δ)
        M C ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0)
        s0 T : ℝ) ≤ δ * (δ⁻¹ * B -
          (inverseScaledController p δ).value
            (fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 0)) := hmul
    _ = B - p.value (scaledBiasBinaryPath p δ M C h0 s0 0) := by
      simp only [fixedBiasBinaryPath_zero, scaledBiasBinaryPath_zero,
        inverseScaledController]
      field_simp

/-- The corresponding division form of the finite count bound. -/
theorem scaledBiasBinaryProgressCount_le_div
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) (T : ℕ) :
    (scaledBiasBinaryProgressCount p δ M C h0 s0 T : ℝ) ≤
      (B - p.value (scaledBiasBinaryPath p δ M C h0 s0 0)) / δ := by
  apply (le_div_iff₀ hδ).mpr
  rw [mul_comm]
  exact scaledBiasBinaryProgressCount_mul_le p δ hδ M C h0 s0 hid B hB T

/-- A quality gap below `δ` freezes every guarded successor. -/
theorem scaledBiasBinaryPath_forall_eq_of_gap_lt_delta
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B)
    (hsmall : B - p.value (scaledBiasBinaryPath p δ M C h0 s0 0) < δ) :
    ∀ t, scaledBiasBinaryPath p δ M C h0 s0 t = s0 := by
  intro t
  rw [← fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t]
  apply fixedBiasBinaryPath_forall_eq_of_gap_lt_one
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 hid (δ⁻¹ * B)
    (fixedScaledBiasPath_upper p δ hδ M C h0 s0 hid B hB)
  change δ⁻¹ * B - δ⁻¹ * p.value
    (fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 0) < 1
  rw [fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid 0,
    scaledBiasBinaryPath_zero]
  calc
    δ⁻¹ * B - δ⁻¹ * p.value s0 = δ⁻¹ * (B - p.value s0) := by ring
    _ < δ⁻¹ * δ := mul_lt_mul_of_pos_left (by simpa using hsmall) (inv_pos.mpr hδ)
    _ = 1 := by field_simp

/-- Eventually each scaled-threshold successor keeps the full state. -/
theorem scaledBiasBinaryPath_eventually_succ_eq
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N, scaledBiasBinaryPath p δ M C h0 s0 (t + 1) =
      scaledBiasBinaryPath p δ M C h0 s0 t := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_succ_eq
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 hid (δ⁻¹ * B)
    (fixedScaledBiasPath_upper p δ hδ M C h0 s0 hid B hB)
  refine ⟨N, fun t ht => ?_⟩
  rw [← fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid (t + 1),
    ← fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t]
  exact hN t ht

/-- The scaled-threshold path is eventually equal to a finite own state. -/
theorem scaledBiasBinaryPath_eventually_eq
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N, scaledBiasBinaryPath p δ M C h0 s0 t =
      scaledBiasBinaryPath p δ M C h0 s0 N := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_eq
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 hid (δ⁻¹ * B)
    (fixedScaledBiasPath_upper p δ hδ M C h0 s0 hid B hB)
  refine ⟨N, fun t ht => ?_⟩
  rw [← fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t,
    ← fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid N]
  exact hN t ht

/-- Under any supplied state topology, convergence follows from constancy. -/
theorem scaledBiasBinaryPath_tendsto_eventual_value [TopologicalSpace S]
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (scaledBiasBinaryPath p δ M C h0 s0 t) ≤ B) :
    ∃ N, Tendsto (scaledBiasBinaryPath p δ M C h0 s0) atTop
      (𝓝 (scaledBiasBinaryPath p δ M C h0 s0 N)) := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_tendsto_eventual_value
    (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 hid (δ⁻¹ * B)
    (fixedScaledBiasPath_upper p δ hδ M C h0 s0 hid B hB)
  refine ⟨N, ?_⟩
  have hfun : fixedBiasBinaryPath (inverseScaledController p δ) M C
      ((feasible_inverseScaledController_iff p δ M C (0 : Fin 2)).mp h0) s0 =
      scaledBiasBinaryPath p δ M C h0 s0 := by
    funext t
    exact fixedScaledBiasPath_eq_scaledBiasPath p δ hδ M C h0 s0 hid t
  rw [hfun] at hN
  exact hN

/-- An upgrade under the positive threshold selects action one. -/
theorem scaledBiasBinaryPath_succ_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ) (δ / 2)
      (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2)) :
    scaledBiasBinaryPath p δ M C h0 s0 (t + 1) =
      p.step (1 : Fin 2) (scaledBiasBinaryPath p δ M C h0 s0 t) := by
  rw [scaledBiasBinaryPath_succ]
  exact twoActionNext_eq_step_one_of_upgrade p
    (scaledBiasBinaryValueEstimate p δ) (δ / 2) M C h0 _ hid
    (by positivity) hup

/-- A threshold upgrade also makes the actual path gain strictly positive. -/
theorem scaledBiasBinaryGain_pos_of_upgrade
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ) (δ / 2)
      (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2)) :
    0 < scaledBiasBinaryGain p δ M C h0 s0 t := by
  have hup := hup
  obtain ⟨_, hmargin⟩ := twoActionUpgrade_spec p
    (scaledBiasBinaryValueEstimate p δ) (δ / 2) M C _ hid (by positivity) hup
  rw [scaledBiasBinaryGain_eq_sub,
    scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p δ hδ M C h0 s0 hid t hup]
  unfold scaledBiasBinaryValueEstimate at hmargin
  rw [hid] at hmargin
  linarith only [hmargin, hδ]

/-- A strictly positive gain forces the action-one step. -/
theorem scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
    (p : ControllerProblem (Fin 2) S) (δ : ℝ) (hδ : 0 < δ)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hpos : 0 < scaledBiasBinaryGain p δ M C h0 s0 t) :
    scaledBiasBinaryPath p δ M C h0 s0 (t + 1) =
      p.step (1 : Fin 2) (scaledBiasBinaryPath p δ M C h0 s0 t) := by
  classical
  by_cases hup : estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ)
      (δ / 2) (scaledBiasBinaryPath p δ M C h0 s0 t) M C (0 : Fin 2)
  · exact scaledBiasBinaryPath_succ_eq_step_one_of_upgrade
      p δ hδ M C h0 s0 hid t hup
  · exfalso
    rw [scaledBiasBinaryGain_eq_sub] at hpos
    rw [scaledBiasBinaryPath_succ,
      guardedRobustNext_of_no_upgrade p (scaledBiasBinaryValueEstimate p δ)
        (δ / 2) _ M C (0 : Fin 2) h0 hup, hid, sub_self] at hpos
    exact lt_irrefl 0 hpos

/-- Threshold one recovers exactly the old fixed-bias path. -/
theorem fixedBiasBinaryPath_eq_scaled_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) :
    fixedBiasBinaryPath p M C h0 s0 =
      scaledBiasBinaryPath p 1 M C h0 s0 := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [fixedBiasBinaryPath_succ, scaledBiasBinaryPath_succ, ih]
      have hval : fixedBiasBinaryValueEstimate p =
          scaledBiasBinaryValueEstimate p 1 := by
        funext s
        unfold fixedBiasBinaryValueEstimate scaledBiasBinaryValueEstimate
        norm_num
      rw [hval]

/-- Threshold one recovers the old gain without altering its definition. -/
theorem fixedBiasBinaryGain_eq_scaled_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (t : ℕ) :
    fixedBiasBinaryGain p M C h0 s0 t =
      scaledBiasBinaryGain p 1 M C h0 s0 t := by
  rw [fixedBiasBinaryGain_eq_sub, scaledBiasBinaryGain_eq_sub]
  simp only [fixedBiasBinaryPath_eq_scaled_one]

/-- Threshold one preserves the exact strict-positive filter and count. -/
theorem fixedBiasBinaryProgressCount_eq_scaled_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (T : ℕ) :
    fixedBiasBinaryProgressCount p M C h0 s0 T =
      scaledBiasBinaryProgressCount p 1 M C h0 s0 T := by
  classical
  unfold fixedBiasBinaryProgressCount scaledBiasBinaryProgressCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t _ht
  rw [fixedBiasBinaryGain_eq_sub, scaledBiasBinaryGain_eq_sub]
  simp only [fixedBiasBinaryPath_eq_scaled_one]

/-- A shared finite positive-gain telescope for the declared `TrainState`
FLOP field. The caller must prove the actual action-one increment; nothing
about estimator evaluations, wall-clock time or physical work is inferred. -/
theorem scaledBiasBinaryTrainPath_flops_eq
    {n a r c k : ℕ} (p : ControllerProblem (Fin 2) (Hagi.State.TrainState n a r c k))
    (δ : ℝ) (hδ : 0 < δ) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : Hagi.State.TrainState n a r c k)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (opCost : ℝ)
    (hpositive : ∀ t, 0 < scaledBiasBinaryGain p δ M C h0 s0 t →
      (p.step (1 : Fin 2) (scaledBiasBinaryPath p δ M C h0 s0 t)).res.flops =
        (scaledBiasBinaryPath p δ M C h0 s0 t).res.flops + opCost)
    (T : ℕ) :
    (scaledBiasBinaryPath p δ M C h0 s0 T).res.flops =
      s0.res.flops + opCost * (scaledBiasBinaryProgressCount p δ M C h0 s0 T : ℝ) := by
  classical
  induction T with
  | zero => simp only [scaledBiasBinaryPath_zero, scaledBiasBinaryProgressCount,
      Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      mul_zero, add_zero]
  | succ T ih =>
      by_cases hpos : 0 < scaledBiasBinaryGain p δ M C h0 s0 T
      · have hsucc := scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
          p δ hδ M C h0 s0 hid T hpos
        rw [hsucc, hpositive T hpos, ih, scaledBiasBinaryProgressCount_succ,
          Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_eq_left hpos]
        ring
      · have hzero : scaledBiasBinaryGain p δ M C h0 s0 T = 0 := by
          rcases scaledBiasBinaryGain_eq_zero_or_delta_le
            p δ hδ M C h0 s0 hid T with hzero | hpositive
          · exact hzero
          · exact False.elim (hpos (lt_of_lt_of_le hδ hpositive))
        have hnoup : ¬ estimatedUpgrade p (scaledBiasBinaryValueEstimate p δ)
            (δ / 2) (scaledBiasBinaryPath p δ M C h0 s0 T) M C (0 : Fin 2) := by
          intro hup
          exact hpos (scaledBiasBinaryGain_pos_of_upgrade p δ hδ M C h0 s0 hid T hup)
        rw [scaledBiasBinaryPath_succ,
          guardedRobustNext_of_no_upgrade p (scaledBiasBinaryValueEstimate p δ)
            (δ / 2) _ M C (0 : Fin 2) h0 hnoup, hid,
          ih, scaledBiasBinaryProgressCount_succ,
          Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          ite_eq_right hpos, add_zero]

/-- If actual values are nonpositive and the supplied cost is nonnegative,
the shared positive-gain telescope is bounded by `(opCost / δ) * -value(s0)`.
This is an accounting bound for accepted transitions only. -/
theorem scaledBiasBinaryTrainPath_flops_le_of_value_nonpos
    {n a r c k : ℕ} (p : ControllerProblem (Fin 2) (Hagi.State.TrainState n a r c k))
    (δ : ℝ) (hδ : 0 < δ) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : Hagi.State.TrainState n a r c k)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (opCost : ℝ) (hcost : 0 ≤ opCost)
    (hvalue : ∀ s, p.value s ≤ 0)
    (hpositive : ∀ t, 0 < scaledBiasBinaryGain p δ M C h0 s0 t →
      (p.step (1 : Fin 2) (scaledBiasBinaryPath p δ M C h0 s0 t)).res.flops =
        (scaledBiasBinaryPath p δ M C h0 s0 t).res.flops + opCost)
    (T : ℕ) :
    (scaledBiasBinaryPath p δ M C h0 s0 T).res.flops ≤
      s0.res.flops + (opCost / δ) * (-p.value s0) := by
  rw [scaledBiasBinaryTrainPath_flops_eq p δ hδ M C h0 s0 hid opCost hpositive T]
  have hcount := scaledBiasBinaryProgressCount_le_div p δ hδ M C h0 s0 hid 0
    (fun t => hvalue (scaledBiasBinaryPath p δ M C h0 s0 t)) T
  rw [scaledBiasBinaryPath_zero] at hcount
  calc
    s0.res.flops + opCost * (scaledBiasBinaryProgressCount p δ M C h0 s0 T : ℝ) ≤
        s0.res.flops + opCost * ((0 - p.value s0) / δ) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hcount hcost) _
    _ = s0.res.flops + (opCost / δ) * (-p.value s0) := by ring

end Hagi.Unified.FixedBiasBinaryProgress
set_option linter.style.header false

