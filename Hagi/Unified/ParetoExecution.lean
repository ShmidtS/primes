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
