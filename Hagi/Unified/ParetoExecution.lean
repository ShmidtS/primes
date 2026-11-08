/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.SelfDevelopment
import Hagi.Model.StageSemantics
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
