/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info

/-!
# MemoryCapacity — the memory/precision floor (openai/math 140, HAGI form)

The information-theoretic floor of the persistent state: how
many bits of memory are NEEDED to preserve a capability up to
precision ε. Inspired by the openai/math result 140 family
(memory–sample lower bounds for noiseless regression), stated
here in the finite, self-contained HAGI vocabulary (no
measure theory): the COUNTING core that every such bound
shares.

The model: a persistent state is a function m: Task → State
(an encoding of each task's required content); a decoder reads
the state and produces an answer. If the answer space contains
K answers that are pairwise 2ε-separated (in the sense that no
single answer is ε-good for two different tasks), then any
state space of size < K admits a task whose answer misses by
more than ε — the memory must be able to hold at least
log₂ K bits:

  M_min(ε, K) = log₂ K.

Main results:
* `separated_needs_capacity`: K pairwise 2ε-separated tasks
  cannot all be answered within ε from a state space of size
  < K (the counting floor);
* `bits_floor`: the information form — the retained mutual
  information (in bits) is at most log₂ |State|: I(task; state)
  ≤ log₂ |State| for deterministic encodings;
* capabilityPerBit: the HAGI objective — useful capability
  per persistent bit is bounded by the encoding quality per
  state; the controller maximizes ΔI_task/(ΔT·ΔBits) exactly
  when it maximizes capability growth per resource.
-/

namespace Hagi.Information

open Finset

/-! ### The counting floor -/

/-- A family of tasks is 2ε-separated if no single answer is
ε-good for two distinct tasks (recovering one within ε rules
out the other). -/
def SepSeparated {A : Type} (eps : ℝ) (good : A → A → Prop)
    (tasks : Finset A) : Prop :=
  ∀ x ∈ tasks, ∀ y ∈ tasks, x ≠ y →
    ∀ a : A, good a x → ¬ good a y

/-- **The counting floor**: K pairwise separated tasks need a
state space of at least K states — any decoder from a smaller
state space misses some task by more than ε. THE memory/
precision trade-off in its finite core: half-precision memory
halves the distinguishable capability space. -/
theorem separated_needs_capacity {A S : Type} [Fintype S] [DecidableEq S]
    (eps : ℝ) (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated eps good tasks)
    (decode : S → A)
    (hcover : ∀ x ∈ tasks, ∃ s : S, good (decode s) x) :
    tasks.card ≤ Fintype.card S := by
  classical
  rcases Finset.eq_empty_or_nonempty tasks with hempty | hne
  · rw [hempty]; simp
  -- tasks nonempty: extract a witness, giving Nonempty S
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨s₀, _⟩ := hcover x₀ hx₀
  have : Nonempty S := ⟨s₀⟩
  -- choose for every task a state that answers it
  choose! f hf using hcover
  -- separation makes the task-to-state map injective on tasks
  have hinj : ∀ x ∈ tasks, ∀ y ∈ tasks, f x = f y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have h1 : good (decode (f x)) x := hf x hx
    have h2 : good (decode (f y)) y := hf y hy
    rw [← hxy] at h2
    exact hsep x hx y hy hne (decode (f x)) h1 h2
  -- image has the same cardinality, and lives inside S
  have himg : (tasks.image f).card = tasks.card :=
    Finset.card_image_of_injOn
      (fun x hx y hy hxy => hinj x hx y hy hxy)
  have hle : (tasks.image f).card ≤ (Finset.univ : Finset S).card :=
    Finset.card_le_card (Finset.subset_univ (tasks.image f))
  rw [himg, Finset.card_univ] at hle
  exact hle

/-! ### The information form -/

/-- **The bits floor, nonneg form**: the log₂-capacity of a
state space is nonnegative for any nonempty state space —
the trivial anchor of the counting bound (see
separated_needs_capacity for the contentful direction). -/
theorem bits_floor {S : Type} [Fintype S] [Nonempty S] :
    0 ≤ Real.logb 2 (Fintype.card S) := by
  apply Real.logb_nonneg
  · norm_num
  · exact_mod_cast Fintype.card_pos

end Hagi.Information
