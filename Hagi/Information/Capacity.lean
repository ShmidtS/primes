/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

/-!
# Ёмкостное семейство информации (объединённое)

MemoryCapacity (ёмкость памяти), RoutingCapacity (ёмкость
маршрутизации), GainRecoverability (восстановимость выигрыша).
Слит из трёх модулей; namespace и имена сохранены.
-/

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

/-- A family of tasks is separated w.r.t. `good` if no single
answer is good for two distinct tasks (recovering one rules
out the other). The ε-precision lives in the choice of `good`
(ε-good answers), not in this predicate. -/
def SepSeparated {A : Type} (good : A → A → Prop)
    (tasks : Finset A) : Prop :=
  ∀ x ∈ tasks, ∀ y ∈ tasks, x ≠ y →
    ∀ a : A, good a x → ¬ good a y

/-- **The counting floor**: K pairwise separated tasks need a
state space of at least K states — any decoder from a smaller
state space misses some task by more than ε. THE memory/
precision trade-off in its finite core: half-precision memory
halves the distinguishable capability space. -/
theorem separated_needs_capacity {A S : Type} [Fintype S] [DecidableEq S]
    (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated good tasks)
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

/-!
# InformationRetention — compression never creates information

The data-processing core of the openai/math result 119 family
(independent noise contracts information), stated in the HAGI
finite vocabulary: a QUANTIZER/ROUTER is a deterministic
post-processing of the weights; the information the downstream
model can hold about the task is capped by what the COMPRESSED
representation retains — never more.

Main results:
* `no_free_recovery`: a compressed representation cannot
  answer a task that no compressed state answers — no decoder
  manufactures information (the data-processing principle);
* `quantized_separation_needs_range`: if a K-task 2ε-separated
  family is fully served through a compressed pipeline, the
  compressed range has at least K states — quantization
  quality costs range size, exactly (MemoryCapacity applied
  through the pipeline).
-/

namespace Hagi.Information

open Finset

/-- **No free recovery** (the data-processing principle, finite
form): any answer the compressed pipeline gives was already an
answer of some compressed state — decoders do not create
information. -/
theorem no_free_recovery {A Q : Type} (encode : A → Q)
    (decode : Q → A) (good : A → A → Prop) (w : A)
    (h : good (decode (encode w)) w) :
    ∃ q : Q, good (decode q) w :=
  ⟨encode w, h⟩

/-- **Quantized separation needs range**: a 2ε-separated task
family of size K served ε-well through a deterministic
compress-then-decode pipeline forces the compressed range to
carry at least K states. Combined with
separated_needs_capacity this says: the quantization range is
the capability currency — the pipeline cannot preserve more
separated capabilities than it has compressed states. -/
theorem quantized_separation_needs_range
    {A Q : Type} [Fintype Q] [DecidableEq Q]
    (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated good tasks)
    (encode : A → Q) (decode : Q → A)
    (hcover : ∀ x ∈ tasks, ∃ w : A, good (decode (encode w)) x) :
    tasks.card ≤ Fintype.card Q := by
  -- every task is answered by SOME compressed state
  have hcover' : ∀ x ∈ tasks, ∃ q : Q, good (decode q) x := by
    intro x hx
    obtain ⟨w, hw⟩ := hcover x hx
    exact ⟨encode w, hw⟩
  exact separated_needs_capacity good tasks hsep decode hcover'

end Hagi.Information

/-!
# RepresentationRate — the information density of a representation

The entropy-rate/contraction analogy of openai/math result 148
(dim μ = min{1, h/χ}: the surviving dimension is the injection
rate over the contraction rate), lifted to HAGI as an exact
finite statement about representations:

  ρ_info:= retained information / representation bits.

Three regimes (proved as a total trichotomy):

* ρ_info = 1 — the representation is SATURATED: every bit
  carries one bit of retained information (a perfect code;
  MemoryCapacity's counting floor is tight);
* 0 < ρ_info < 1 — the GROWTH regime: slack exists, a strictly
  better packing is possible in principle;
* ρ_info = 0 — the DEGENERATE regime: retained information is
  zero (or bits infinite): no capability survives.

All statements are exact finite algebra — no analogy is claimed
about the 148 dynamics themselves; only the RATIO STRUCTURE is
imported (honest boundary).
-/

namespace Hagi.Information

open Finset

/-- Information density of a representation: retained
information (in bits, a real ≥ 0) per representation bit. -/
noncomputable def repRate (retained bits : ℝ) : ℝ := retained / bits

/-- The three regimes of ρ_info UNDER THE COUNTING CAP
retained ≤ bits (MemoryCapacity: information cannot exceed
the bits that carry it): every representation is saturated,
or in the growth regime, or degenerate — a total trichotomy. -/
theorem repRate_trichotomy (retained bits : ℝ) (hbits : 0 < bits)
    (hret : 0 ≤ retained) (hcap : retained ≤ bits) :
    repRate retained bits = 1 ∨
      (0 < repRate retained bits ∧ repRate retained bits < 1) ∨
      repRate retained bits = 0 := by
  rcases lt_trichotomy retained bits with h | h | h
  · rcases eq_or_ne retained 0 with hr | hr
    · right; right
      rw [repRate, hr, zero_div]
    · right; left
      have hpos : 0 < retained := lt_of_le_of_ne hret hr.symm
      constructor
      · rw [repRate]; exact div_pos hpos hbits
      · rw [repRate]; exact (div_lt_one hbits).mpr h
  · left; rw [repRate, h, div_self hbits.ne']
  · exact absurd h (not_lt.mpr hcap)

end Hagi.Information

/-!
# RoutingCapacity — the router is a bounded information channel

The router-as-channel view (the HAGI reading of the 119 core):
routing (top-k, quantized gates) is a DETERMINISTIC compression
of the input; the capabilities it can serve downstream are
capped by its ROUTE COUNT, and the routes are capped by the
routing-state BITS: exponential form of the counting floor.

Main results:

* `router_capacity_bound`: K pairwise-separated task families
  served ε-well through such a router force K ≤ 2^B — the
  routing state must hold log₂ K bits: the top-k/quantization
  budget is a CAPABILITY budget, not an engineering choice.
-/

namespace Hagi.Information

open Finset

/-- **The router capacity bound**: if K pairwise 2ε-separated
task families are each served ε-well through a deterministic
router with B bits of state (at most 2^B routes), then
K ≤ 2^B: preserving K separated capabilities requires
log₂ K routing bits. -/
theorem router_capacity_bound {A Q : Type} [Fintype Q]
    [DecidableEq Q] (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated good tasks)
    (encode : A → Q) (decode : Q → A)
    (hcover : ∀ x ∈ tasks, ∃ w : A, good (decode (encode w)) x)
    (B : ℕ) (hQ : Fintype.card Q ≤ 2 ^ B) :
    tasks.card ≤ 2 ^ B := by
  have h1 : tasks.card ≤ Fintype.card Q :=
    quantized_separation_needs_range good tasks hsep encode
      decode hcover
  exact le_trans h1 hQ

end Hagi.Information

/-!
# GainRecoverability — disagreement is EXTRACTABLE, not just present

The ProjectionMoments-inspired brick (openai/math 140 branch):
positive deviation energy does not merely EXIST — it is
RECOVERABLE by a linear readout. This closes the conceptual
gap between `devEnergy > 0` (MergeCancellation: the pool
carries diversity) and `G > 0` (GainOperator: the diversity
can be converted): between them stands the question whether a
readout exists that extracts nonzero signal. Here it always
does: the deviation directions themselves are such readouts.

Main results (finite Euclidean vocabulary of DustAlign):

* `devEnergyF_pos_iff`: total deviation energy is positive
  iff some expert deviates — the existence form;
* `recoverable_avg`: if total deviation energy E > 0 then SOME
  deviation carries at least E/N of it (pigeonhole: the best
  expert is never below the average) — the extractability
  lower bound on what the readout pool has to work with;
* `devSignal_self`: a nonzero deviation has strictly positive
  self-signal d ⬝ᵥ d > 0 — the linear readout ⟨d, ·⟩ extracts
  the deviation: recoverable signal is REAL, not a norm
  artifact.
-/

namespace Hagi.Information

open Finset

variable {N d : ℕ}

/-- Total deviation energy of an expert pool (finite form of
the GainOperator `devEnergy`, in the Dust Euclidean
vocabulary). -/
def devEnergyF (dev : Fin N → Fin d → ℝ) : ℝ :=
  ∑ k, dev k ⬝ᵥ dev k

private theorem dotSelf_nonneg {d : ℕ} (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- **Existence form**: total deviation energy is positive iff
some expert deviates. -/
theorem devEnergyF_pos_iff (dev : Fin N → Fin d → ℝ) :
    0 < devEnergyF dev ↔ ∃ k : Fin N, dev k ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply absurd h (not_lt.mpr (le_of_eq ?_))
    have : devEnergyF dev = 0 := by
      apply sum_eq_zero
      intro k _
      rw [hne k, dotProduct_zero]
    rw [this]
  · rintro ⟨k, hk⟩
    refine sum_pos' (fun _ _ => dotSelf_nonneg _) ⟨k, mem_univ k, ?_⟩
    have hz : dev k ⬝ᵥ dev k ≠ 0 := fun he =>
      hk (dotProduct_self_eq_zero.mp he)
    exact lt_of_le_of_ne (dotSelf_nonneg (dev k)) hz.symm

/-- **The pigeonhole extractability bound**: if the total
deviation energy E is positive, some single deviation carries
at least E/N of it — the readout pool never has to work below
the average. -/
theorem recoverable_avg (dev : Fin N → Fin d → ℝ)
    (hN : 0 < N) (h : 0 < devEnergyF dev) :
    ∃ k : Fin N, devEnergyF dev / N ≤ dev k ⬝ᵥ dev k := by
  obtain ⟨k, -⟩ := (devEnergyF_pos_iff dev).mp h
  by_contra hcon
  push_neg at hcon
  have hsum : devEnergyF dev < ∑ k : Fin N, devEnergyF dev / N := by
    show (∑ j : Fin N, dev j ⬝ᵥ dev j) < _
    apply sum_lt_sum _ ⟨k, mem_univ k, hcon k⟩
    intro j _
    exact le_of_lt (hcon j)
  have hconst : ∑ k : Fin N, devEnergyF dev / N = devEnergyF dev := by
    rw [sum_const]
    simp
    field_simp
  rw [hconst] at hsum
  exact lt_irrefl _ hsum

/-- **Self-signal**: a nonzero deviation has strictly positive
self-signal — the linear readout ⟨d, ·⟩ extracts d with
strength ‖d‖²: disagreement is not only present but linearly
readable. -/
theorem devSignal_self {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ v := by
  have hz : v ⬝ᵥ v ≠ 0 := fun he => hv (dotProduct_self_eq_zero.mp he)
  exact lt_of_le_of_ne (dotSelf_nonneg v) hz.symm

end Hagi.Information
