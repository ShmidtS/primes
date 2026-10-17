/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.MemoryCapacity
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
