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
    (eps : ℝ) (good : A → A → Prop)
    (tasks : Finset A) (hsep : SepSeparated eps good tasks)
    (encode : A → Q) (decode : Q → A)
    (hcover : ∀ x ∈ tasks, ∃ w : A, good (decode (encode w)) x) :
    tasks.card ≤ Fintype.card Q := by
  -- every task is answered by SOME compressed state
  have hcover' : ∀ x ∈ tasks, ∃ q : Q, good (decode q) x := by
    intro x hx
    obtain ⟨w, hw⟩ := hcover x hx
    exact ⟨encode w, hw⟩
  exact separated_needs_capacity eps good tasks hsep decode hcover'

end Hagi.Information
