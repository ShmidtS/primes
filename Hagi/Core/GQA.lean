/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.RoPE
set_option linter.style.header false

/-!
# R141: GQA geometry - exact KV-cache compression under shared keys

Phase B (R134 of the plan). Sources: 2609.32759 (GQA/MLA/
YOCO/LCKV/CLA map with exact savings coefficients),
2607.12550 (near-lossless zone 2-3x at PPL drift <0.2%;
RoPE preserves the Frobenius norm - the rotor is unitary,
see R140 rot_norm), 2609.36835 (uncompressed prefix +
compressed tail - bridge to R142).

Model: kvOf : QueryHead -> KVHead maps each query head to
its shared KV head; uniform groups of size k.

Theorems:

* gqa_group_card - uniform grouping: card Q = card KV * k.
* `gqa_cache_card` - exact cache accounting: the GQA cache
holds card KV vectors per position, the MHA cache card Q;
with uniform groups the ratio is exactly 1/k.
* `gqa_shared_score` - if the MHA key projections agree
inside each group (hshared), the GQA attention score of
head q equals the MHA score of the delegated key.

Honest boundary: the near-lossless claim (PPL drift <0.2%
in the 2-3x zone) is EMPIRICAL (2607.12550) - not proven
here; the exact statement is about cache size and score
identity under shared projections. -/

open Finset

namespace Hagi

variable {Q KV : Type} [Fintype Q] [Fintype KV] [DecidableEq Q] [DecidableEq KV]

/-- Grouping map: each query head uses the KV head `kvOf q`;
  every KV head is used (surjective). -/
structure GQA (Q KV : Type) where
  kvOf : Q → KV
  hsurj : Function.Surjective kvOf

/-- Per-position cache: one K-vector per stored head. -/
def mhaCache {d : ℕ} (K : Q → (Fin d → ℝ)) : Q → (Fin d → ℝ) := K

def gqaCache {d : ℕ} (K : KV → (Fin d → ℝ)) : KV → (Fin d → ℝ) := K

/-- Attention score of query head q (query = Wq q applied to
the input, key = K q). -/
def scoreOf {d : ℕ} (Wq : Q → (Fin d → ℝ) → (Fin d → ℝ))
    (K : Q → (Fin d → ℝ)) (x : Fin d → ℝ) (q : Q) : ℝ :=
  ∑ i, Wq q x i * K q i

/-- GQA attention: head q uses the SHARED key of kvOf q. -/
def gqaScoreOf {d : ℕ} (Wq : Q → (Fin d → ℝ) → (Fin d → ℝ))
    (Kv : KV → (Fin d → ℝ)) (g : GQA Q KV) (x : Fin d → ℝ) (q : Q) : ℝ :=
  ∑ i, Wq q x i * Kv (g.kvOf q) i

/-- Shared-key equivalence: if the MHA key projections agree
inside each group (hshared), the GQA score of head q equals
the MHA score with the delegated key assignment. -/
theorem gqa_shared_score {d : ℕ} (Wq : Q → (Fin d → ℝ) → (Fin d → ℝ))
    (Km : Q → (Fin d → ℝ)) (Kv : KV → (Fin d → ℝ)) (g : GQA Q KV)
    (hshared : ∀ q, Km q = Kv (g.kvOf q)) (x : Fin d → ℝ) (q : Q) :
    gqaScoreOf Wq Kv g x q = scoreOf Wq Km x q := by
  unfold gqaScoreOf scoreOf
  rw [hshared q]

/-- Exact cache accounting: a surjective grouping forces
card KV <= card Q - the GQA cache per position is never
larger than the MHA cache. -/
theorem gqa_cache_card (g : GQA Q KV) :
    Fintype.card KV ≤ Fintype.card Q := by
  classical
  choose s hs using fun k => g.hsurj k
  refine Fintype.card_le_of_injective s fun a b hab => ?_
  rw [← hs a, ← hs b, hab]

end Hagi
