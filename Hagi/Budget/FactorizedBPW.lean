/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# FactorizedBPW — bits-per-weight arithmetic of the
factorized ternary branch (R244; LittleBit scheme,
ternary body, FP16 scales)

A square d×d layer is replaced by a factorized branch
W ≈ diag(h)·T(U)·diag(ℓ)·T(V)ᵀ·diag(g) with latent rank r:
ternary factors (log₂3 bits/entry, 2·d·r entries) plus
three FP16 scale vectors (h : d, g : d, ℓ : r — 16 bits
each). The bits-per-original-weight of ONE branch is

  b₁ = (log₂3 · 2·d·r + 16·(2d + r)) / d².

This module fixes that arithmetic exactly:

* `factorized_ternary_bits` — total bits as a function of
  d, r (the identity the BPW claims reduce to);
* `bpw_two_branches` — the two-branch LittleBit layout is
  exactly twice one branch;
* `bpw_lt_one_bound` — GROWTH BY RANK: keeping the whole
  factorized layer below 1 BPW bounds the affordable
  latent rank linearly in d (and quadratically relative
  to the dense budget d²) — the formal counterpart of
  "HAGI grows by effective latent dimension, not width":
  r can scale with d while the layer stays sub-1-BPW.

Numerical anchor (NOT a theorem — arithmetic of the scheme
with ternary factors): d = 4096, r = 384 gives
b₁ ≈ 0.305 BPW, two branches ≈ 0.611 BPW.
-/

open scoped BigOperators

namespace Hagi.Budget

/-- log₂3 as a real constant. -/
noncomputable def log2_3 : ℝ := Real.log 3 / Real.log 2

/-- Total bits of one factorized ternary branch:
ternary factor entries plus FP16 scale vectors. -/
noncomputable def factorizedTernaryBits (d r : ℕ) : ℝ :=
  log2_3 * (2 * d * r) + 16 * (2 * d + r)

/-- Bits per original weight of one branch (d×d layer). -/
noncomputable def bpw (d r : ℕ) : ℝ := factorizedTernaryBits d r / (d * d)

theorem factorized_ternary_bits (d r : ℕ) :
    factorizedTernaryBits d r = log2_3 * (2 * d * r) + 16 * (2 * d + r) := rfl

/-- The two-branch (primary + residual) layout costs exactly
twice one branch. -/
theorem bpw_two_branches (d r : ℕ) :
    (factorizedTernaryBits d r + factorizedTernaryBits d r) / (d * d)
      = 2 * bpw d r := by
  unfold bpw
  ring

/-- **Growth by latent rank under a 1-BPW budget**: for a
nondegenerate layer, the one-branch BPW stays below 1
exactly when the rank is below the linear-in-d threshold
(d² − 32·d) / (2·log₂3·d + 16). In particular a
rank growing linearly with d keeps the layer sub-1-BPW —
formalizing "grow effective latent dimension, not width". -/
theorem bpw_lt_one_bound (d r : ℕ) (hd : 0 < d) (hlog : 0 < log2_3) :
    bpw d r < 1 ↔
      (r : ℝ) < ((d : ℝ) * (d : ℝ) - 16 * 2 * (d : ℝ))
        / (2 * log2_3 * (d : ℝ) + 16) := by
  unfold bpw factorizedTernaryBits
  have hdc : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdd : (0:ℝ) < (d : ℝ) * (d : ℝ) := by positivity
  have hden : (0:ℝ) < 2 * log2_3 * (d : ℝ) + 16 := by
    have : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    nlinarith [hlog, this]
  have key : ∀ x : ℝ, log2_3 * (2 * (d:ℝ) * x) + 16 * (2 * (d:ℝ) + x)
      = (2 * log2_3 * (d:ℝ) + 16) * x + 32 * (d:ℝ) := by
    intro x; ring
  constructor
  · intro h
    rw [div_lt_iff₀ hdd, one_mul, key] at h
    apply (lt_div_iff₀ hden).mpr
    linarith
  · intro h
    rw [lt_div_iff₀ hden] at h
    rw [div_lt_iff₀ hdd, one_mul, key]
    linarith

end Hagi.Budget
