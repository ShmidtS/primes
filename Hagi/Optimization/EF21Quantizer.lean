/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Optimization.EF21Markov
import Hagi.Energy.Ternary

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Quantizer compressor instances for EF21 (A7 bridge 2)

The bridge from REAL quantizers (ternary rounding, TopK sparsifier)
to the EF21 Markov contract `IsContractive`
(`Hagi/Optimization/EF21Markov.lean`, C231). Honest math:

* `topK` (fixed-support mask) IS `alpha = 0` contractive
  (`topK_contractive`): zeroing the tail never expands. It is NOT
  contractive for any `alpha in (0, 1]` (`topK_not_contractive_pos`):
  a vector supported entirely on the tail is fully lost.
* `qTernVec` — the vector lift of the ternary quantizer
  `s * roundTern (./s)`, the same formula as `Hagi.Runtime.qTern`
  (re-stated: the layer DAG lets `Optimization` import `Energy`
  but not `Runtime`) — IS `alpha = 0` contractive
  (`qTernVec_contractive_zero`, per-coordinate
  `|x - s*roundTern (x/s)| <= |x|`). It is NOT contractive for any
  `alpha in (0, 1]` (`qTernVec_not_contractive`): the half-step
  witness `u = s/2` rounds to `0`, keeping `|Q u - u| = |u|`.
  Relative contractivity `|Q u - u| <= c|u|` with `c < 1` is
  REFUTED for plain rounding — the EF21 literature resolves this
  with per-vector scaling, which is NOT modelled here (documented
  boundary).
* `IsInexactCompressor` — the additive-error contract
  `|C u - u|_2 <= (1-alpha)|u|_2 + eps` that quantizers actually
  satisfy: `inexact_of_contractive` embeds exact contractors
  (eps = 0), `ef21_update_norm_le_inexact` transfers it through the
  Markov update, `ef21_inexact_descent` derives one-step Lyapunov
  descent (alignment and norm defects derived from the inexact
  bound via Cauchy-Schwarz, then fed to `ef21_lyapunov_descent`).
* Instances: `topK_inexact`, `qTernVec_inexact` (alpha = 0,
  eps = 0), and the in-range half-step budget
  `qTernVec_error_inrange` (`|Q u - u|_2 <= sqrt(n)*s/2` under
  `|u i| <= 3s/2`). The saturation-tail form (no in-range
  assumption) is `ternary_split_le` in
  `Hagi/Runtime/TernaryExact.lean` (energy form); wiring it into
  this contract needs the Runtime layer and remains documented,
  not proven, here.
-/

namespace Hagi.Optimization.EF21Quantizer

open Finset Real

section TopK

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The fixed-support TopK compressor: keeps the coordinates in
the support `S` and zeroes the tail. (The adaptive argmax-TopK of
the literature selects `S` per vector; the alpha = 0 contractivity
proof below is support-agnostic, so the fixed-support form carries
it.) -/
def topK (S : Finset n) (u : n → ℝ) : n → ℝ :=
  fun i => if i ∈ S then u i else 0

/-- TopK is `alpha = 0` contractive: dropping tail coordinates
never expands — `|topK S u - u|_2 <= |u|_2` for every `u`. -/
theorem topK_contractive (S : Finset n) :
    EF21Markov.IsContractive (topK S) 0 := by
  intro u
  have h : ∀ i : n, (topK S u i - u i) ^ 2 ≤ u i ^ 2 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [topK, hi, ite_true]; ring_nf; positivity
    · have e : topK S u i - u i = -u i := by simp [topK, hi]
      rw [e, neg_sq]
  have h' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  rw [show (1 - (0:ℝ)) ^ 2 * ∑ i, u i ^ 2 = ∑ i, u i ^ 2 by norm_num]
  exact h'

/-- TopK is NOT contractive for any `alpha in (0, 1]` when the
support misses a coordinate: a vector supported on the tail is
fully lost, so `|Q u - u| = |u|` exactly. -/
theorem topK_not_contractive_pos (S : Finset n) (hne : S ≠ Finset.univ)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ¬EF21Markov.IsContractive (topK S) α := by
  intro h
  have hw := h (fun i => if i ∈ S then (0:ℝ) else 1)
  have hQ : topK S (fun i => if i ∈ S then (0:ℝ) else 1) = 0 := by
    funext i
    by_cases hi : i ∈ S
    · simp [topK, hi]
    · simp [topK, hi]
  simp only [hQ, Pi.zero_apply, zero_sub, neg_sq] at hw
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra hcon
    exact hne (Finset.eq_univ_of_forall fun j =>
      Classical.byContradiction fun hc => hcon ⟨j, hc⟩)
  have hpos : (0:ℝ) < ∑ j, (if j ∈ S then (0:ℝ) else 1) ^ 2 := by
    have hterm : (0:ℝ) < (if i ∈ S then (0:ℝ) else 1) ^ 2 := by
      have : ¬ i ∈ S := hi
      simp [this]
    have hle : (0:ℝ) ≤ ∑ j, (if j ∈ S then (0:ℝ) else 1) ^ 2 :=
      Finset.sum_nonneg (fun j _ => by
        by_cases hj : j ∈ S <;> simp [hj] <;> positivity)
    have hsing : (if i ∈ S then (0:ℝ) else 1) ^ 2
        ≤ ∑ j, (if j ∈ S then (0:ℝ) else 1) ^ 2 :=
      Finset.single_le_sum
        (f := fun j => (if j ∈ S then (0:ℝ) else 1) ^ 2)
        (fun j _ => by by_cases hj : j ∈ S <;> simp [hj] <;> positivity)
        (Finset.mem_univ i)
    simp only [hi, ite_false, one_pow] at hterm hsing
    linarith
  have h1 : (1 - α) ^ 2 < 1 := by nlinarith
  nlinarith

end TopK

section Ternary

variable {n : Type*} [Fintype n]

/-- The vector lift of the ternary quantizer: per coordinate the
nearest-grid rounding `s * roundTern (u i / s)` on `{-1, 0, +1}*s` —
the same formula as `Hagi.Runtime.qTern`, re-stated because the
layer DAG allows `Optimization` to see `Energy` but not `Runtime`. -/
noncomputable def qTernVec (s : ℝ) (u : n → ℝ) : n → ℝ :=
  fun i => s * ((roundTern (u i / s) : ℝ))

/-- Per-coordinate non-expansion of ternary rounding on the grid
`{-1, 0, +1}*s`: `|x - s*roundTern (x/s)| <= |x|` — the quantized
error never exceeds the magnitude (exact rounding to 0 on the
half-grid `|x| <= s/2`, and past `s/2` the grid point is nearer
than the origin). -/
theorem qTern_pointwise_le (s x : ℝ) (hs : 0 < s) :
    |x - s * ((roundTern (x / s) : ℝ))| ≤ |x| := by
  rw [← sq_le_sq]
  unfold roundTern
  by_cases h1 : 1 / 2 < x / s
  · rw [ite_eq_left h1]
    have hx : s / 2 < x := by
      rw [lt_div_iff₀ hs] at h1; linarith
    push_cast
    ring_nf
    nlinarith [hx]
  · by_cases h2 : x / s < -1 / 2
    · rw [ite_eq_right h1, ite_eq_left h2]
      have hx : x < -s / 2 := by
        rw [div_lt_iff₀ hs] at h2; linarith
      push_cast
      ring_nf
      nlinarith [hx]
    · rw [ite_eq_right h1, ite_eq_right h2]
      push_cast
      ring_nf
      exact le_refl _

/-- The ternary quantizer is `alpha = 0` contractive: per
coordinate the quantization error never exceeds the magnitude, so
`|Q u - u|_2 <= |u|_2` for every `u` (the degenerate endpoint of
the `IsContractive` contract, same convention as C231's
`contractive_zero`). -/
theorem qTernVec_contractive_zero (s : ℝ) (hs : 0 < s) :
    EF21Markov.IsContractive (qTernVec s : (n → ℝ) → (n → ℝ)) 0 := by
  intro u
  have h : ∀ i : n, (qTernVec s u i - u i) ^ 2 ≤ u i ^ 2 := by
    intro i
    have hle := qTern_pointwise_le s (u i) hs
    have e : qTernVec s u i - u i = -(u i - qTernVec s u i) := by ring
    rw [e, neg_sq]
    exact sq_le_sq.mpr hle
  have h' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  rw [show (1 - (0:ℝ)) ^ 2 * ∑ i, u i ^ 2 = ∑ i, u i ^ 2 by norm_num]
  exact h'

end Ternary

section Negative

/-- The half-grid tie rounds to zero: `roundTern (1/2) = 0`
(the tie is `1/2 < x`, strict). -/
private theorem roundTern_half : roundTern (1 / 2) = 0 := by
  unfold roundTern
  norm_num

variable {n : Type*} [Fintype n] [Nonempty n]

/-- Plain ternary rounding is NOT contractive for any
`alpha in (0, 1]` (nonempty carrier): the half-step witness
`u = s/2` (every coordinate) rounds to `0`, keeping
`|Q u - u| = |u|`. Relative contractivity `|Q u - u| <= c*|u|`
with `c < 1` is refuted for plain rounding. -/
theorem qTernVec_not_contractive (s : ℝ) (hs : 0 < s)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ¬EF21Markov.IsContractive (qTernVec s : (n → ℝ) → (n → ℝ)) α := by
  intro h
  have hw := h (fun _ => s / 2)
  have hQ : ∀ i : n, qTernVec s (fun _ => s / 2) i = 0 := by
    intro i
    have hbeta : qTernVec s (fun _ : n => s / 2) i
        = s * ((roundTern ((s / 2) / s) : ℝ)) := rfl
    have hd : (s / 2) / s = 1 / 2 := by field_simp
    rw [hbeta, hd, roundTern_half]
    push_cast
    ring
  simp only [hQ, zero_sub, neg_sq] at hw
  have hC : (0:ℝ) < ∑ i : n, (s / 2) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (0:ℝ) < (Fintype.card n : ℝ) := by
      have : 0 < Fintype.card n := Fintype.card_pos
      exact_mod_cast this
    exact mul_pos hcard (by positivity)
  have h1 : (1 - α) ^ 2 < 1 := by nlinarith
  nlinarith

end Negative

section Inexact

variable {n : Type*} [Fintype n]

/-- The additive-error compressor contract, inexact EF21 form:
`|C u - u|_2 <= (1-alpha)*|u|_2 + eps` for every `u` (squared,
explicit sums — the carrier discipline of `IsContractive`). -/
def IsInexactCompressor (C : (n → ℝ) → (n → ℝ)) (α ε : ℝ) : Prop :=
  ∀ u : n → ℝ, ∑ i, (C u i - u i) ^ 2
    ≤ ((1 - α) * Real.sqrt (∑ i, u i ^ 2) + ε) ^ 2

/-- Every exact contractor is an inexact compressor with `eps = 0`. -/
theorem inexact_of_contractive (C : (n → ℝ) → (n → ℝ)) (α : ℝ)
    (hC : EF21Markov.IsContractive C α) : IsInexactCompressor C α 0 := by
  intro u
  have h := hC u
  have hs : (0:ℝ) ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hrw : ((1 - α) * Real.sqrt (∑ i, u i ^ 2)) ^ 2
      = (1 - α) ^ 2 * ∑ i, u i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs]
  rw [add_zero, hrw]
  exact h

/-- Inexact transfer through the Markov update: with the additive
contract, `|v + C(g-v) - g|_2 <= (1-alpha)*|g-v|_2 + eps` — the
inexact twin of `ef21_update_norm_le`. -/
theorem ef21_update_norm_le_inexact (C : (n → ℝ) → (n → ℝ)) (α ε : ℝ)
    (hC : IsInexactCompressor C α ε) (v g : n → ℝ) :
    ∑ i, (v i + C (g - v) i - g i) ^ 2
      ≤ ((1 - α) * Real.sqrt (∑ i, (g i - v i) ^ 2) + ε) ^ 2 := by
  have h := hC (g - v)
  have hexp : ∀ i : n,
      (v i + C (g - v) i - g i) ^ 2 = (C (g - v) i - (g i - v i)) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i)]
  exact h

/-- One-step Lyapunov descent for an inexact compressor: with the
additive contract at the fresh gradient, an L-smoothness step
inequality for the compressed direction `C g`, `alpha in [0,1]`,
`eps >= 0`, `eta <= 1/(2L)`:

`f' <= f - (eta/2)(1-2*L*eta)*|g|_2^2
      + (eta/2)(1+2*L*eta)*((1-alpha)*|g|_2 + eps)^2`.

Alignment and norm defects are DERIVED from the inexact bound via
Cauchy-Schwarz (`Real.sum_mul_le_sqrt_mul_sqrt`) and fed to
`ef21_lyapunov_descent` — the constants stay exact. -/
theorem ef21_inexact_descent (C : (n → ℝ) → (n → ℝ)) (α ε L η f f' : ℝ)
    (g : n → ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hε : 0 ≤ ε)
    (hL : 0 < L) (hη : 0 < η) (hηL : η ≤ 1 / (2 * L))
    (hC : IsInexactCompressor C α ε)
    (hsm : f' ≤ f - η * ∑ i, g i * C g i + L * η ^ 2 / 2 * ∑ i, (C g i) ^ 2) :
    f' ≤ f - η / 2 * (1 - 2 * L * η) * ∑ i, g i ^ 2
      + η / 2 * (1 + 2 * L * η) * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε) ^ 2 := by
  have hsnn : (0:ℝ) ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsn : (0:ℝ) ≤ Real.sqrt (∑ i, g i ^ 2) := Real.sqrt_nonneg _
  have hαn : 0 ≤ 1 - α := by linarith
  have hδ : 0 ≤ (1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε := by positivity
  -- the residual r = C g − g and its norm bound
  have hr : ∑ i, (C g i - g i) ^ 2
      ≤ ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε) ^ 2 := hC g
  -- Cauchy–Schwarz: ⟪g, r⟫ ≤ ‖g‖·‖r‖
  have hcs : ∑ i, g i * (C g i - g i)
      ≤ Real.sqrt (∑ i, g i ^ 2) * Real.sqrt (∑ i, (C g i - g i) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => g i)
      (fun i => C g i - g i)
  have hcs' : ∑ i, (-g i) * (C g i - g i)
      ≤ Real.sqrt (∑ i, (-g i) ^ 2) * Real.sqrt (∑ i, (C g i - g i) ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -g i)
      (fun i => C g i - g i)
  have hcsn : ∑ i, (-g i) ^ 2 = ∑ i, g i ^ 2 := by
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hrdelta : Real.sqrt (∑ i, (C g i - g i) ^ 2)
      ≤ (1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε := by
    refine (Real.sqrt_le_sqrt hr).trans ?_
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ]
  have hstep : ∑ i, g i * (C g i - g i)
      ≤ Real.sqrt (∑ i, g i ^ 2)
        * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε) := by
    calc ∑ i, g i * (C g i - g i)
        ≤ Real.sqrt (∑ i, g i ^ 2)
            * Real.sqrt (∑ i, (C g i - g i) ^ 2) := hcs
      _ ≤ Real.sqrt (∑ i, g i ^ 2)
            * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε) :=
          mul_le_mul_of_nonneg_left hrdelta (Real.sqrt_nonneg _)
  -- alignment: ⟪g, C g⟫ ≥ s² − s·δ
  have hal : (Real.sqrt (∑ i, g i ^ 2)) ^ 2
      - Real.sqrt (∑ i, g i ^ 2) * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε)
      ≤ ∑ i, g i * C g i := by
    have hexp : ∑ i, g i * C g i
        = ∑ i, g i ^ 2 + ∑ i, g i * (C g i - g i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have ht2 : (Real.sqrt (∑ i, g i ^ 2)) ^ 2 = ∑ i, g i ^ 2 :=
      Real.sq_sqrt hsnn
    rw [hexp, ht2]
    rw [hcsn] at hcs'
    have hlow : -(Real.sqrt (∑ i, g i ^ 2)
          * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε))
        ≤ ∑ i, g i * (C g i - g i) := by
      have hnA : ∑ i, g i * (C g i - g i)
          = -∑ i, (-g i) * (C g i - g i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hge : -(Real.sqrt (∑ i, g i ^ 2)
            * ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε))
          ≤ -Real.sqrt (∑ i, g i ^ 2)
            * Real.sqrt (∑ i, (C g i - g i) ^ 2) := by
        nlinarith [hrdelta, hsn]
      rw [hnA]
      linarith
    linarith
  -- norm: ‖C g‖² ≤ (s + δ)²
  have hnorm : ∑ i, (C g i) ^ 2
      ≤ (Real.sqrt (∑ i, g i ^ 2)
          + ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε)) ^ 2 := by
    have hsplit : ∑ i, (C g i) ^ 2
        = ∑ i, g i ^ 2 + 2 * ∑ i, g i * (C g i - g i)
          + ∑ i, (C g i - g i) ^ 2 := by
      have hterm : ∀ i : n, (C g i) ^ 2
          = g i ^ 2 + 2 * (g i * (C g i - g i)) + (C g i - g i) ^ 2 :=
        fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i),
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    have ht2 : (Real.sqrt (∑ i, g i ^ 2)) ^ 2 = ∑ i, g i ^ 2 :=
      Real.sq_sqrt hsnn
    rw [hsplit]
    nlinarith [hstep, hr, ht2, hsn, hδ, mul_nonneg hsn hδ]
  exact EF21Markov.ef21_lyapunov_descent L η
    ((1 - α) * Real.sqrt (∑ i, g i ^ 2) + ε)
    (Real.sqrt (∑ i, g i ^ 2)) hL hη hηL f f' g (C g) hsm
    (Real.sq_sqrt hsnn) hsn hδ hal hnorm

end Inexact

section Instances

variable {n : Type*} [Fintype n]

/-- TopK embeds into the inexact contract with `ε = 0`. -/
theorem topK_inexact (S : Finset n) [DecidableEq n] :
    IsInexactCompressor (topK S) 0 0 :=
  inexact_of_contractive _ _ (topK_contractive S)

/-- The ternary quantizer embeds into the inexact contract with
`α = 0`, `ε = 0`: quantization error never exceeds the input norm. -/
theorem qTernVec_inexact (s : ℝ) (hs : 0 < s) :
    IsInexactCompressor (qTernVec s : (n → ℝ) → (n → ℝ)) 0 0 :=
  inexact_of_contractive _ _ (qTernVec_contractive_zero s hs)

/-- The in-range half-step budget, norm form: if every coordinate
satisfies `|u i| ≤ 3s/2`, then `‖Q u − u‖₂ ≤ √n · s / 2`. The
saturation-tail version (no in-range assumption) is
`ternary_split_le` in `Hagi/Runtime/TernaryExact.lean` (energy
form; wiring it here needs the Runtime layer). -/
theorem qTernVec_error_inrange (s : ℝ) (hs : 0 < s) (u : n → ℝ)
    (hall : ∀ i, |u i| ≤ 3 * s / 2) :
    Real.sqrt (∑ i, (qTernVec s u i - u i) ^ 2)
      ≤ Real.sqrt ((Fintype.card n : ℝ)) * s / 2 := by
  have hpt : ∀ i : n, (qTernVec s u i - u i) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    have hle := Hagi.Energy.roundTern_error_scaled s (u i) hs (hall i)
    have e2 : (qTernVec s u i - u i) ^ 2 = (u i - qTernVec s u i) ^ 2 := by ring
    have hq : qTernVec s u i = s * ((roundTern (u i / s) : ℝ)) := rfl
    rw [e2, hq]
    exact sq_le_sq.mpr (hle.trans (le_abs_self (s / 2)))
  have hsum : ∑ i, (qTernVec s u i - u i) ^ 2
      ≤ (Fintype.card n : ℝ) * (s / 2) ^ 2 := by
    calc ∑ i, (qTernVec s u i - u i) ^ 2
        ≤ ∑ i, (s / 2) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = (Fintype.card n : ℝ) * (s / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (0:ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast Nat.zero_le _
  refine (Real.sqrt_le_sqrt hsum).trans_eq ?_
  rw [Real.sqrt_mul hN, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith : (0:ℝ) < s / 2)]
  ring

end Instances


end Hagi.Optimization.EF21Quantizer
