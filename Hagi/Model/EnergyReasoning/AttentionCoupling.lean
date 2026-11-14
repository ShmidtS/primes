/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.SingleCellDescent
import Hagi.Model.EnergyReasoning.LatentEnergy
import Hagi.Model.EnergyReasoning.NumericalRobustness

set_option linter.style.header false

/-!
# Attention coupling: the latent-to-visible field link L_ij(z)

Track B3 (addendum A11 B-level): the REAL CRAM+Z link — the latent
state `z` couples into the VISIBLE pairwise energy through an
ATTENTION-weighted coupling kernel K(z), not just an additive bias
(the additive route is `LatentEnergy.visibleBiasWithZ`, the E3
two-phase seam — both exist, this file adds the multiplicative
attention link).

Construction: at FROZEN `z` (E3 two-phase protocol; `z` is
discrete/frozen — no differentiability-in-`z` is claimed), scores
`s : ι → ι → ℝ` induce softmax attention weights
`attentionWeights s i j = exp(s i j) / ∑_k exp(s i k)`, and the
coupling carries BOTH directed edges in every entry:

  `L_ij(a,b) = κ_ij · w_ij · f(a,b) + κ_ji · w_ji · f(b,a)`.

* `attentionWeights_nonneg` / `attentionWeights_le_one` /
  `attentionWeights_sum` — the softmax simplex facts (weights in
  `[0,1]`, row sums `1`; premise `[Nonempty ι]`: an empty index type
  has no softmax).
* `attention_coupling_symmetric` — (B3 MAIN) `L_ij(a,b) = L_ji(b,a)`
  BY CONSTRUCTION: the two directed contributions swap exactly. This
  is the A9 upper-triangle trick — both directed edges are built into
  every `L_ij`, so the kernel satisfies the C261 `hK` premise with NO
  symmetry hypothesis on `κ` or `w`. Fin 3 numeric anchor below uses
  a deliberately ASYMMETRIC `κ` to catch any index-role slip.
* `attention_coupling_bounded` — `|L_ij(a,b)| ≤ 2·κmax·fmax` when
  `0 ≤ κ ≤ κmax`, `w ∈ [0,1]`, `|f| ≤ fmax`. The constant `2` is
  TIGHT: two directed contributions, each `≤ κmax·fmax` (witness: `f`
  constant `±fmax` attains both simultaneously).
* `attentionK` — the kernel `K(z)` at frozen `z` (`w = α(·; z)`),
  `attention_K_symmetric` — the C261 premise verbatim.
* `frozen_z_field_with_attention` — the local field for `K(z)` is
  well-defined and the C261 machinery applies at frozen `z`: a
  local-field minimizer move does not increase
  `pairwiseEnergy B (attentionK κ (attentionWeights s) f)`.
* `attention_coupling_field_diff` — weight drift `|w1 − w2| ≤ δ`
  (premise) ⇒ local-field perturbation
  `≤ |S_i| · 2κmax·fmax·δ`, `S_i = univ \ {i}`.
* `latent_error_couples_field` — the composed latent-error contract
  (PREMISE-FORM, honest): `‖z − z*‖ ≤ η` plus a softmax-Lipschitz
  PREMISE `|w(z) − w(z*)| ≤ L_sm·η` (no such lemma is claimed for
  this carrier; `z` is frozen) bounds the field perturbation by
  `|S_i|·2κmax·fmax·L_sm·η`.
* `latent_attention_guarded_drop` — the C270 guard ABSORBS the latent
  error: with `ε := |S_i|·2κmax·fmax·L_sm·η`, a computed margin
  `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a STRICT drop of
  the TRUE energy `pairwiseEnergy B (attentionK κ w(z*) f)` — the
  2ε-guard recipe of `guarded_energy_delta` instantiated at the
  coupling bound.

## Honest boundaries (B3)

This is the STRUCTURAL CRAM+Z bridge only. Full Maze-Hard semantics —
support of `z*`, reachability, and JOINT `(z, y)` updates — remain
OPEN: joint updates are still forbidden by the E3 two-phase protocol
(a mid-descent z-move changes the kernel and voids the C261 delta
identity; no joint theorem exists or is claimed). The softmax
Lipschitz-in-z step is a premise, not a theorem.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy greedy_single_cell_nonincreasing)

/-! ## Softmax attention weights (z frozen in the scores s) -/
section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **`attentionWeights`** — the softmax attention weight
`α_ij = exp(s i j) / ∑_k exp(s i k)`; the latent state `z` is FROZEN
inside the scores `s` (premise-form scores: `z` discrete/frozen, no
differentiability-in-`z` claimed). -/
noncomputable def attentionWeights (s : ι → ι → ℝ) (i j : ι) : ℝ :=
  Real.exp (s i j) / ∑ k, Real.exp (s i k)

/-- **`attentionWeights_nonneg`** — softmax weights are nonnegative
(the denominator is a sum of positive exponentials). -/
theorem attentionWeights_nonneg (s : ι → ι → ℝ) (i j : ι) :
    0 ≤ attentionWeights s i j := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  exact div_nonneg (Real.exp_nonneg _) (le_of_lt hZ)

/-- **`attentionWeights_le_one`** — each softmax weight is at most
`1` (the numerator is one summand of the denominator). -/
theorem attentionWeights_le_one (s : ι → ι → ℝ) (i j : ι) :
    attentionWeights s i j ≤ 1 := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  have hle : Real.exp (s i j) ≤ ∑ k, Real.exp (s i k) :=
    Finset.single_le_sum (fun k _ => (Real.exp_pos (s i k)).le)
      (Finset.mem_univ j)
  unfold attentionWeights
  rw [div_le_iff₀ hZ]
  exact hle.trans_eq (one_mul _).symm

/-- **`attentionWeights_sum`** — the softmax row sums to `1`
(premise `[Nonempty ι]`: on an empty index type the denominator is
`0` and there is no softmax). -/
theorem attentionWeights_sum (s : ι → ι → ℝ) (i : ι) :
    ∑ j, attentionWeights s i j = 1 := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s i k) :=
    Finset.sum_pos' (fun k _ => (Real.exp_pos (s i k)).le)
      ⟨i, Finset.mem_univ i, Real.exp_pos (s i i)⟩
  unfold attentionWeights
  rw [← Finset.sum_div, div_self hZ.ne']

end Weights

/-! ## The attention coupling and its constructive symmetry -/
section Coupling

variable {ι : Type*}
variable {α : Type*}

/-- **`attentionCoupling`** — the attention coupling
`L_ij(a,b) = κ_ij·w_ij·f(a,b) + κ_ji·w_ji·f(b,a)`: BOTH directed
edges are built into every entry (the A9 upper-triangle
construction); `w` is the attention weight function (e.g.
`attentionWeights s` at frozen `z`). -/
noncomputable def attentionCoupling (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    (i j : ι) (a b : α) : ℝ :=
  κ i j * w i j * f a b + κ j i * w j i * f b a

/-- **`attention_coupling_symmetric`** — (B3 MAIN) symmetry BY
CONSTRUCTION: `L_ij(a,b) = L_ji(b,a)` — the two directed
contributions swap exactly (add_comm; NO symmetry premise on `κ` or
`w`). This is why the kernel `attentionK` satisfies the C261 `hK`
premise verbatim. -/
theorem attention_coupling_symmetric (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    (i j : ι) (a b : α) :
    attentionCoupling κ w f i j a b = attentionCoupling κ w f j i b a := by
  unfold attentionCoupling
  ring

/-- **`attention_coupling_bounded`** — with `0 ≤ κ ≤ κmax`, weights
in `[0,1]` (softmax facts) and `|f| ≤ fmax`:
`|L_ij(a,b)| ≤ 2·κmax·fmax`. The constant `2` is TIGHT — two
directed contributions, each `≤ κmax·fmax`. -/
theorem attention_coupling_bounded (κ w : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hw : ∀ i j, 0 ≤ w i j ∧ w i j ≤ 1)
    (hf : ∀ a b, |f a b| ≤ fmax) (i j : ι) (a b : α) :
    |attentionCoupling κ w f i j a b| ≤ 2 * κmax * fmax := by
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hterm : ∀ (p q : ι) (a b : α), |κ p q * w p q * f a b| ≤ κmax * fmax := by
    intro p q a b
    have h1 := (hκ p q).1
    have h2 := (hκ p q).2
    have h3 := (hw p q).1
    have h4 := (hw p q).2
    have habs : |κ p q * w p q * f a b| = κ p q * w p q * |f a b| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg h1 h3)]
    rw [habs]
    have hkw : κ p q * w p q ≤ κmax := by
      nlinarith [mul_le_mul_of_nonneg_left h4 h1]
    exact mul_le_mul hkw (hf a b) (abs_nonneg _) hκmax
  have h1 := hterm i j a b
  have h2 := hterm j i b a
  calc |attentionCoupling κ w f i j a b|
      = |κ i j * w i j * f a b + κ j i * w j i * f b a| := rfl
    _ ≤ |κ i j * w i j * f a b| + |κ j i * w j i * f b a| := abs_add_le _ _
    _ ≤ 2 * κmax * fmax := by linarith

end Coupling

/-! ## The kernel K(z) and the frozen-z visible field -/
section Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`attentionK`** — the attention coupling KERNEL `K(z)` at frozen
`z`: `K(z) i j a b = attentionCoupling κ w f i j a b` with `w = α(·;z)`
the frozen attention weights. -/
noncomputable def attentionK (κ w : ι → ι → ℝ) (f : α → α → ℝ) :
    ι → ι → α → α → ℝ :=
  fun i j a b => attentionCoupling κ w f i j a b

/-- **`attention_K_symmetric`** — `K(z)` satisfies the C261 `hK`
premise verbatim, for ANY `κ` and `w` (constructive symmetry). -/
theorem attention_K_symmetric (κ w : ι → ι → ℝ) (f : α → α → ℝ) :
    ∀ i j a b, attentionK κ w f i j a b = attentionK κ w f j i b a :=
  fun i j a b => attention_coupling_symmetric κ w f i j a b

/-- **`frozen_z_field_with_attention`** — (B3 MAIN, thin by design)
the local field for `K(z)` is well-defined and the C261 machinery
applies AT FROZEN `z`: moving cell `i` to a local-field minimizer of
`pairwiseEnergy B (attentionK κ (attentionWeights s) f)` does not
increase the energy. PREMISE-FORM for the descent — NO joint
`(z, y)` theorem exists or is claimed (E3 two-phase protocol: a
mid-descent z-move changes the kernel and voids the C261 delta
identity). -/
theorem frozen_z_field_with_attention (B : ι → α → ℝ)
    (κ : ι → ι → ℝ) (s : ι → ι → ℝ) (f : α → α → ℝ)
    (y : ι → α) (i : ι) (a : α)
    (hmin : ∀ a', localField B (attentionK κ (attentionWeights s) f) y i a
      ≤ localField B (attentionK κ (attentionWeights s) f) y i a') :
    pairwiseEnergy B (attentionK κ (attentionWeights s) f)
        (Function.update y i a)
      ≤ pairwiseEnergy B (attentionK κ (attentionWeights s) f) y :=
  greedy_single_cell_nonincreasing B _ (attention_K_symmetric _ _ _) y i a hmin

end Kernel

/-! ## Weight drift ⇒ local-field perturbation -/
section FieldDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`attention_coupling_field_diff`** — weight drift
`|w1 − w2| ≤ δ` (premise; the softmax-Lipschitz step is NOT claimed
here) perturbs the local field by at most
`|S_i| · 2κmax·fmax·δ`, `S_i = Finset.univ \ {i}`: each coupling
difference is `κ·|Δw|·|f|` in each of the two directed summands
(triangle + `Finset.abs_sum_le_sum_abs` + `Finset.sum_const`). -/
theorem attention_coupling_field_diff (B : ι → α → ℝ) (κ w1 w2 : ι → ι → ℝ)
    (f : α → α → ℝ)
    {κmax fmax δ : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hw : ∀ i j, |w1 i j - w2 i j| ≤ δ) (y : ι → α) (i : ι) (a : α) :
    |localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a|
      ≤ ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * δ) := by
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hone : ∀ (p q : ι) (c d : α),
      |κ p q * (w1 p q - w2 p q) * f c d| ≤ κmax * fmax * δ := by
    intro p q c d
    have habs : |κ p q * (w1 p q - w2 p q) * f c d|
        = κ p q * |w1 p q - w2 p q| * |f c d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hκ p q).1]
    rw [habs]
    have hδ0 : (0:ℝ) ≤ δ := le_trans (abs_nonneg _) (hw p q)
    have hinner : |w1 p q - w2 p q| * |f c d| ≤ δ * fmax :=
      mul_le_mul (hw p q) (hf c d) (abs_nonneg _) hδ0
    have hstep : κ p q * (|w1 p q - w2 p q| * |f c d|) ≤ κmax * (δ * fmax) :=
      mul_le_mul (hκ p q).2 hinner
        (mul_nonneg (abs_nonneg (w1 p q - w2 p q)) (abs_nonneg (f c d))) hκmax
    have hlhs : κ p q * |w1 p q - w2 p q| * |f c d|
        = κ p q * (|w1 p q - w2 p q| * |f c d|) := by ring
    have hrhs : κmax * (δ * fmax) = κmax * fmax * δ := by ring
    rw [hlhs]
    exact le_trans hstep (le_of_eq hrhs)
  have hterm : ∀ j ∈ Finset.univ \ {i},
      |attentionCoupling κ w1 f i j a (y j)
        - attentionCoupling κ w2 f i j a (y j)| ≤ 2 * κmax * fmax * δ := by
    intro j _
    have h1 := hone i j a (y j)
    have h2 := hone j i (y j) a
    have heq : κ i j * w1 i j * f a (y j) + κ j i * w1 j i * f (y j) a
          - (κ i j * w2 i j * f a (y j) + κ j i * w2 j i * f (y j) a)
        = κ i j * (w1 i j - w2 i j) * f a (y j)
          + κ j i * (w1 j i - w2 j i) * f (y j) a := by ring
    unfold attentionCoupling
    rw [heq]
    calc |κ i j * (w1 i j - w2 i j) * f a (y j)
          + κ j i * (w1 j i - w2 j i) * f (y j) a|
        ≤ |κ i j * (w1 i j - w2 i j) * f a (y j)|
          + |κ j i * (w1 j i - w2 j i) * f (y j) a| := abs_add_le _ _
      _ ≤ 2 * κmax * fmax * δ := by linarith
  have hfield : localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a
      = ∑ j ∈ Finset.univ \ {i},
        (attentionCoupling κ w1 f i j a (y j)
          - attentionCoupling κ w2 f i j a (y j)) := by
    unfold localField attentionK
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [hfield]
  have hsum : |∑ j ∈ Finset.univ \ {i},
      (attentionCoupling κ w1 f i j a (y j)
        - attentionCoupling κ w2 f i j a (y j))|
      ≤ ∑ j ∈ Finset.univ \ {i}, 2 * κmax * fmax * δ :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => hterm j hj)
  have hconst : ∑ j ∈ Finset.univ \ {i}, 2 * κmax * fmax * δ
      = ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * δ) := by
    rw [Finset.sum_const]; simp
  linarith [hsum.trans_eq hconst]

end FieldDiff

/-! ## The composed latent-error contract and the guarded drop -/
section LatentLink

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`latent_error_couples_field`** — (B3 MAIN, PREMISE-FORM chain,
honest) the composed latent-error contract: if the latent settling
tolerance gives `‖z − z*‖ ≤ η` and the softmax attention is
Lipschitz-in-`z` with constant `L_sm` (PREMISE — no such lemma is
claimed for this carrier; `z` is frozen), then the `K(z)` local field
is within `|S_i|·2κmax·fmax·L_sm·η` of the `K(z*)` local field. The
value is the explicit composed contract `η → δ_w → field
perturbation`; each arrow is auditable. -/
theorem latent_error_couples_field (B : ι → α → ℝ) (κ : ι → ι → ℝ)
    (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α) :
    |localField B (attentionK κ w1 f) y i a
      - localField B (attentionK κ w2 f) y i a|
      ≤ ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η)) :=
  attention_coupling_field_diff B κ w1 w2 f hκ hf hsoft y i a

/-- **`latent_attention_guarded_drop`** — (B3 MAIN) the C270 guard
ABSORBS the latent error: with
`ε := |S_i|·2κmax·fmax·L_sm·η` (the coupling bound), a computed
improvement margin `2ε < L̂(y_i) − L̂(a)` on the `K(z)`-fields gives a
STRICT drop of the TRUE energy
`pairwiseEnergy B (attentionK κ w2 f)` — the `2ε`-guard recipe of
`guarded_energy_delta` instantiated at the attention coupling bound.
Rejection still carries no information (C270 honesty). Joint
`(z, y)` updates remain FORBIDDEN (E3). -/
theorem latent_attention_guarded_drop [Nonempty α] (B : ι → α → ℝ)
    (κ : ι → ι → ℝ) (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α)
    (hguard : 2 * (((Finset.univ \ {i}).card : ℝ)
        * (2 * κmax * fmax * (Lsm * η)))
      < localField B (attentionK κ w1 f) y i (y i)
        - localField B (attentionK κ w1 f) y i a) :
    pairwiseEnergy B (attentionK κ w2 f) (Function.update y i a)
      < pairwiseEnergy B (attentionK κ w2 f) y := by
  refine guarded_energy_delta B (attentionK κ w2 f)
    (attention_K_symmetric κ w2 f) y i a
    (fun _ b => localField B (attentionK κ w1 f) y i b)
    (((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η)))
    (by
      have a0 := Classical.arbitrary α
      have hf0 : (0:ℝ) ≤ fmax :=
        le_trans (abs_nonneg (f a0 a0)) (hf a0 a0)
      have hκ0 : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
      have hδ0 : (0:ℝ) ≤ Lsm * η :=
        le_trans (abs_nonneg _) (hsoft i i)
      exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκ0) hf0) hδ0)) ?_ hguard
  intro b
  exact latent_error_couples_field B κ w1 w2 f hκ hf hsoft y i b

end LatentLink

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`κa3`** — deliberately ASYMMETRIC distance kernel on `Fin 3`
(anchor: the constructive symmetry must survive asymmetric `κ`). -/
noncomputable def κa3 : Fin 3 → Fin 3 → ℝ := fun i j => (i.val + 2 * j.val : ℝ) / 4 + 1

/-- **`wa3`** — nonconstant weight fixture on `Fin 3`. -/
noncomputable def wa3 : Fin 3 → Fin 3 → ℝ := fun i j => (i.val * j.val : ℝ) / 8 + 1 / 8

/-- **`fa3`** — value-coupling fixture on `Bool`. -/
def fa3 : Bool → Bool → ℝ := fun a b => if a then (if b then 3 else 1) else -2

/-- Numeric anchor (Fin 3): `L_02(tt, ff) = L_20(ff, tt)` on an
ASYMMETRIC `κ` — the index roles swap exactly. -/
example : attentionCoupling κa3 wa3 fa3 0 2 true false
    = attentionCoupling κa3 wa3 fa3 2 0 false true := by
  unfold attentionCoupling κa3 wa3 fa3
  norm_num

end Fixture

end Hagi.Model.EnergyReasoning
