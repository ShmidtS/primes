/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Math.Info.InfoCore

set_option linter.style.header false

/-!
# The concat==child invariant and the `scale = 1/n` temperature correction

* `concatCols_identical` — the concat head of `n` copies of `W`
  applied to the stacked states of `n` copies of `x` is
  `(n : ℝ) • (W *ᵥ x)`.
* `concat_unique_identity_scale` — a scale `s` reproducing the
  child at a coordinate where the child's logit is nonzero must
  equal `1 / (n : ℝ)`.
* `temperature_softmax_eq_forces_const` /
  `temperature_changes_softmax` — if rescaled logits (`c ≠ 1`)
  produce the same softmax distribution, the logits were constant.

The `lse` / `ceOneHot` / `softmaxP` family lives in
`Hagi.Math.Info.InfoCore`, which this module imports.
-/

open scoped Matrix

namespace Hagi.Core

section Concat

variable {o m : Type*} [Fintype o] [Fintype m]

/-- The column-concatenation of `n` copies of the child head `W`
(the merged head of `n` identical children). -/
def concatCols (n : ℕ) (W : Matrix o m ℝ) :
    Matrix o (Fin n × m) ℝ :=
  fun j p => W j p.2

omit [Fintype o] in
/-- The concatenated head of `n` copies of `W`, applied to the
stacked states of `n` copies of `x`, yields `(n : ℝ) • (W *ᵥ x)`. -/
theorem concatCols_identical (n : ℕ) (W : Matrix o m ℝ) (x : m → ℝ) :
    concatCols n W *ᵥ (fun p => x p.2) = (n : ℝ) • (W *ᵥ x) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, concatCols]
  rw [Fintype.sum_prod_type]
  have step1 : ∀ i : Fin n, ∑ y : m, W j (i, y).2 * x (i, y).2
      = ∑ y : m, W j y * x y := fun i =>
    Finset.sum_congr rfl fun y _ => rfl
  rw [Finset.sum_congr rfl (fun i _ => step1 i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp [Matrix.mulVec, dotProduct]

omit [Fintype o] in
/-- Pointwise form of `concatCols_identical`. -/
theorem concatCols_identical_apply (n : ℕ) (W : Matrix o m ℝ) (x : m → ℝ)
    (j : o) :
    (concatCols n W *ᵥ (fun p => x p.2)) j = (n : ℝ) * (W *ᵥ x) j := by
  have h := congrFun (concatCols_identical n W x) j
  rw [h, Pi.smul_apply, smul_eq_mul]

omit [Fintype o] in
/-- If the scale `s` rescales the merged logits to the child's logit
at a coordinate `j` where `(W *ᵥ x) j ≠ 0`, then `s = 1 / (n : ℝ)`. -/
theorem concat_unique_identity_scale (n : ℕ) (hn : 0 < n)
    (W : Matrix o m ℝ) (x : m → ℝ) (j : o)
    (hx : (W *ᵥ x) j ≠ 0) (s : ℝ)
    (hs : s * (concatCols n W *ᵥ (fun p => x p.2)) j = (W *ᵥ x) j) :
    s = 1 / (n : ℝ) := by
  rw [concatCols_identical_apply, ← mul_assoc] at hs
  have h2' : s * (n : ℝ) = 1 :=
    mul_right_cancel₀ hx (by rw [one_mul]; exact hs)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have h3 : s = (n : ℝ)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hn').mp h2'
  rw [h3, inv_eq_one_div]

end Concat

section Temperature

variable {k : Type*} [Fintype k] [Nonempty k]

/-- If `c ≠ 1` and rescaling the logits by `c` leaves the softmax
distribution unchanged, then the logits are constant: `z a = z b`
for all `a, b`. -/
theorem temperature_softmax_eq_forces_const (c : ℝ) (z : k → ℝ)
    (hc : c ≠ 1)
    (h : (fun i => Real.exp (c * z i) / ∑ l, Real.exp (c * z l))
      = (fun i => Real.exp (z i) / ∑ l, Real.exp (z l))) :
    ∀ a b : k, z a = z b := by
  have hS1 : (0 : ℝ) < ∑ l, Real.exp (z l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hSc : (0 : ℝ) < ∑ l, Real.exp (c * z l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hfun : ∀ i : k,
      Real.exp (c * z i) * (∑ l, Real.exp (z l))
        = Real.exp (z i) * (∑ l, Real.exp (c * z l)) := by
    intro i
    have hfuni := congrFun h i
    rw [div_eq_div_iff (ne_of_gt hSc) (ne_of_gt hS1)] at hfuni
    exact hfuni
  intro a b
  by_contra hne
  have ha := hfun a
  have hb := hfun b
  have key0 : (Real.exp (c * z a) * Real.exp (z b)
      - Real.exp (z a) * Real.exp (c * z b))
      * (∑ l, Real.exp (z l)) = 0 := by
    linear_combination Real.exp (z b) * ha - Real.exp (z a) * hb
  have key : Real.exp (c * z a) * Real.exp (z b)
      = Real.exp (z a) * Real.exp (c * z b) := by
    rcases mul_eq_zero.mp key0 with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 (ne_of_gt hS1)
  have hexp : Real.exp (c * z a + z b) = Real.exp (z a + c * z b) := by
    rw [Real.exp_add, Real.exp_add]
    exact key
  have heq : c * z a + z b = z a + c * z b := Real.exp_injective hexp
  have hzero : (c - 1) * (z a - z b) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hc
  · exact absurd (sub_eq_zero.mp h2) hne

/-- If `c ≠ 1` and the logits are non-constant, rescaling by `c`
changes the softmax distribution. -/
theorem temperature_changes_softmax (c : ℝ) (z : k → ℝ) (hc : c ≠ 1)
    (hne : ∃ a b : k, z a ≠ z b) :
    (fun i => Real.exp (c * z i) / ∑ l, Real.exp (c * z l))
      ≠ (fun i => Real.exp (z i) / ∑ l, Real.exp (z l)) := by
  intro hcontra
  obtain ⟨a, b, hab⟩ := hne
  exact hab (temperature_softmax_eq_forces_const c z hc hcontra a b)

end Temperature
end Hagi.Core
