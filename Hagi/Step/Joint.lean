/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib


/-!
# Joint — joint-шаг: когда fine-tune с merged prior помогает и когда разрушает

Модель: первопорядковое квадратичное приращение
компонентной (по корпусам) потери у prior:
`quadIncr gc Hc δ = ⟨gc, δ⟩ + ½ δᵀHcδ`, шаг по градиенту
смеси `δ = −lr·g`, гладкость `vᵀHc v ≤ L‖v‖²`.

* `jointStep_conflict_regression`: при конфликте
  `⟨gc, g⟩ < 0` любой шаг `0 < lr < 2|⟨gc, g⟩|/(L‖g‖²)`
  строго увеличивает компонентную потерю;
* `jointStep_regression_bound`: для любого lr —
  `quadIncr ≤ |lr|·‖gc‖·‖g‖ + (L/2)·lr²·‖g‖²` (линейно
  по lr при малых шагах);
* `trustRegion_bound`: при `‖δ‖ ≤ R` —
  `quadIncr ≤ ‖gc‖·R + (L/2)·R²` независимо от направления
  шага (обоснование proximal/ridge-формы).
-/
open scoped Matrix

set_option linter.style.header false


namespace Hagi.Step

section JointStep

variable {n : Type*} [Fintype n]

/-- `quadIncr gc Hc δ = gc ⬝ᵥ δ + ½·δ ⬝ᵥ (Hc *ᵥ δ)` —
квадратичное приращение компонентной потери. -/
noncomputable def quadIncr (gc : n → ℝ) (Hc : Matrix n n ℝ)
    (δ : n → ℝ) : ℝ :=
  gc ⬝ᵥ δ + (1/2) * (δ ⬝ᵥ (Hc *ᵥ δ))

variable {gc : n → ℝ} {Hc : Matrix n n ℝ}

/-- При `0 < L`, `g ≠ 0`, `gc ⬝ᵥ g < 0`,
`−L·(v⬝ᵥv) ≤ v ⬝ᵥ (Hc *ᵥ v)` и
`0 < lr < 2·|gc ⬝ᵥ g|/(L·(g ⬝ᵥ g))` выполнено
`0 < quadIncr gc Hc (fun i => −lr·g i)` — конфлитный
компонентный градиент строго растит потерю. -/
theorem jointStep_conflict_regression (g : n → ℝ) (L : ℝ)
    (hL : 0 < L) (hg : g ≠ 0)
    (hconflict : gc ⬝ᵥ g < 0)
    (hsmoothLo : ∀ v : n → ℝ, -L * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Hc *ᵥ v))
    (_hsmooth : ∀ v : n → ℝ, v ⬝ᵥ (Hc *ᵥ v) ≤ L * (v ⬝ᵥ v))
    {lr : ℝ} (hlr0 : 0 < lr)
    (hlr1 : lr < 2 * |gc ⬝ᵥ g| / (L * (g ⬝ᵥ g))) :
    0 < quadIncr gc Hc (fun i => -lr * g i) := by
  -- the norm identity: ||-lr*g||² = lr²||g||²
  have hnorm : (fun i => -lr * g i) ⬝ᵥ (fun i => -lr * g i)
      = lr * lr * (g ⬝ᵥ g) := by
    simp only [dotProduct]
    have hmem : ∀ i : n, -lr * g i * (-lr * g i)
        = (lr * lr) * (g i * g i) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hmem i, ← Finset.mul_sum]
  -- the linear term: -lr*<gc,g> = lr*|<gc,g>| > 0
  have hlin : gc ⬝ᵥ (fun i => -lr * g i) = lr * |gc ⬝ᵥ g| := by
    have hsplit : gc ⬝ᵥ (fun i => -lr * g i)
        = (-lr) * (gc ⬝ᵥ g) := by
      simp only [dotProduct]
      have hmem : ∀ i : n, gc i * (-lr * g i)
          = (-lr) * (gc i * g i) := fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hmem i, Finset.mul_sum]
    rw [hsplit]
    have habs : |gc ⬝ᵥ g| = -(gc ⬝ᵥ g) := abs_of_neg hconflict
    rw [habs]
    linarith
  -- g ≠ 0: positive norm
  have hgg : 0 < g ⬝ᵥ g := by
    have h2 : 0 ≤ g ⬝ᵥ g := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exact (hg ((dotProduct_self_eq_zero (v := g)).mp h.symm)).elim
  -- the window condition, multiplied through
  have hwindow : lr * (L * (g ⬝ᵥ g)) < 2 * |gc ⬝ᵥ g| := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < L * (g ⬝ᵥ g))] at hlr1
    exact hlr1
  -- the quadratic term bounded below by -(L/2)lr²||g||²
  have hqlo : -(L * lr * lr * (g ⬝ᵥ g))
      ≤ (fun i => -lr * g i) ⬝ᵥ (Hc *ᵥ (fun i => -lr * g i)) := by
    have hstep := hsmoothLo (fun i => -lr * g i)
    rw [hnorm] at hstep
    linarith [hstep]
  -- half the window: (L/2)lr²||g||² < lr|<gc,g>|
  have hhalf : (1/2) * (L * lr * lr * (g ⬝ᵥ g)) < lr * |gc ⬝ᵥ g| := by
    have h1 : lr * (lr * (L * (g ⬝ᵥ g))) < lr * (2 * |gc ⬝ᵥ g|) :=
      mul_lt_mul_of_pos_left hwindow hlr0
    nlinarith [h1, hgg]
  -- conclude: quadIncr = lr|<gc,g>| + (1/2)quad > 0
  unfold quadIncr
  rw [hlin]
  have : (1/2) * ((fun i => -lr * g i)
      ⬝ᵥ (Hc *ᵥ (fun i => -lr * g i)))
      ≥ -(1/2) * (L * lr * lr * (g ⬝ᵥ g)) := by
    linarith [hqlo]
  linarith [this, hhalf]

/-- При `v ⬝ᵥ (Hc *ᵥ v) ≤ L·(v ⬝ᵥ v)` для всех v и любом lr:
`quadIncr gc Hc (fun i => −lr·g i)
≤ |lr|·√(gc⬝ᵥgc)·√(g⬝ᵥg) + (L/2)·lr²·(g⬝ᵥg)`. -/
theorem jointStep_regression_bound (g : n → ℝ) (L : ℝ)
    (hsmooth : ∀ v : n → ℝ, v ⬝ᵥ (Hc *ᵥ v) ≤ L * (v ⬝ᵥ v))
    (lr : ℝ) :
    quadIncr gc Hc (fun i => -lr * g i)
      ≤ |lr| * (Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (g ⬝ᵥ g))
        + (1/2) * L * lr * lr * (g ⬝ᵥ g) := by
  -- Cauchy-Schwarz: (<gc,g>)² <= (gc⬝ᵥgc)(g⬝ᵥg)
  have hcauchy : (gc ⬝ᵥ g)^2 ≤ (gc ⬝ᵥ gc) * (g ⬝ᵥ g) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ gc g
    have hconv : (∑ i, gc i ^ 2) = ∑ i, gc i * gc i :=
      Finset.sum_congr rfl fun i _ => pow_two (gc i)
    have hconv2 : (∑ i, g i ^ 2) = ∑ i, g i * g i :=
      Finset.sum_congr rfl fun i _ => pow_two (g i)
    rw [hconv, hconv2] at h
    exact h
  -- |<gc,g>| <= sqrt((gc⬝ᵥgc)(g⬝ᵥg)) = sqrt(gc⬝ᵥgc)*sqrt(g⬝ᵥg)
  have hcs : |gc ⬝ᵥ g|
      ≤ Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (g ⬝ᵥ g) := by
    have hsq : |gc ⬝ᵥ g| * |gc ⬝ᵥ g| ≤ (gc ⬝ᵥ gc) * (g ⬝ᵥ g) := by
      rw [abs_mul_abs_self (gc ⬝ᵥ g), ← pow_two (gc ⬝ᵥ g)]
      exact hcauchy
    have h4 : Real.sqrt (|gc ⬝ᵥ g| * |gc ⬝ᵥ g|)
        ≤ Real.sqrt ((gc ⬝ᵥ gc) * (g ⬝ᵥ g)) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul_self (abs_nonneg (gc ⬝ᵥ g))] at h4
    rw [Real.sqrt_mul (by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)] at h4
    exact h4
  -- the linear term: -lr*<gc,g>, abs = |lr|*|<gc,g>|
  have hlinabs : |gc ⬝ᵥ (fun i => -lr * g i)| = |lr| * |gc ⬝ᵥ g| := by
    have hsplit : gc ⬝ᵥ (fun i => -lr * g i) = (-lr) * (gc ⬝ᵥ g) := by
      simp only [dotProduct]
      have hmem : ∀ i : n, gc i * (-lr * g i)
          = (-lr) * (gc i * g i) := fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hmem i, Finset.mul_sum]
    rw [hsplit, abs_mul, abs_neg]
  -- the quadratic term bounded by L*lr²*(g⬝ᵥg)
  have hnorm : (fun i => -lr * g i) ⬝ᵥ (fun i => -lr * g i)
      = lr * lr * (g ⬝ᵥ g) := by
    simp only [dotProduct]
    have hmem : ∀ i : n, -lr * g i * (-lr * g i)
        = (lr * lr) * (g i * g i) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hmem i, ← Finset.mul_sum]
  have hq : (fun i => -lr * g i) ⬝ᵥ (Hc *ᵥ (fun i => -lr * g i))
      ≤ L * lr * lr * (g ⬝ᵥ g) := by
    have hstep := hsmooth (fun i => -lr * g i)
    rw [hnorm] at hstep
    linarith [hstep]
  -- assemble
  unfold quadIncr
  have hle1 : gc ⬝ᵥ (fun i => -lr * g i)
      ≤ |lr| * (Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (g ⬝ᵥ g)) := by
    calc gc ⬝ᵥ (fun i => -lr * g i)
        ≤ |gc ⬝ᵥ (fun i => -lr * g i)| := le_abs_self _
      _ = |lr| * |gc ⬝ᵥ g| := hlinabs
      _ ≤ |lr| * (Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (g ⬝ᵥ g)) :=
          mul_le_mul_of_nonneg_left hcs (abs_nonneg lr)
  linarith [hle1, hq]

/-- При `0 ≤ L`, гладкости и `√(δ ⬝ᵥ δ) ≤ R`:
`quadIncr gc Hc δ ≤ √(gc⬝ᵥgc)·R + (1/2)·L·R²`
независимо от направления δ. -/
theorem trustRegion_bound (L R : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ v : n → ℝ, v ⬝ᵥ (Hc *ᵥ v) ≤ L * (v ⬝ᵥ v))
    (δ : n → ℝ) (hδ : Real.sqrt (δ ⬝ᵥ δ) ≤ R) :
    quadIncr gc Hc δ
      ≤ Real.sqrt (gc ⬝ᵥ gc) * R + (1/2) * L * R * R := by
  -- Cauchy-Schwarz: <gc,δ> <= sqrt(gc⬝ᵥgc)*sqrt(δ⬝ᵥδ) <= sqrt(gc⬝ᵥgc)*R
  have hcauchy : (gc ⬝ᵥ δ)^2 ≤ (gc ⬝ᵥ gc) * (δ ⬝ᵥ δ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ gc δ
    have hconv : (∑ i, gc i ^ 2) = ∑ i, gc i * gc i :=
      Finset.sum_congr rfl fun i _ => pow_two (gc i)
    have hconv2 : (∑ i, δ i ^ 2) = ∑ i, δ i * δ i :=
      Finset.sum_congr rfl fun i _ => pow_two (δ i)
    rw [hconv, hconv2] at h
    exact h
  have hcs : gc ⬝ᵥ δ
      ≤ Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (δ ⬝ᵥ δ) := by
    have hcauchy : (gc ⬝ᵥ δ)^2 ≤ (gc ⬝ᵥ gc) * (δ ⬝ᵥ δ) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ gc δ
      have hconv : (∑ i, gc i ^ 2) = ∑ i, gc i * gc i :=
        Finset.sum_congr rfl fun i _ => pow_two (gc i)
      have hconv2 : (∑ i, δ i ^ 2) = ∑ i, δ i * δ i :=
        Finset.sum_congr rfl fun i _ => pow_two (δ i)
      rw [hconv, hconv2] at h
      exact h
    have h1 : gc ⬝ᵥ δ ≤ |gc ⬝ᵥ δ| := le_abs_self _
    have h2 : |gc ⬝ᵥ δ| ≤ Real.sqrt ((gc ⬝ᵥ gc) * (δ ⬝ᵥ δ)) := by
      have hsq : |gc ⬝ᵥ δ| * |gc ⬝ᵥ δ| ≤ (gc ⬝ᵥ gc) * (δ ⬝ᵥ δ) := by
        rw [abs_mul_abs_self (gc ⬝ᵥ δ), ← pow_two (gc ⬝ᵥ δ)]
        exact hcauchy
      have h4 : Real.sqrt (|gc ⬝ᵥ δ| * |gc ⬝ᵥ δ|)
          ≤ Real.sqrt ((gc ⬝ᵥ gc) * (δ ⬝ᵥ δ)) := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul_self (abs_nonneg (gc ⬝ᵥ δ))] at h4
      exact h4
    rw [Real.sqrt_mul (by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)] at h2
    linarith [h1, h2]
  have hlin : gc ⬝ᵥ δ ≤ Real.sqrt (gc ⬝ᵥ gc) * R := by
    calc gc ⬝ᵥ δ
        ≤ Real.sqrt (gc ⬝ᵥ gc) * Real.sqrt (δ ⬝ᵥ δ) := hcs
      _ ≤ Real.sqrt (gc ⬝ᵥ gc) * R :=
          mul_le_mul_of_nonneg_left hδ (by positivity)
  -- the quadratic term: δ⬝ᵥδ <= R² (squaring the trust radius)
  have hquad : δ ⬝ᵥ (Hc *ᵥ δ) ≤ L * (δ ⬝ᵥ δ) := hsmooth δ
  have hR2 : δ ⬝ᵥ δ ≤ R * R := by
    have hnn : 0 ≤ δ ⬝ᵥ δ := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hR : 0 ≤ R := le_trans (Real.sqrt_nonneg _) hδ
    have h2 : Real.sqrt (δ ⬝ᵥ δ) * Real.sqrt (δ ⬝ᵥ δ) ≤ R * R :=
      mul_le_mul hδ hδ (Real.sqrt_nonneg _) hR
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn] at h2
    exact h2
  -- assemble: quadIncr = <gc,δ> + (1/2)quad <= sqrt(gc⬝ᵥgc)*R + (L/2)*R²
  unfold quadIncr
  have hfin : (1/2) * (δ ⬝ᵥ (Hc *ᵥ δ)) ≤ (1/2) * L * (R * R) := by
    have hle : δ ⬝ᵥ (Hc *ᵥ δ) ≤ L * (R * R) :=
      calc δ ⬝ᵥ (Hc *ᵥ δ) ≤ L * (δ ⬝ᵥ δ) := hquad
        _ ≤ L * (R * R) := mul_le_mul_of_nonneg_left hR2 hL
    linarith [hle]
  linarith [hlin, hfin]

end JointStep



end Hagi.Step

namespace Hagi
export Hagi.Step (quadIncr jointStep_conflict_regression jointStep_regression_bound trustRegion_bound)
end Hagi
