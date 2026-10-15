/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.GibbsCooling
import Hagi.Probability.MomentBounds
set_option linter.style.header false

open Finset Real

/-- **Экспоненциальное затухание флуктуаций энергии Гиббса (R498)**:
если все энергии лежат в [E*, E* + Δ] и есть зазор δ > 0,
то дисперсия энергии при распределении Гиббса не превосходит
Δ² · (n−1) · exp(−δ/T). Доказательство связывает R393
(экспоненциальная оценка избытка среднего) с R496
(Бхатия—Дэвис: Var ≤ (b−μ)(μ−a)). Это даёт сертифицированную
границу энергетических флуктуаций для термостатного stop-gate. -/
theorem gibbs_energy_variance_bound
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
    let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
    let μ : ℝ := ∑ v : V, p v * E v
    ∑ v : V, p v * (E v - μ) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
  let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
  let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
  let μ : ℝ := ∑ v : V, p v * E v
  change ∑ v : V, p v * (E v - μ) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T)
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hp : ∀ v : V, 0 < p v := by
    intro v
    dsimp [p]
    exact div_pos (Real.exp_pos _) hZpos
  have hp1 : ∑ v : V, p v = 1 := by
    change (∑ v : V, Real.exp (-(E v) / T) / Z) = 1
    rw [Finset.sum_div]
    change Z / Z = 1
    exact div_self hZpos.ne'
  -- Convert the normalized Gibbs mean into the partition-function form R393.
  have hμeq : μ =
      (∑ v : V, E v * Real.exp (-(E v) / T)) / Z := by
    calc
      μ = ∑ v : V, p v * E v := rfl
      _ = ∑ v : V, (E v * Real.exp (-(E v) / T)) / Z := by
        apply Finset.sum_congr rfl
        intro v _
        change (Real.exp (-(E v) / T) / Z) * E v
          = (E v * Real.exp (-(E v) / T)) / Z
        ring
      _ = (∑ v : V, E v * Real.exp (-(E v) / T)) / Z := by
        rw [Finset.sum_div]
  have hmean := gibbs_expected_energy_bound E δ T hT vstar Δ hmin hgap hΔ
  have hμupper : μ ≤ E vstar
      + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
    rw [hμeq]
    simpa [Z] using hmean
  have hΔ0 : (0:ℝ) ≤ Δ := by
    have h := hΔ vstar
    simpa using h
  have hconst : ∑ v : V, p v * E vstar = E vstar := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (p v) (E vstar)),
      ← Finset.mul_sum, hp1, mul_one]
  have hμlower : E vstar ≤ μ := by
    calc
      E vstar = ∑ v : V, p v * E vstar := hconst.symm
      _ ≤ ∑ v : V, p v * E v :=
        Finset.sum_le_sum (fun v _ =>
          mul_le_mul_of_nonneg_left (hmin v) (le_of_lt (hp v)))
      _ = μ := rfl
  have hconstB : ∑ v : V, p v * (E vstar + Δ) = E vstar + Δ := by
    rw [Finset.sum_congr rfl
        (fun v _ => mul_comm (p v) (E vstar + Δ)),
      ← Finset.mul_sum, hp1, mul_one]
  have hμleB : μ ≤ E vstar + Δ := by
    calc
      μ = ∑ v : V, p v * E v := rfl
      _ ≤ ∑ v : V, p v * (E vstar + Δ) :=
        Finset.sum_le_sum (fun v _ =>
          mul_le_mul_of_nonneg_left (by linarith [hΔ v]) (le_of_lt (hp v)))
      _ = E vstar + Δ := hconstB
  have hmeanExcess : μ - E vstar
      ≤ Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
    linarith [hμupper]
  -- Apply the sharper Bhatia-Davis variance inequality (R496).
  have hbd := bhatia_davis p E E vstar (E vstar + Δ) hp hp1
    hmin (fun v => by linarith [hΔ v])
  have hvar : ∑ v : V, p v * (E v - μ) ^ 2
      ≤ (E vstar + Δ - μ) * (μ - E vstar) := by
    simpa [μ] using hbd
  have hfactor1 : E vstar + Δ - μ ≤ Δ := by
    linarith [hμlower]
  have hfactor2 : (0:ℝ) ≤ μ - E vstar := by
    linarith [hμlower]
  calc
    ∑ v : V, p v * (E v - μ) ^ 2
        ≤ (E vstar + Δ - μ) * (μ - E vstar) := hvar
    _ ≤ Δ * (μ - E vstar) :=
      mul_le_mul_of_nonneg_right hfactor1 hfactor2
    _ ≤ Δ * (Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T)) :=
      mul_le_mul_of_nonneg_left hmeanExcess hΔ0
    _ = Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by ring
