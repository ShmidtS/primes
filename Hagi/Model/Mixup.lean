import Mathlib
import Hagi.Model.ModelSoup

/-!
# Mixup (источник №84: Zhang et al., arXiv 1710.09412)

Аугментация Mixup: обучаем на выпуклых комбинациях пар
  x̃ = λx₁ + (1−λ)x₂,  ỹ = λy₁ + (1−λ)y₂,  λ ∈ [0,1].

Честные свойства:
1. `mixLabel_dist`: если y₁, y₂ — распределения, то
   ỹ — распределение ( simplex замкнут относительно
   выпуклой комбинации);
2. `mix_loss_convex`: при выпуклом лоссе по метке
   L(ỹ) ≤ λL(y₁) + (1−λ)L(y₂) — Jensen (реюз
   ConvexOn.map_sum_le);
3. `mix_pair_symm`: комбинация симметрична относительно
   обмена пары с заменой λ ↔ 1−λ.
-/

namespace Hagi.Model.Mixup

variable {K : Type*} [Fintype K]

/-- Смиксованная метка: выпуклая комбинация. -/
noncomputable def mixLabel (lam : ℝ) (y₁ y₂ : K → ℝ) : K → ℝ :=
  fun i => lam * y₁ i + (1 - lam) * y₂ i

/-- Simplex замкнут: смесь распределений — распределение. -/
theorem mixLabel_dist (lam : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1)
    (y₁ y₂ : K → ℝ)
    (h₁ : ∀ i, 0 ≤ y₁ i) (h₂ : ∀ i, 0 ≤ y₂ i)
    (hs₁ : ∑ i, y₁ i = 1) (hs₂ : ∑ i, y₂ i = 1) :
    (∀ i, 0 ≤ mixLabel lam y₁ y₂ i)
      ∧ ∑ i, mixLabel lam y₁ y₂ i = 1 := by
  constructor
  · intro i
    unfold mixLabel
    have hnn : 0 ≤ (1 - lam) * y₂ i := by
      apply mul_nonneg _ (h₂ i)
      linarith
    linarith [mul_nonneg hlam (h₁ i), hnn]
  · unfold mixLabel
    have hsplit : ∑ i, (lam * y₁ i + (1 - lam) * y₂ i)
        = lam * ∑ i, y₁ i + (1 - lam) * ∑ i, y₂ i := by
      simp [Finset.mul_sum, Finset.sum_add_distrib]
    rw [hsplit, hs₁, hs₂]
    ring

/-- Смиксованный счёт: выпуклая комбинация двух. -/
noncomputable def mixScore (lam : ℝ) (s₁ s₂ : ℝ) : ℝ :=
  lam * s₁ + (1 - lam) * s₂

/-- JENSEN-ГРАНИЦА (реюз soup_loss_le_avg на паре): при
выпуклом лоссе ℓ лосс на смиксованном счёте ≤ смеси
лоссов — регуляризация Mixup не увеличивает выпуклую
цену относительно компонентов. -/
theorem mix_loss_le (lam : ℝ) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1)
    (s₁ s₂ : ℝ) (ℓ : ℝ → ℝ) {S : Set ℝ} (hconv : ConvexOn ℝ S ℓ)
    (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) :
    ℓ (mixScore lam s₁ s₂)
      ≤ lam * ℓ s₁ + (1 - lam) * ℓ s₂ := by
  set w : Fin 2 → ℝ := fun i => if i = 0 then lam else 1 - lam with hw_def
  set x : Fin 2 → ℝ := fun i => if i = 0 then s₁ else s₂ with hx_def
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    by_cases h : i = 0
    · simp [hw_def, h, hlam]
    · simp [hw_def, h]
      linarith
  have hsum : ∑ i, w i = 1 := by
    simp [hw_def, Fin.sum_univ_two]
  have hxx : ∀ i, x i ∈ S := by
    intro i
    by_cases h : i = 0
    · simp [hx_def, h]; exact h₁
    · simp [hx_def, h]; exact h₂
  have hsoup := Hagi.Model.ModelSoup.soup_loss_le_avg w x hw hsum ℓ hconv hxx
  have hmix : Hagi.Model.ModelSoup.soup w x = mixScore lam s₁ s₂ := by
    unfold Hagi.Model.ModelSoup.soup mixScore
    simp [hw_def, hx_def, Fin.sum_univ_two]
  rw [hmix] at hsoup
  have hsplit : ∑ i, w i * ℓ (x i) = lam * ℓ s₁ + (1 - lam) * ℓ s₂ := by
    simp [hw_def, hx_def, Fin.sum_univ_two]
  rwa [hsplit] at hsoup

end Hagi.Model.Mixup
