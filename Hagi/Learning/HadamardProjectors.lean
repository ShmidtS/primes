import Mathlib.Tactic
import Hagi.Core.Hadamard

set_option linter.style.header false

/-!
# HadamardProjectors — ортогональные проекторы характеров для
изоляции доменов памяти (исследовательский цикл 7)

Синтез RCDL+HAGI: памяти разных доменов не должны
интерферировать. Строки матрицы Сильвестра — характеры χ_w,
попарно ортогональные. Проектор на характер w:
P_w(v) = (⟨χ_w, v⟩ / 2^k) • χ_w.

Доказано строго:
- `charProj_idem`: P_w — идемпотентный проектор;
- `charProj_orthog`: P_w ∘ P_u = 0 для w ≠ u — изоляция
  доменов: обновление памяти домена w не меняет компоненту u.
-/

open Finset

namespace Hagi.Learning.HadamardProjectors

open Hagi.Core

variable {k : ℕ}

/-- Строка-характер χ_w матрицы Сильвестра. -/
def charRow (w : Fin k → ZMod 2) : (Fin k → ZMod 2) → ℚ :=
  fun i => (sylvester k w i : ℚ)

/-- Норма характера: ⟨χ_w, χ_w⟩ = 2^k. -/
theorem charRow_norm (w : Fin k → ZMod 2) :
    dotProduct (charRow w) (charRow w) = (2 ^ k : ℕ) := by
  unfold charRow dotProduct sylvester
  simp only [← Int.cast_mul, chi2_sq, Int.cast_one]
  rw [Finset.sum_const]
  simp [Fintype.card_fun]

/-- Ортогональность характеров: w ≠ u ⇒ ⟨χ_w, χ_u⟩ = 0. -/
theorem charRow_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u) :
    dotProduct (charRow w) (charRow u) = 0 := by
  have hwu0 : w + u ≠ 0 := by
    intro h0
    apply hwu
    funext l
    have := congrFun h0 l
    simp only [Pi.add_apply] at this
    have h2 : w l = -u l := by
      rw [eq_neg_iff_add_eq_zero]
      exact this
    rw [h2, zmod2_neg_eq_self]
  unfold charRow dotProduct sylvester
  have hmul : ∀ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l)) : ℤ)
        = chi2 (∑ l, (w + u) l * i l) := by
    intro i
    rw [chi2_mul, inner2_add_left]
  have hz : ∑ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hmul i), sum_chi2_eq_zero hwu0]
  calc dotProduct (charRow w) (charRow u)
      = ((∑ i : Fin k → ZMod 2,
          ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ))) : ℚ) := rfl
    _ = ((0 : ℤ) : ℚ) := by
        have : ∀ i : Fin k → ZMod 2,
            (↑(chi2 (∑ l, w l * i l)) * ↑(chi2 (∑ l, u l * i l)) : ℚ)
              = ↑((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l))) :=
          fun i => (Int.cast_mul _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Int.cast_sum, hz]
    _ = 0 := by simp


/-! ### Проекторы и изоляция доменов -/

/-- Ортогональный проектор на характер χ_w (нормировка 2^k). -/
noncomputable def charProj (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℚ) : (Fin k → ZMod 2) → ℚ :=
  fun i => (dotProduct (charRow w) v / (2 ^ k : ℕ)) * charRow w i

/-- ИДЕМПОТЕНТНОСТЬ: P_w — проектор. -/
theorem charProj_idem (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℚ) :
    charProj w (charProj w v) = charProj w v := by
  have hnorm : dotProduct (charRow w) (charRow w) = (2 ^ k : ℕ) :=
    charRow_norm w
  unfold charProj
  have hinner : dotProduct (charRow w)
      (fun j => dotProduct (charRow w) v / (2 ^ k : ℕ) * charRow w j)
        = dotProduct (charRow w) v := by
    have hsmul : (fun j => dotProduct (charRow w) v / (2 ^ k : ℕ)
        * charRow w j)
          = (dotProduct (charRow w) v / (2 ^ k : ℕ)) • (charRow w) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hsmul, dotProduct_smul, hnorm]
    have h2k : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by
      positivity
    rw [smul_eq_mul, div_mul_cancel₀ _ h2k]
  funext i
  rw [hinner]


/-- ИЗОЛЯЦИЯ ДОМЕНОВ: проекторы разных характеров annihilируют
друг друга: P_w ∘ P_u = 0 при w ≠ u. Обновление памяти домена w
не меняет компоненту домена u. -/
theorem charProj_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℚ) :
    charProj w (charProj u v) = 0 := by
  have horth := charRow_orthog hwu
  unfold charProj
  have hsmul : (fun j => dotProduct (charRow u) v / (2 ^ k : ℕ)
      * charRow u j)
        = (dotProduct (charRow u) v / (2 ^ k : ℕ)) • (charRow u) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  funext i
  rw [hsmul, dotProduct_smul, horth, smul_zero]
  simp


/-! ### ℝ-версии (для связки с RCDL-софтмаксом) -/

/-- Строка-характер в ℝ. -/
def charRowR (w : Fin k → ZMod 2) : (Fin k → ZMod 2) → ℝ :=
  fun i => (sylvester k w i : ℝ)

theorem charRowR_norm (w : Fin k → ZMod 2) :
    dotProduct (charRowR w) (charRowR w) = (2 ^ k : ℕ) := by
  unfold charRowR dotProduct sylvester
  simp only [← Int.cast_mul, chi2_sq, Int.cast_one]
  rw [Finset.sum_const]
  simp [Fintype.card_fun]

theorem charRowR_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u) :
    dotProduct (charRowR w) (charRowR u) = 0 := by
  have hwu0 : w + u ≠ 0 := by
    intro h0
    apply hwu
    funext l
    have := congrFun h0 l
    simp only [Pi.add_apply] at this
    have h2 : w l = -u l := by
      rw [eq_neg_iff_add_eq_zero]
      exact this
    rw [h2, zmod2_neg_eq_self]
  unfold charRowR dotProduct sylvester
  have hmul : ∀ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l)) : ℤ)
        = chi2 (∑ l, (w + u) l * i l) := by
    intro i
    rw [chi2_mul, inner2_add_left]
  have hz : ∑ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hmul i), sum_chi2_eq_zero hwu0]
  calc dotProduct (charRowR w) (charRowR u)
      = ((∑ i : Fin k → ZMod 2,
          ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ))) : ℝ) := rfl
    _ = ((0 : ℤ) : ℝ) := by
        have : ∀ i : Fin k → ZMod 2,
            (↑(chi2 (∑ l, w l * i l)) * ↑(chi2 (∑ l, u l * i l)) : ℝ)
              = ↑((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l))) :=
          fun i => (Int.cast_mul _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Int.cast_sum, hz]
    _ = 0 := by simp

/-- Ортогональный проектор на характер χ_w в ℝ. -/
noncomputable def charProjR (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  fun i => (dotProduct (charRowR w) v / (2 ^ k : ℕ)) * charRowR w i

theorem charProjR_idem (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    charProjR w (charProjR w v) = charProjR w v := by
  have hnorm : dotProduct (charRowR w) (charRowR w) = (2 ^ k : ℕ) :=
    charRowR_norm w
  unfold charProjR
  have hsmul : (fun j => dotProduct (charRowR w) v / (2 ^ k : ℕ)
      * charRowR w j)
        = (dotProduct (charRowR w) v / (2 ^ k : ℕ)) • (charRowR w) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  have hinner : dotProduct (charRowR w)
      (fun j => dotProduct (charRowR w) v / (2 ^ k : ℕ) * charRowR w j)
        = dotProduct (charRowR w) v := by
    rw [hsmul, dotProduct_smul, hnorm]
    have h2k : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
    rw [smul_eq_mul, div_mul_cancel₀ _ h2k]
  funext i
  rw [hinner]

theorem charProjR_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℝ) :
    charProjR w (charProjR u v) = 0 := by
  have horth := charRowR_orthog hwu
  unfold charProjR
  have hsmul : (fun j => dotProduct (charRowR u) v / (2 ^ k : ℕ)
      * charRowR u j)
        = (dotProduct (charRowR u) v / (2 ^ k : ℕ)) • (charRowR u) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  funext i
  rw [hsmul, dotProduct_smul, horth, smul_zero]
  simp

/-- Линейность проектора по аргументу. -/
theorem charProjR_add (w : Fin k → ZMod 2) (v1 v2 : (Fin k → ZMod 2) → ℝ) :
    charProjR w (v1 + v2) = charProjR w v1 + charProjR w v2 := by
  unfold charProjR
  funext i
  rw [dotProduct_add, add_div, add_mul, Pi.add_apply]

end Hagi.Learning.HadamardProjectors

