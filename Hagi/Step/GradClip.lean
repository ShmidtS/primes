import Mathlib

/-!
# Gradient Clipping: проекция на ℓ₂-шар (источник №29)

Источник №29: Pascanu, Mikolov, Bengio, "On the difficulty of
training recurrent neural networks" (arXiv 1211.5063).
Gradient clipping — стандартная защита от взрывных градиентов:
g заменяется на min(1, R/‖g‖)·g — проекцию на ℓ₂-шар радиуса R.

Формализованное ядро (строгое):
- `clip_norm_le`: ‖clip R g‖ ≤ R — норма никогда не
  превосходит порога (защита от взрыва);
- `clip_eq_of_le`: при ‖g‖ ≤ R клип не меняет вектор
  (инертность в нормальном режиме);
- `clip_idem`: повторный клип ничего не меняет;
- `clip_dir`: при ‖g‖ > R > 0 клип сохраняет НАПРАВЛЕНИЕ
  (положительный скаляр) — спусковость направления не
  нарушается.
-/

namespace Hagi.Step.GradClip

variable {n : ℕ}

/-- Клип на ℓ₂-шар радиуса R: тождество при ‖g‖ ≤ R,
иначе масштабирование до нормы R. -/
noncomputable def clip (R : ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  if ‖g‖ ≤ R then g else (R / ‖g‖) • g

/-- Норма клипа не превосходит порога (ядро №29). -/
theorem clip_norm_le (R : ℝ) (hR : 0 ≤ R) (g : Fin n → ℝ) :
    ‖clip R g‖ ≤ R := by
  unfold clip
  split
  · next hT => exact hT
  · next hN =>
    have hgn : ‖g‖ ≠ 0 := by
      intro hz
      rw [hz] at hN
      simp at hN
      linarith
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (norm_nonneg g)),
      div_mul_cancel₀ R hgn]

/-- При ‖g‖ ≤ R клип инертен. -/
theorem clip_eq_of_le (R : ℝ) (g : Fin n → ℝ) (h : ‖g‖ ≤ R) :
    clip R g = g := by
  unfold clip
  split
  · rfl
  · next hN => exact absurd h hN

/-- Повторный клип идемпотентен. -/
theorem clip_idem (R : ℝ) (hR : 0 ≤ R) (g : Fin n → ℝ) :
    clip R (clip R g) = clip R g := by
  have hle := clip_norm_le R hR g
  exact clip_eq_of_le R (clip R g) hle

/-- При R < ‖g‖ клип сохраняет направление:
clip R g = c • g с c = R/‖g‖ > 0 (нужно R > 0). -/
theorem clip_dir (R : ℝ) (hR : 0 < R) (g : Fin n → ℝ)
    (h : R < ‖g‖) : ∃ c : ℝ, 0 < c ∧ clip R g = c • g := by
  refine ⟨R / ‖g‖, div_pos hR (norm_pos_iff.mpr (by
    intro hz
    rw [hz] at h
    simp at h
    linarith)), ?_⟩
  unfold clip
  split
  · next hT => exact absurd hT (by linarith)
  · rfl

end Hagi.Step.GradClip
