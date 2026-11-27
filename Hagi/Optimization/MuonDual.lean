/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MuonDual — ортогонализованный шаг максимизирует линейный функционал

Muon (optimal_lm.py, `lr_muon`): шаг по `G (GᵀG)^{-1/2}` — полярному множителю,
вычисляемому Polar Express (`PolarExpressCert`). Матричный смысл: спектральная
норма — двойственная к ядровой, `‖G‖_* = max_{‖U‖≤1} ⟨G, U⟩`, и ортогонализация
даёт максимизатор.

В евклидовом пространстве (скалярный срез каждого сингулярного направления):
* `inner_le_of_norm_le_one` — `⟨g, u⟩ ≤ ‖g‖` при `‖u‖ ≤ 1`;
* `polar_step_attains` — `u = ‖g‖⁻¹ • g` допустим и достигает `‖g‖`;
* `muon_direction_max` — любой допустимый `u` не лучше ортогонализованного.

Матричная (ядровая) норма не формализована — это общий каркас двойственности.
PrimeCertTrain (`optim.py`, MuonGuards): the polar step is applied only under
three guards — `‖G‖ > ε`, spectral box `‖X‖ ≤ 1049/1024`, `⟨G, X⟩ > 0`.
`MuonGuards`, `guards_sound` (the step `−η·X` is a descent with
`‖Δθ‖ ≤ η·c`), `guards_g_ne_zero`, `polar_guards` (the exact polar step passes
the guards with `c = 1`).
-/

namespace Hagi.Optimization.MuonDual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Двойственность евклидовой нормы: `⟨g, u⟩ ≤ ‖g‖` при `‖u‖ ≤ 1`. -/
theorem inner_le_of_norm_le_one (g u : E) (hu : ‖u‖ ≤ 1) : inner ℝ g u ≤ ‖g‖ := by
  have := real_inner_le_norm g u
  have := this.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg g))
  simpa using this
/-- Ортогонализованный шаг Muon `u = g/‖g‖` — максимизирующий элемент. -/
theorem polar_step_attains (g : E) (hg : g ≠ 0) :
    ‖(‖g‖⁻¹ : ℝ) • g‖ ≤ 1 ∧ inner ℝ g ((‖g‖⁻¹ : ℝ) • g) = ‖g‖ := by
  have hpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
/-- Итог: `max_{‖u‖≤1} ⟨g, u⟩ = ‖g‖` — спектральная (ядровая) норма градиента
достигается ортогонализацией; шаг Muon идёт по направлению максимума. -/
theorem muon_direction_max (g : E) (hg : g ≠ 0) (u : E) (hu : ‖u‖ ≤ 1) :
    inner ℝ g u ≤ inner ℝ g ((‖g‖⁻¹ : ℝ) • g) := by
  rw [(polar_step_attains g hg).2]
  exact inner_le_of_norm_le_one g u hu

/-- Guards PrimeCertTrain (`optim.py`, MuonGuards): `‖G‖ > ε`,
спектральный бокс `‖X‖ ≤ c` (`c = 1049/1024`), `⟨G, X⟩ > 0`. -/
structure MuonGuards (G X : E) (ε c : ℝ) : Prop where
  nonzero : ε < ‖G‖
  spectral : ‖X‖ ≤ c
  descent : 0 < inner ℝ G X
/-- Guard'ы достаточны: шаг `θ ← θ − η·X` — спуск по линейной модели
`⟨G, Δθ⟩ = −η⟨G, X⟩ < 0` и `‖Δθ‖ ≤ η·c` (спектральный бокс ограничивает
длину шага сверху). -/
theorem guards_sound (G X : E) (ε c η : ℝ) (hη : 0 < η) (hc : 0 ≤ c)
    (h : MuonGuards G X ε c) :
    inner ℝ G (-(η • X)) < 0 ∧ ‖η • X‖ ≤ η * c := by
  refine ⟨?_, ?_⟩
  · rw [inner_neg_right, real_inner_smul_right]
    have := mul_pos hη h.descent
    linarith
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    exact mul_le_mul_of_nonneg_left h.spectral hη.le
/-- Guard «не ноль» нужен: при `G = 0` полярный шаг не определён
(`polar_step_attains` требует `g ≠ 0`); `nonzero` гарантирует `G ≠ 0`
при `ε ≥ 0` (порог `eps` в коде положителен). -/
theorem guards_g_ne_zero (G X : E) (ε c : ℝ) (hε : 0 ≤ ε) (h : MuonGuards G X ε c) :
    G ≠ 0 := by
  intro h0
  subst h0
  have := h.nonzero
  rw [show ‖(0:E)‖ = 0 from norm_zero] at this
  linarith
/-- Полярный шаг `X₃ = UVᵀ` (3 шага Polar Express) проходит guard'ы при
`‖G‖ > ε`: `⟨G, X₃⟩ = ‖G‖` для точного полярного шага (`polar_step_attains`)
— положителен; `‖X₃‖ ≤ 1` для матриц. -/
theorem polar_guards (g : E) (ε : ℝ) (hε : 0 ≤ ε) (hg : ε < ‖g‖) :
    MuonGuards g ((‖g‖⁻¹ : ℝ) • g) ε 1 := by
  have hg0 : g ≠ 0 := by
    intro h0
    subst h0
    have := hg
    rw [show ‖(0:E)‖ = 0 from norm_zero] at this
    linarith
  have hp := polar_step_attains g hg0
  exact ⟨hg, hp.1, by rw [hp.2]; exact norm_pos_iff.2 hg0⟩

end Hagi.Optimization.MuonDual
