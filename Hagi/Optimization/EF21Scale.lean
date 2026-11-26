/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Optimization.EF21Quantizer

/-!
# EF21Scale — масштаб тернарного квантователя: фиксированный против адаптивного

Тернарный EF21-квантователь `qTernVec s u` сохраняет только координаты с
`|u i| > s/2`. Alignment `⟨u, Q u⟩` (слагаемое `A` сертифицированного шага)
равен `s · Σ_{|u i| > s/2} |u i|`.

* `qTernVec_inner` — точное тождество alignment.
* `qTernVec_inner_ge` — нижняя граница: `s·‖u‖₁ − card n·s²/2`.
* `qTernVec_freeze` — фиксированный `s` при `‖u‖_∞ < s/2` даёт нулевое
  направление: шаг всегда отклоняется, forward + JVP потрачены впустую.
* `qTernVec_inner_ge_adaptive` — адаптивный `s = ‖u‖_∞/2` сохраняет
  `‖u‖_∞/2·‖u‖₁ − card n·‖u‖_∞²/8` при любом уровне градиента.

* `certifiedDrop_mono`, `qTernVec_certifiedDrop_ge` — сертифицированный drop
  `2A²/R` вдоль квантованного направления не ниже `2(s‖u‖₁ − card n·s²/2)²/R`
  (когда нижняя граница неотрицательна).

Отсюда: масштаб должен пересчитываться на каждом шаге (или сжиматься при
нулевой доле), а не замораживаться на первом.
-/

namespace Hagi.Optimization.EF21Quantizer

open Finset

variable {n : Type*} [Fintype n]

/-- Вклад координаты: `s·|x|` при `|x| > s/2`, иначе `0`. -/
theorem qTernVec_coord (s x : ℝ) (hs : 0 < s) :
    x * (s * ((roundTern (x / s) : ℝ))) = if s / 2 < |x| then s * |x| else 0 := by
  unfold roundTern
  by_cases h1 : 1 / 2 < x / s
  · have hx : s / 2 < x := by have := (lt_div_iff₀ hs).1 h1; linarith
    have hxp : 0 < x := by linarith
    rw [ite_eq_left h1]
    rw [ite_eq_left (by rw [abs_of_pos hxp]; exact hx), abs_of_pos hxp]
    push_cast; ring
  · rw [ite_eq_right h1]
    by_cases h2 : x / s < -1 / 2
    · have hx : x < -s / 2 := by have := (div_lt_iff₀ hs).1 h2; linarith
      have hxn : x < 0 := by linarith
      rw [ite_eq_left h2]
      rw [ite_eq_left (by rw [abs_of_neg hxn]; linarith), abs_of_neg hxn]
      push_cast; ring
    · rw [ite_eq_right h2]
      have hlo : -1 / 2 ≤ x / s := not_lt.1 h2
      have hhi : x / s ≤ 1 / 2 := not_lt.1 h1
      have hlo' : -s / 2 ≤ x := by have := (le_div_iff₀ hs).1 hlo; linarith
      have hhi' : x ≤ s / 2 := by have := (div_le_iff₀ hs).1 hhi; linarith
      rw [ite_eq_right (by rw [not_lt]; exact abs_le.2 ⟨by linarith, hhi'⟩)]
      push_cast; ring
/-- Alignment — сохранённая масса: `⟨u, Q u⟩ = s · Σ_{|u i| > s/2} |u i|`. -/
theorem qTernVec_inner (s : ℝ) (hs : 0 < s) (u : n → ℝ) :
    ∑ i, u i * qTernVec s u i = s * ∑ i, (if s / 2 < |u i| then |u i| else 0) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    show u i * (s * ((roundTern (u i / s) : ℝ))) = s * _
    rw [qTernVec_coord s (u i) hs]
    by_cases h : s / 2 < |u i| <;> simp [h]
/-- Потерянная масса: каждая координата теряет не более `s/2`, итого `card n · s/2`. -/
theorem qTernVec_loss_le (s : ℝ) (hs : 0 ≤ s) (u : n → ℝ) :
    ∑ i, (|u i| - (if s / 2 < |u i| then |u i| else 0)) ≤ (Fintype.card n : ℝ) * (s / 2) := by
  have h1 : ∀ i, |u i| - (if s / 2 < |u i| then |u i| else 0) ≤ s / 2 := by
    intro i
    by_cases h : s / 2 < |u i|
    · simp only [ite_eq_left h, sub_self]; positivity
    · simp only [ite_eq_right (by linarith : ¬ s / 2 < |u i|), sub_zero]; linarith [(not_lt.1 h)]
  calc ∑ i, (|u i| - (if s / 2 < |u i| then |u i| else 0))
      ≤ ∑ i, (s / 2) := Finset.sum_le_sum fun i _ => h1 i
    _ = (Fintype.card n : ℝ) * (s / 2) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
/-- Alignment снизу: `⟨u, Q u⟩ ≥ s·‖u‖₁ − card n · s²/2`. -/
theorem qTernVec_inner_ge (s : ℝ) (hs : 0 < s) (u : n → ℝ) :
    s * (∑ i, |u i|) - (Fintype.card n : ℝ) * s * s / 2 ≤ ∑ i, u i * qTernVec s u i := by
  have hloss := mul_le_mul_of_nonneg_left (qTernVec_loss_le s hs.le u) hs.le
  have hid : s * (∑ i, (if s / 2 < |u i| then |u i| else 0)) =
      s * (∑ i, |u i|) - s * ∑ i, (|u i| - (if s / 2 < |u i| then |u i| else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : s / 2 < |u i| <;> simp [h]
  rw [qTernVec_inner s hs u, hid]
  have h2 : s * ((Fintype.card n : ℝ) * (s / 2)) = (Fintype.card n : ℝ) * s * s / 2 := by ring
  linarith
/-- Fixed-scale freeze: если `‖u‖_∞ < s/2`, квантованное направление нулевое и alignment `0`. -/
theorem qTernVec_freeze (s : ℝ) (hs : 0 < s) (u : n → ℝ) (h : ∀ i, |u i| < s / 2) :
    ∑ i, u i * qTernVec s u i = 0 := by
  rw [qTernVec_inner s hs u]
  rw [Finset.sum_eq_zero fun i _ => ite_eq_right (not_lt.2 (le_of_lt (h i))), mul_zero]
/-- Adaptive scale `s = ‖u‖_∞/2`: alignment не меньше `(1/2)·‖u‖_∞·‖u‖₁ − card n·‖u‖_∞²/8`;
для fixed `s` при `‖u‖_∞ < s/2` alignment нулевой (предыдущая теорема). -/
theorem qTernVec_inner_ge_adaptive (u : n → ℝ) (M : ℝ) (hM : 0 < M) :
    M / 2 * (∑ i, |u i|) - (Fintype.card n : ℝ) * M * M / 8 ≤ ∑ i, u i * qTernVec (M / 2) u i := by
  have hs : 0 < M / 2 := by linarith
  have := qTernVec_inner_ge (M / 2) hs u
  have h2 : (Fintype.card n : ℝ) * (M / 2) * (M / 2) / 2 = (Fintype.card n : ℝ) * M * M / 8 := by ring
  rw [h2] at this
  exact this

/-- Сертифицированное снижение range-based шага вдоль направления с alignment `A`. -/
noncomputable def certifiedDrop (A R : ℝ) : ℝ := 2 * A ^ 2 / R
/-- Drop монотонен по alignment при положительном диапазоне. -/
theorem certifiedDrop_mono (A A' R : ℝ) (hR : 0 < R) (h : 0 ≤ A) (hA : A ≤ A') :
    certifiedDrop A R ≤ certifiedDrop A' R := by
  unfold certifiedDrop
  have hsq : A ^ 2 ≤ A' ^ 2 := pow_le_pow_left₀ h hA 2
  have : 2 * A ^ 2 ≤ 2 * A' ^ 2 := by linarith
  exact div_le_div_of_nonneg_right this hR.le
/-- Сертифицированный drop EF21-шага: `A = ⟨m, Q m⟩ ≥ s‖m‖₁ − card n·s²/2`. -/
theorem qTernVec_certifiedDrop_ge {n : Type*} [Fintype n] (s R : ℝ) (hs : 0 < s) (hR : 0 < R)
    (u : n → ℝ)
    (h0 : 0 ≤ s * (∑ i, |u i|) - (Fintype.card n : ℝ) * s * s / 2) :
    certifiedDrop (s * (∑ i, |u i|) - (Fintype.card n : ℝ) * s * s / 2) R ≤
      certifiedDrop (∑ i, u i * qTernVec s u i) R :=
  certifiedDrop_mono _ _ _ hR h0 (qTernVec_inner_ge s hs u)

end Hagi.Optimization.EF21Quantizer
