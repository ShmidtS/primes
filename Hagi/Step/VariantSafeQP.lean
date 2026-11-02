/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Step.SafeQP
import Hagi.Probability.KLSBridge

/-!
# Варианты SafeQP (объединённые)

Метрический SafeQP и KLS-SafeQP. Слит из двух модулей;
имена деклараций сохранены.
-/

set_option linter.style.header false

/-!
# SafeQP в метрике M

Проекция кандидата d₀ на допустимое множество
`⟪g_i, d⟫ ≥ −ε_i` в метрике d ↦ ‖A d‖ (симметричная
положительно определённая M = AᵀA при самосопряжённом
положительном A).

Существование и единственность сводятся к евклидову SafeQP
заменой координат y = A d: M-проекция d* = A⁻¹ y*, где y* —
евклидова проекция A d₀ на transported-множество с
градиентами (A⁻¹)† g_i.

Утверждений о спуске для исходной цели здесь нет:
метрическая геометрия и геометрия цели независимы —
условие спуска остаётся явной посылкой.
-/

open Real Finset InnerProductSpace InnerProduct

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {K : Type*} [Fintype K]

/-- M-метрика, заданная невырожденным носителем A:
‖d − e‖_M := ‖A (d − e)‖. -/
def mDist (A : X ≃L[ℝ] X) (d e : X) : ℝ := ‖A (d - e)‖

/-- Транспортированные градиенты: (A⁻¹)† g_i. -/
noncomputable def transportedGrad (A : X ≃L[ℝ] X) (g : K → X) : K → X :=
  fun i => ((A.symm : X →L[ℝ] X)†) (g i)

/-- Ключевой транспорт: в координатах y = A d допустимость
задаётся транспонированными градиентами (A⁻¹)† g_i:
y ∈ safeSet(transportedGrad) ↔ A⁻¹ y ∈ safeSet g. -/
theorem inner_transport (A : X ≃L[ℝ] X) (g : K → X) (eps : K → ℝ)
    (y : X) :
    y ∈ Hagi.safeSet (transportedGrad A g) eps ↔
      A.symm y ∈ Hagi.safeSet g eps := by
  unfold transportedGrad Hagi.safeSet
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    have h1 := h i
    have hid : ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ
        = ⟪g i, A.symm y⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)
    rwa [hid] at h1
  · intro h i
    have h1 := h i
    have hid : ⟪g i, A.symm y⟫_ℝ
        = ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)).symm
    rwa [hid] at h1

/-- mDist в координатах y = A d — евклидово расстояние. -/
theorem mDist_eq (A : X ≃L[ℝ] X) (e d0 : X) :
    mDist A e d0 = dist (A e) (A d0) := by
  unfold mDist
  have h1 : e - d0 = A.symm (A e) - A.symm (A d0) := by
    rw [A.symm_apply_apply, A.symm_apply_apply]
  rw [h1, A.map_sub]
  simp only [A.apply_symm_apply, A.apply_symm_apply]
  simp [dist_eq_norm]

/-- Существование и единственность M-проекции: при
неотрицательных ε и невырожденном A M-проекция
существует и единственна — сведение к евклидову SafeQP
в координатах y = A d. -/
theorem mProject_exists_unique (A : X ≃L[ℝ] X)
    (g : K → X) (eps : K → ℝ) (heps : ∀ i, 0 ≤ eps i) (d0 : X) :
    ∃! d : X, d ∈ Hagi.safeSet g eps ∧
      ∀ e ∈ Hagi.safeSet g eps,
        mDist A d d0 ≤ mDist A e d0 := by
  obtain ⟨y, ⟨hy, hymin⟩, hyuni⟩ :=
    Hagi.safeQP_exists_unique (transportedGrad A g) (A d0) eps heps
  have hdy : mDist A (A.symm y) d0 = dist y (A d0) := by
    rw [mDist_eq A (A.symm y) d0, A.apply_symm_apply]
  refine ⟨A.symm y, ⟨?_, ?_⟩, ?_⟩
  · exact (inner_transport A g eps y).mp hy
  · intro e he
    have hAe : A e ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A e)).mpr
        (show A.symm (A e) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hmin := hymin (A e) hAe
    have hde : mDist A e d0 = dist (A e) (A d0) := mDist_eq A e d0
    rw [hdy, hde]
    exact hmin
  · intro d ⟨hd, hdmin⟩
    have hAd : A d ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A d)).mpr
        (show A.symm (A d) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hAmin : ∀ z ∈ Hagi.safeSet (transportedGrad A g) eps,
        dist (A d) (A d0) ≤ dist z (A d0) := by
      intro z hz
      have hz' : A.symm z ∈ Hagi.safeSet g eps :=
        (inner_transport A g eps z).mp hz
      have hmin := hdmin (A.symm z) hz'
      have hz1 : mDist A (A.symm z) d0 = dist z (A d0) := by
        rw [mDist_eq A (A.symm z) d0, A.apply_symm_apply]
      have hd1 : mDist A d d0 = dist (A d) (A d0) := mDist_eq A d d0
      rw [hd1, hz1] at hmin
      exact hmin
    have heq : A d = y := hyuni (A d) ⟨hAd, hAmin⟩
    calc d = A.symm (A d) := (A.symm_apply_apply d).symm
      _ = A.symm y := by rw [heq]

end Hagi.Step

set_option linter.style.header false

/-!
# KLSSafeQP — композиция KLS/Poincaré-шума с SafeQP-запасом

Цепочка: KLS/Poincaré ограничивает дисперсию проекции
минибатча `V = C·L²·‖a‖²/B`; Chebyshev даёт событие
q-вероятности ≥ 1 − V/t². Теорема `klsSafeQP_certified`:
при истинном запасе `ε + |gd|·t` и той же оценке V
зашумлённая проверка сертифицирует ε на событии
q-массы ≥ 1 − V/t².
-/

namespace Hagi.Step

open Finset

/-- При статистических посылках KLS (Poincaré,
чувствительность, некоррелированность батча), точной
девиации `estInner − trueInner` (hdev), `0 < t` и запасе
`ε + |gd|·t ≤ gd·trueInner x` для всех x —
множество `{x | ε ≤ gd·estInner x}` имеет q-массу
≥ 1 − (C·L²·‖a‖²/B)/t². -/
theorem klsSafeQP_certified {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (C L : ℝ) (hC : 0 ≤ C)
    (sens : (Fin n → ℝ) → Ω → ℝ)
    (hpoincare : ∀ (g : Ω → Fin n → ℝ) (a : Fin n → ℝ),
      Probability.gradVar q g a ≤ C * Probability.expQ q (fun x => (sens a x) ^ 2))
    (hop : ∀ (a : Fin n → ℝ) (x : Ω), (sens a x) ^ 2 ≤ L ^ 2 * Probability.sqN a)
    {B : ℕ} (hB : 0 < B) (g : Fin B → Ω → Fin n → ℝ) (a : Fin n → ℝ)
    (huncorr : ∀ i j, i ≠ j →
      Probability.expQ q (fun x => (Probability.proj a (g i x)
          - Probability.expQ q (fun y => Probability.proj a (g i y)))
        * (Probability.proj a (g j x)
          - Probability.expQ q (fun y => Probability.proj a (g j y)))) = 0)
    (trueInner : Ω → ℝ) (estInner : Ω → ℝ)
    (hdev : ∀ x, estInner x - trueInner x
      = (∑ i, Probability.proj a (g i x) / B
          - (∑ i, Probability.expQ q (fun y => Probability.proj a (g i y))) / B))
    (gd : ℝ) (eps t : ℝ) (ht : 0 < t)
    (htrue : ∀ x, eps + |gd| * t ≤ gd * trueInner x) :
    (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ 1 - (C * L ^ 2 * Probability.sqN a / B) / t ^ 2 := by
  -- the deviation field
  set dev : Ω → ℝ := fun x => ∑ i, Probability.proj a (g i x) / B
    - (∑ i, Probability.expQ q (fun y => Probability.proj a (g i y))) / B with hdevdef
  -- the KLS chain bounds its second moment
  set V := C * L ^ 2 * Probability.sqN a / B with hVdef
  have hnoise : Probability.expQ q (fun x => (dev x) ^ 2) ≤ V :=
    Probability.klsBatchNoise q hq0 hq1 C L hC sens hpoincare hop hB g a huncorr
  -- Chebyshev: the bad set has q-mass at most V / t^2
  have hbad : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      ≤ V / t ^ 2 :=
    Probability.klsChebyshev q hq0 V t ht dev hnoise
  -- the certified set contains the complement of the bad set
  have hmono : (Finset.univ.filter (fun x => ¬(t ≤ |dev x|)))
      ⊆ Finset.univ.filter (fun x => eps ≤ gd * estInner x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ x, ?_⟩
    have hlt : |dev x| < t := by
      by_contra hcon
      exact absurd (le_of_not_gt hcon) hx.2
    have hest : estInner x = trueInner x + dev x := by
      have h1 := hdev x
      linarith [h1]
    -- |dev x| <= t (non-strict is enough with a strict margin)
    have habsdev : |dev x| ≤ t := le_of_lt hlt
    -- |gd| * |dev x| <= |gd| * t
    have hbnd : |gd| * |dev x| ≤ |gd| * t :=
      mul_le_mul_of_nonneg_left habsdev (abs_nonneg gd)
    -- chain
    rw [hest]
    have htr := htrue x
    have hkey : |gd| * |dev x| ≤ |gd| * t := hbnd
    have hsplit : gd * dev x ≥ -(|gd| * t) := by
      have hEq : |gd * dev x| = |gd| * |dev x| := abs_mul gd (dev x)
      have h0 := neg_le_abs (gd * dev x)
      linarith [hkey, h0, hEq]
    nlinarith [htr, hsplit, abs_nonneg gd]
  -- the two filters partition the mass
  have hpart : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      + (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      = ∑ x, q x := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- the certified mass dominates the complement's mass
  have hdom : (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      ≤ (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h1 : ¬(t ≤ |dev x|)
    · have hmem : x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, h1⟩
      have hgood := hmono hmem
      rw [Finset.mem_filter] at hgood
      rw [ite_eq_left h1, ite_eq_left hgood.2]
    · by_cases h2 : eps ≤ gd * estInner x
      · rw [ite_eq_right h1, ite_eq_left h2]
        exact hq0 x
      · rw [ite_eq_right h1, ite_eq_right h2]
  -- assemble
  calc (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x) := hdom
    _ = 1 - (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x) := by
        rw [hq1] at hpart
        linarith
    _ ≥ 1 - V / t ^ 2 := by
        linarith [hbad]
end Hagi.Step
