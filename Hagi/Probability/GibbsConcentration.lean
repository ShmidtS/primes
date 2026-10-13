/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

/-!
# Концентрация меры Гиббса при T → 0 (R386)

Термодинамический закон для обучения: при температуре T
распределение Гиббса p_T(v) ∝ exp(−E(v)/T) концентрируется
на глобальном минимуме энергии при охлаждении T → 0⁺ —
фундамент simulated annealing, temperature scaling и
softmax-охлаждения в обучении HAGI.

Формально: при δ-зазоре (E(v*) + δ ≤ E(v) для всех
конкурентов) доля веса минимума

  e^{−E*/T} / Σ_v e^{−E(v)/T}  ≥  1 − (|V|−1)·e^{−δ/T}.

Маршрут: сдвиг энергий (доля = 1/(1+S), S — сумма весов
конкурентов относительно e^{−E*/T}), S ≤ (n−1)e^{−δ/T}
(поточечная экспоненциальная оценка), и 1/(1+x) ≥ 1−x.

Связь с вертикалью: ThermoAxes (оси охлаждения) +
GibbsConcentration (куда сходится охлаждение) —
термодинамический каркас обучения. -/
open Finset Real

theorem gibbs_concentration {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ : ℝ) (vstar : V)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (T : ℝ) (hT : 0 < T) :
    Real.exp (-(E vstar) / T) / ∑ v, Real.exp (-(E v) / T)
      ≥ 1 - ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T) := by
  -- shift energies: numerator/denominator divided by e^{-E*/T}
  have hpos : (0:ℝ) < ∑ v, Real.exp (-(E v) / T) :=
    Finset.sum_pos (fun v _ => exp_pos _) (⟨Classical.arbitrary V, Finset.mem_univ _⟩)
  -- denominator = e^{-E*/T} * (1 + S), S = sum over competitors
  set S : ℝ := ∑ v ∈ Finset.univ.erase vstar,
      Real.exp (-(E v - E vstar) / T) with hS
  have hden : ∑ v, Real.exp (-(E v) / T)
      = Real.exp (-(E vstar) / T) * (1 + S) := by
    have hsplit : ∑ v, Real.exp (-(E v) / T)
        = ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v) / T)
          + Real.exp (-(E vstar) / T) := by
      rw [Finset.sum_erase_add (Finset.univ : Finset V)
        (fun v => Real.exp (-(E v) / T))
        (Finset.mem_univ vstar)]
    rw [hsplit]
    have hfact : ∑ v ∈ Finset.univ.erase vstar,
        Real.exp (-(E v) / T)
        = Real.exp (-(E vstar) / T) * S := by
      calc ∑ v ∈ Finset.univ.erase vstar, Real.exp (-(E v) / T)
          = ∑ v ∈ Finset.univ.erase vstar,
              Real.exp (-(E vstar) / T)
                * Real.exp (-(E v - E vstar) / T) :=
            Finset.sum_congr rfl (fun v _ => by
              rw [← Real.exp_add]
              congr 1
              field_simp
              ring)
        _ = Real.exp (-(E vstar) / T) * S := by
            rw [Finset.mul_sum]
    rw [hfact]
    ring
  -- bound S
  have hSpos : (0:ℝ) ≤ S := Finset.sum_nonneg
    (fun v _ => le_of_lt (exp_pos _))
  have hSbound : S ≤ ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) := by
    have hterm : ∀ v ∈ Finset.univ.erase vstar,
        Real.exp (-(E vstar + δ - E vstar) / T)
          = Real.exp (-δ / T) := by
      intro v _
      congr 1
      congr 1
      ring
    calc S ≤ ∑ v ∈ Finset.univ.erase vstar,
          Real.exp (-(E vstar + δ - E vstar) / T) := by
          refine Finset.sum_le_sum ?_
          intro v hv
          have hvne : v ≠ vstar := (Finset.mem_erase.mp hv).1
          have hE : E vstar + δ - E vstar ≤ E v - E vstar :=
            by
            have := hgap v hvne
            linarith
          exact Real.exp_le_exp.mpr (by
            rw [div_le_div_iff₀ hT hT]
            nlinarith [hT])
      _ = ∑ v ∈ Finset.univ.erase vstar,
          Real.exp (-δ / T) :=
            Finset.sum_congr rfl (fun v hv => hterm v hv)
      _ = ((Finset.univ.erase vstar).card : ℝ)
          * Real.exp (-δ / T) := by
          rw [Finset.sum_const]
          norm_num
  -- final: share = 1/(1+S) >= 1 - card*e^{-δ/T}
  set Ce : ℝ := ((Finset.univ.erase vstar).card : ℝ)
      * Real.exp (-δ / T) with hCe
  have hCenn : (0:ℝ) ≤ Ce := mul_nonneg
    (by positivity) (le_of_lt (exp_pos _))
  have hdiv : Real.exp (-(E vstar) / T)
      / (Real.exp (-(E vstar) / T) * (1 + S)) = 1 / (1 + S) := by
    field_simp
  rw [hden, hdiv]
  have hmono1 : 1 / (1 + Ce) ≤ 1 / (1 + S) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hmono2 : 1 - Ce ≤ 1 / (1 + Ce) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 + Ce)]
    nlinarith [mul_self_nonneg Ce]
  exact hmono2.trans hmono1

