/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.StageCalculus
import Hagi.Foundations.Recurrence

set_option linter.style.header false

/-!
# Compound — компаундинг прироста за цикл: два аддитивных канала

Модель: прирост цикла `c t ≤ α·G t + J t`, где `G t` —
разногласие свежих листов (ансамблевый канал, сбор с
коэффициентом α), `J t` — собственный прирост joint-шага;
разногласие убывает к уровню пополнения `D`
(ρ-D-закон `Hagi.Foundations.genGap_decay`).

* `compound_c_stabilizes`: при `α·G t + J ≥ c t`,
  `G t ≤ D + (G₀ − D)·a^t` и `a ≤ ε/(α(G₀−D))` —
  `c 1 ≤ α·D + J + ε`;
* `compound_constant_regime`: при `|G t − D| ≤ δ` (t ≥ 1) и
  законе распада — `cG t ≤ α(D + δ) + J`;
* `compound_trajectory`: при `G (t+1) ≤ ρ·G t + D` кумулятивная
  оценка замыкается через замкнутую форму `genGap_decay`;
* `compound_budget`: если `α·D + J ≤ ε_c`, то
  `α·G_next + J ≤ ε_c` для всех `G_next ≤ D`;
* `compound_cumulative`: при `c t ≤ C` —
  `M₀ − Σ c t ≥ M₀ − k·C`;
* `compound_budget_interval` / `compound_fold_interval`:
интервальные версии бюджета (пессимистичный/оптимистичный
конец доверительной области).
-/

namespace Hagi.Step

section Compound

open Hagi

/-- Стабилизация: если `c t ≤ α·G t + J`,
`G t ≤ D + (G₀ − D)·a^t` и `a ≤ ε/(α·(G₀ − D))`, то
`c 1 ≤ α·D + J + ε`. Закон прироста — эмпирическая посылка;
теорема — конечногоризонтный сертификат стабилизации. -/
theorem compound_c_stabilizes (α G0 D a J ε : ℝ) (c G : ℕ → ℝ)
    (hα : 0 < α) (_hJ : 0 ≤ J) (_hD : 0 ≤ D) (hG0D : D < G0)
    (hε : 0 < ε)
    (h_emp_c : ∀ t, c t ≤ α * G t + J)
    (h_emp_gap : ∀ t : ℕ, G t ≤ D + (G0 - D) * a^t)
    (h_emp_decay : a ^ 1 ≤ ε / (α * (G0 - D))) :
    c 1 ≤ α * D + J + ε := by
  have hgap := h_emp_gap 1
  have hclaw := h_emp_c 1
  have hcancel : α * (G0 - D) ≠ 0 := by positivity
  -- α·(G0−D)·a ≤ α·(G0−D)·(ε/(α(G0−D))) = ε
  have hprod : α * ((G0 - D) * a ^ 1) ≤ ε := by
    have hG0Dnn : 0 ≤ G0 - D := by linarith
    have hm : (G0 - D) * a ^ 1 ≤ (G0 - D) * (ε / (α * (G0 - D))) :=
      mul_le_mul_of_nonneg_left h_emp_decay hG0Dnn
    have hleft : α * ((G0 - D) * a ^ 1) ≤ α * ((G0 - D) * (ε / (α * (G0 - D)))) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    have hne : G0 - D ≠ 0 := by linarith
    have hright : α * ((G0 - D) * (ε / (α * (G0 - D)))) = ε := by
      field_simp
    linarith [hleft, hright]
  have hpow : a ^ 1 = a := by ring
  rw [hpow] at hprod
  nlinarith [hgap, hclaw, hprod]

/-- Если `|G t − D| ≤ δ` при `t ≥ 1` и `cG t ≤ α·G t + J`,
то `cG t ≤ α·(D + δ) + J` при `t ≥ 1`. -/
theorem compound_constant_regime (α D J δ : ℝ)
    (hα : 0 ≤ α) (_hD : 0 ≤ D) (_hJ : 0 ≤ J) (_hδ : 0 ≤ δ)
    (G cG : ℕ → ℝ) (hstab : ∀ t, 1 ≤ t → |G t - D| ≤ δ)
    (hdec : ∀ t, cG t ≤ α * G t + J) :
    ∀ t, 1 ≤ t → cG t ≤ α * (D + δ) + J := by
  intro t ht
  have hGle : G t ≤ D + δ := by
    have h1 : G t - D ≤ |G t - D| := le_abs_self _
    have h2 := hstab t ht
    linarith [h1, h2]
  calc cG t ≤ α * G t + J := hdec t
    _ ≤ α * (D + δ) + J := by
        refine add_le_add_left ?_ J
        exact mul_le_mul_of_nonneg_left hGle hα

/-- Если `G (t+1) ≤ ρ·G t + D` и `G 0 ≤ G₀`, то
`Σ_{t<k}(α·G t + J) ≤ Σ_{t<k}(α·(ρ^t·G₀ + D(1−ρ^t)/(1−ρ)) + J)`
(замкнутая форма через `Hagi.Foundations.genGap_decay`). -/
theorem compound_trajectory (ρ D G₀ α J : ℝ)
    (hα : 0 ≤ α) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (G : ℕ → ℝ) (hG0 : G 0 ≤ G₀)
    (hstep : ∀ t, G (t + 1) ≤ ρ * G t + D)
    (k : ℕ) :
    ∑ t ∈ Finset.range k, (α * G t + J)
      ≤ ∑ t ∈ Finset.range k, (α * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + J) := by
  refine Finset.sum_le_sum fun t _ => ?_
  refine add_le_add_left ?_ J
  refine mul_le_mul_of_nonneg_left ?_ hα
  exact Hagi.Foundations.genGap_decay ρ D G₀ hρ hρ1 hD G hG0 hstep t

/-- Если `0 ≤ α` и `α·D + J ≤ ε_c`, то
`α·G_next + J ≤ ε_c` для любого `G_next ≤ D`. -/
theorem compound_budget (α D J ε_c : ℝ)
    (hα : 0 ≤ α) (hpos : α * D + J ≤ ε_c) :
    ∀ (G_next : ℝ), G_next ≤ D → α * G_next + J ≤ ε_c :=
  Hagi.Foundations.compound_budget α D J ε_c hα hpos

/-- При `c t ≤ C` для всех t:
`M₀ − Σ_{t<k} c t ≥ M₀ − k·C`. -/
theorem compound_cumulative (M₀ : ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ t, c t ≤ C) :
    M₀ - ∑ t ∈ Finset.range k, c t ≥ M₀ - k * C := by
  have hsum : ∑ t ∈ Finset.range k, c t ≤ ∑ t ∈ Finset.range k, C := by
    exact Finset.sum_le_sum fun t _ => hstep t
  have hcard : (Finset.range k).card = k := Finset.card_range k
  rw [Finset.sum_const, hcard] at hsum
  have hsmul : k • C = (k : ℝ) * C := by simp
  rw [hsmul] at hsum
  linarith

end Compound



section Interval

/-- Если `0 ≤ αlo`, `0 ≤ Dlo`, `αlo ≤ α`, `Dlo ≤ D` и
`Jlo ≤ J`, то `αlo·Dlo + Jlo ≤ α·D + J` (пессимистичный конец
интервальной оценки). -/
theorem compound_budget_interval (αlo Dlo Jlo _εc : ℝ)
    (α D J : ℝ)
    (hαlo : 0 ≤ αlo) (hDlo : 0 ≤ Dlo)
    (hα : αlo ≤ α) (hD : Dlo ≤ D) (hJ : Jlo ≤ J) :
    αlo * Dlo + Jlo ≤ α * D + J := by
  have hαD : αlo * Dlo ≤ α * D :=
    mul_le_mul hα hD hDlo (le_trans hαlo hα)
  linarith [hαD, hJ]

/-- Если `0 ≤ Dlo`, `0 ≤ αhi`, `α ≤ αhi`, `Dlo ≤ D ≤ Dhi`,
`Jlo ≤ J ≤ Jhi` и `αhi·Dhi + Jhi ≤ εc`, то `α·D + J ≤ εc`
(оптимистичный конец — сертифицированная остановка). -/
theorem compound_fold_interval (αhi Dlo Dhi Jlo Jhi εc : ℝ)
    (α D J : ℝ)
    (hDlo : 0 ≤ Dlo) (_hαlo : 0 ≤ α) (hαhi : 0 ≤ αhi)
    (hα : α ≤ αhi) (hD : Dlo ≤ D ∧ D ≤ Dhi) (hJ : Jlo ≤ J ∧ J ≤ Jhi)
    (hfold : αhi * Dhi + Jhi ≤ εc) :
    α * D + J ≤ εc := by
  have hαD : α * D ≤ αhi * Dhi :=
    mul_le_mul hα hD.2 (le_trans hDlo hD.1) hαhi
  linarith [hαD, hJ.2, hfold]

end Interval

end Hagi.Step

namespace Hagi
export Hagi.Step (compound_c_stabilizes compound_constant_regime compound_trajectory compound_budget compound_cumulative compound_budget_interval compound_fold_interval)
end Hagi
