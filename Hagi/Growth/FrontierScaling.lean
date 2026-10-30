/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainRenewal
import Hagi.Foundations.ConeTakeoff
import Hagi.Foundations.GrowthBand
set_option linter.style.header false

/-!
# FrontierScaling — конус-инвариант из производственной динамики

Фронтир (usable disagreement) D и capability C связаны
посылками: динамика производства `D (t+1) ≥ ρ·D t + β·C t − ξ t`,
кап на рост `C (t+1) ≤ (1+α)·C t`, конус в нуле и порог на `β`.

  пороге `(α/γ)·((1+α) − ρ) + ξ t / C t ≤ β` (нужно `0 < C t`);
(Конусный шаг/инвариант перенесён в Foundations/ConeTakeoff — R326.)
* `takeoff_edge_forced`: при точном шаге, gain-законе, конусе
  и капе выполнены тождества `G = α·C`, `D = (α/γ)·C`,
  `C' = (1+α)·C` — модель ПОЛНОСТЬЮ НАСЫЩЕННОГО режима
  (одновременные нижняя и верхняя границы роста): точное
  равенство каждой итерации. Это не устойчивая гарантия для
  произвольного обучения с шумом — вне насыщения применять
  нельзя (оговорка внешнего аудита);
* `sustained_takeoff_from_production`: из указанных посылок —
  `C 0 * (1 + α) ^ T ≤ C T` для всех T (без свободной
  гипотезы «α·C ≤ γ·D»: ворота выводятся из конуса);
* `frontier_asymptotic`: если `ξ t ≤ ξ̄·C t`, порог стягивается
  к константе `(α/γ)·((1+α) − ρ) + ξ̄ ≤ β` и выводится тот же
  takeaway.

Эмпирическое содержание — сами посылки (динамика, порог).
-/

open Real Finset

namespace Hagi.Growth

/-! ## The cone step -/

/-- При `0 < γ`, точном шаге `C (t+1) = C t + G t`,
gain-законе `γ·D t ≤ G t`, конусе `α/γ·C t ≤ D t` и капе
`C (t+1) ≤ (1+α)·C t` выполнены тождества
`G t = α·C t`, `D t = α/γ·C t` и `C (t+1) = (1+α)·C t`. -/
theorem takeoff_edge_forced (C G D : ℕ → ℝ) (α γ : ℝ)
    (hγ : 0 < γ)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_cone : ∀ t, α / γ * C t ≤ D t)
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (t : ℕ) :
    G t = α * C t ∧ D t = α / γ * C t
      ∧ C (t + 1) = (1 + α) * C t := by
  have hg := h_gain_prod t
  have hc := h_cone t
  have hcap := h_C_cap t
  have hstep := h_step t
  have he : γ * (α / γ * C t) = α * C t := by
    field_simp
  -- конус ⇒ α·C ≤ G
  have hchain : α * C t ≤ G t := by
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left hc hγ.le
    rw [he] at h1
    exact le_trans h1 hg
  -- зажатие C' = (1+α)C
  have hkey : C t + G t = (1 + α) * C t := by
    have hring : (1 + α) * C t = C t + α * C t := by ring
    have hlow : (1 + α) * C t ≤ C t + G t := by
      rw [hring]
      linarith [hchain]
    linarith [hlow]
  -- G = αC
  have hGeq : G t = α * C t := by
    have hring : (1 + α) * C t = C t + α * C t := by ring
    linarith [hkey, hring]
  -- γD = αC (зажато с двух сторон) ⇒ D = (α/γ)C
  have hpin : γ * D t = α * C t := by
    rw [hGeq] at hg
    exact le_antisymm hg
      (by rw [← he]; exact mul_le_mul_of_nonneg_left hc hγ.le)
  have hDeq : D t = α / γ * C t := by
    field_simp
    linarith [hpin]
  exact ⟨hGeq, hDeq, hstep ▸ hkey⟩

/-- Вспомогательная (private): при `0 < C 0`, конусе в нуле,
точном шаге, gain-законе, динамике, капе и пороге (при каждом
t, с `0 < C t`) выполнено `0 < C t ∧ α/γ·C t ≤ D t` при всех t.
Позитивность и конус доказываются совместно: порог делит на
`C t`, а позитивность `C (t+1)` следует из конуса при t. -/
private theorem cone_and_pos (C G D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0) (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, 0 < C t → α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, 0 < C t ∧ α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨hC0, h_cone0⟩
  | succ t ih =>
      obtain ⟨hpos, hcone⟩ := ih
      -- the gate at t from the cone: α·C_t = γ·(k·C_t) ≤ γ·D_t ≤ G_t
      have hg : γ * (α / γ * C t) ≤ G t :=
        le_trans (mul_le_mul_of_nonneg_left hcone hγ.le) (h_gain_prod t)
      have e : γ * (α / γ * C t) = α * C t := by
        field_simp
      rw [e] at hg
      have hA : 0 < α * C t := by positivity
      refine ⟨?_, Hagi.Foundations.frontier_cone_inductive C D ξ α γ ρ β hα hγ hρ t
        hpos hcone (h_dyn t) (h_C_cap t) (hβ t hpos)⟩
      rw [h_step t]
      linarith

/-- При `0 < α`, `0 < γ`, `0 ≤ ρ`, `0 < C 0`, конусе в нуле,
точном шаге `C (t+1) = C t + G t`, gain-законе `γ·D t ≤ G t`,
динамике `ρ·D t + β·C t − ξ t ≤ D (t+1)`, капе
`C (t+1) ≤ (1+α)·C t` и пороге
`α/γ·((1+α) − ρ) + ξ t / C t ≤ β` выводится
`C 0 * (1 + α) ^ T ≤ C T` для всех `T`: ворота
`α·C t ≤ γ·D t` выводятся из конус-инварианта и применяется
`renewal_feeds_takeoff`. -/
theorem sustained_takeoff_from_production (C G D ξ : ℕ → ℝ)
    (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap (fun t _ => hβ t)
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone := Hagi.Foundations.frontier_cone_invariant C D ξ α γ ρ β hα hγ hρ hCpos
    h_cone0 h_dyn h_C_cap hβ
  -- the gate, DERIVED from the cone: α·C_t = γ·((α/γ)·C_t) ≤ γ·D_t
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

/-! ## The asymptotic (constant-threshold) corollary -/

/-- Версия `sustained_takeoff_from_production` с постоянным
порогом: если дополнительно `ξ t ≤ ξ̄·C t` при всех t и
`α/γ·((1+α) − ρ) + ξ̄ ≤ β`, то `C 0 * (1 + α) ^ T ≤ C T`. -/
theorem frontier_asymptotic (C G D ξ : ℕ → ℝ)
    (α γ ρ β ξbar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (h_xibar : ∀ t, ξ t ≤ ξbar * C t)
    (h_beta_const : α / γ * ((1 + α) - ρ) + ξbar ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap
      (fun t ht => by
        have h := (div_le_iff₀ ht).mpr (h_xibar t)
        linarith [h, h_beta_const])
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone : ∀ t, α / γ * C t ≤ D t := fun t => (hcp t).2
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

end Hagi.Growth


namespace Hagi
export Hagi.Growth (takeoff_edge_forced sustained_takeoff_from_production frontier_asymptotic)
export Hagi.Foundations.GrowthBand (growth_band_step growth_band_iter)
end Hagi
