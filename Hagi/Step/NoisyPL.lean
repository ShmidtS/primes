/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# Noisy PL-контур: сходимость до окрестности радиуса O(m²/μ)

Замыкание моста MEASURE -> PROPOSE -> CONVERGE. Шаг по
неточному градиенту `ĝ` (‖ĝ − g‖ ≤ m) с `η = 1/(8L)` даёт
сертифицированное убывание `E⁺ ≤ E − (‖g‖² − 3m²)/(32L)`:
спуск работает, пока сигнал сильнее порога `√3·m`. С
PL-условием `2μ(E−E*) ≤ ‖g‖²` это даёт рекуррентность

`e⁺ ≤ (1 − μ/(16L))·e + 3m²/(32L)`,

телескоп которой останавливается на **радиусе шума**

`E_t − E* ≤ (1 − μ/(16L))^t·(E₀ − E*) + 3m²/(2μ)`.

Литература: worst-case анализ inexact GD (PEP, Vernimmen–
Glineur 2025, doi 10.1016/j.neucom.2025.131883); Tadić 2009
(Łojasiewicz + шум); Bertsekas (gradient method with errors).
Ключевой вывод для архитектуры: точность обучения
ограничена отношением сигнал/шум измерений — бюджет
измерений (батч/Dust) надо наращивать синхронно с
приближением к оптимуму; certified-stop: как только
geometric член сравнялся с 3m²/(2μ), дальнейшие шаги
не улучшают гарантию.
-/

namespace Hagi.Step

/-- Телескоп шумовой рекуррентности: если
`e (t+1) ≤ c·e t + d` с `0 ≤ c < 1`, `0 ≤ d`, то
`e t ≤ c^t·e 0 + d/(1−c)`. -/
theorem noisy_recurrence_telescope (e : ℕ → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (hc1 : c < 1) (hd : 0 ≤ d)
    (hstep : ∀ t, e (t + 1) ≤ c * e t + d)
    (e₀ : ℝ) (h0 : e 0 ≤ e₀) (t : ℕ) :
    e t ≤ c ^ t * e₀ + d / (1 - c) := by
  induction t with
  | zero =>
    have hpos : (0:ℝ) ≤ d / (1 - c) := by positivity
    show e 0 ≤ (1:ℝ) * e₀ + d / (1 - c)
    linarith
  | succ t ih =>
    have hdd : d * (1 - c) / (1 - c) = d := by
      field_simp
    have h1 : c ^ (t + 1) * e₀ + d / (1 - c)
        = c * (c ^ t * e₀ + d / (1 - c))
          + d * (1 - c) / (1 - c) := by
      rw [pow_succ]
      field_simp
      ring
    have hmul : c * e t ≤ c * (c ^ t * e₀ + d / (1 - c)) :=
      mul_le_mul_of_nonneg_left ih hc
    calc e (t + 1) ≤ c * e t + d := hstep t
      _ ≤ c * (c ^ t * e₀ + d / (1 - c))
          + d * (1 - c) / (1 - c) := by
          rw [hdd]
          linarith
      _ ≤ c ^ (t + 1) * e₀ + d / (1 - c) := by
          rw [h1]

/-- ГЛАВНАЯ ТЕОРЕМА: noisy PL-сходимость. При
noisy-шаге `E⁺ ≤ E − (‖g‖² − 3m²)/(32L)` (в терминах
G t := ‖g t‖²), PL-доминировании `2μ e ≤ G` и
сигнале `3m² ≤ G t` на всех шагах:
`e t ≤ (1 − μ/(16L))^t·e 0 + 3m²/(2μ)`. -/
theorem noisy_pl_convergence (e G : ℕ → ℝ) (Estar μ L m : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) (hm : 0 ≤ m)
    (he : ∀ t, Estar ≤ e t)
    (hstep : ∀ t, e (t + 1) ≤ e t - (G t - 3 * m ^ 2) / (32 * L))
    (hPL : ∀ t, 2 * μ * (e t - Estar) ≤ G t)
    (hsig : ∀ t, 3 * m ^ 2 ≤ G t)
    (t : ℕ) :
    e t ≤ Estar + (1 - μ / (16 * L)) ^ t * (e 0 - Estar)
      + 3 * m ^ 2 / (2 * μ) := by
  -- рекуррентность: e⁺ ≤ (1 − μ/(16L))·e + 3m²/(32L)·... выведем
  have hrec : ∀ t, e (t + 1) ≤ (1 - μ / (16 * L)) * (e t - Estar)
      + Estar + 3 * m ^ 2 / (32 * L) := by
    intro t
    have hst := hstep t
    have hPLt := hPL t
    have hsig_t := hsig t
    have hge : G t - 3 * m ^ 2 ≥ 0 := by linarith
    -- (G − 3m²)/(32L) ≥ μ/(16L)·(e − Estar) − 3m²/(32L)
    have hsplit : (G t - 3 * m ^ 2) / (32 * L)
        ≥ μ / (16 * L) * (e t - Estar)
          - 3 * m ^ 2 / (32 * L) := by
      have hG1 : 2 * μ * (e t - Estar) - 3 * m ^ 2
          ≤ G t - 3 * m ^ 2 := by linarith
      have hG2 : (2 * μ * (e t - Estar) - 3 * m ^ 2) / (32 * L)
          ≤ (G t - 3 * m ^ 2) / (32 * L) := by
        exact div_le_div_of_nonneg_right hG1 (by positivity)
      have hEq : μ / (16 * L) * (e t - Estar)
          - 3 * m ^ 2 / (32 * L)
          = (2 * μ * (e t - Estar) - 3 * m ^ 2) / (32 * L) := by
        have h32 : (32 * L : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [hEq]
      exact hG2
    have hadd : e t - (G t - 3 * m ^ 2) / (32 * L)
        ≤ e t - (μ / (16 * L) * (e t - Estar)
          - 3 * m ^ 2 / (32 * L)) := by
      have := hsplit
      linarith
    linarith [hst, hadd]
  -- сдвиг к стационарной форме
  have hshift : ∀ t, (e (t + 1) - Estar)
      ≤ (1 - μ / (16 * L)) * (e t - Estar)
        + 3 * m ^ 2 / (32 * L) := by
    intro t
    have := hrec t
    linarith
  -- телескоп на e − Estar
  have htelescope : ∀ t, (e t - Estar)
      ≤ (1 - μ / (16 * L)) ^ t * (e 0 - Estar)
        + (3 * m ^ 2 / (32 * L)) / (μ / (16 * L)) := by
    intro t
    have := noisy_recurrence_telescope
      (fun k => e k - Estar) (1 - μ / (16 * L))
      (3 * m ^ 2 / (32 * L))
      (by
        have h16 : μ / (16 * L) ≤ 1 / 16 := by
          have hform : μ / (16 * L) = μ / L / 16 := by
            field_simp
          rw [hform]
          have h1 : μ / L ≤ 1 := by
            rw [div_le_one hL]; exact hμL
          exact div_le_div_of_nonneg_right h1 (by positivity)
        linarith)
      (by
        have hpos : (0:ℝ) < μ / (16 * L) :=
          div_pos hμ (by positivity)
        linarith)
      (by positivity)
      hshift (e 0 - Estar)
      (le_refl _) t
    have hden : (1:ℝ) - (1 - μ / (16 * L)) = μ / (16 * L) := by ring
    rw [hden] at this
    exact this
  have hfinal := htelescope t
  have hfrac : (3 * m ^ 2 / (32 * L)) / (μ / (16 * L))
      = 3 * m ^ 2 / (2 * μ) := by
    field_simp
    ring
  rw [hfrac] at hfinal
  have hE := he t
  linarith

end Hagi.Step
