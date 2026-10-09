/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.SafeQP
set_option linter.style.header false

/-!
# SafeQPPL — PL-скорость SafeQP с налогом конфликтов

Модель: L-гладкость (десцент-лемма — посылка), SafeQP-свойство
`‖d‖² ≤ ⟪g, d⟫`, PL-условие `‖g‖² ≥ 2μ(E − E*)`.

* `safeqp_pl_descent`: при `η = 1/L` —
  `f (x − (1/L)·d) ≤ f x − ‖d‖²/(2L)`;
* `safeqp_pl_rate`:
  `E' − E* ≤ (1 − μ·κ/L)·(E − E*)`, где
  `κ = ‖d‖²/‖g‖²` — измеримый коэффициент конфликтности;
* `pl_rate_noconflict`: при `d = g` — классический темп
  `1 − μ/L`.

Десцент-лемма и PL — посылки; κ измерим на каждом шаге.
-/

open Finset InnerProductSpace

namespace Hagi

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- При `0 < L`, десцент-лемме `hdescent` и `‖d‖² ≤ ⟪g, d⟫`:
`f (x − (1/L) • d) ≤ f x − ‖d‖²/(2L)`. -/
theorem safeqp_pl_descent (f : X → ℝ) (x : X) (d : X)
    (g : X) (L : ℝ) (hL : 0 < L)
    (hdescent : ∀ η (u : X), 0 ≤ η →
      f (x - η • u) ≤ f x - η * ⟪g, u⟫_ℝ + (L / 2) * η ^ 2 * ‖u‖ ^ 2)
    (hsafeqp : ‖d‖ ^ 2 ≤ ⟪g, d⟫_ℝ) :
    f (x - (1 / L) • d) ≤ f x - ‖d‖ ^ 2 / (2 * L) := by
  have h1 := hdescent (1 / L) d (by positivity)
  have hη : (1 / L) ^ 2 = 1 / L ^ 2 := by
    field_simp
  -- подстановка η = 1/L
  have hstep : f (x - (1 / L) • d)
      ≤ f x - (1 / L) * ⟪g, d⟫_ℝ + (L / 2) * (1 / L ^ 2) * ‖d‖ ^ 2 := by
    rw [← hη]
    exact h1
  -- линейная часть: −(1/L)⟪g,d⟫ ≤ −(1/L)‖d‖²
  have hlin : f x - (1 / L) * ⟪g, d⟫_ℝ ≤ f x - (1 / L) * ‖d‖ ^ 2 := by
    have h2 : ‖d‖ ^ 2 ≤ ⟪g, d⟫_ℝ := hsafeqp
    have h3 : (1:ℝ) / L * ‖d‖ ^ 2 ≤ (1:ℝ) / L * ⟪g, d⟫_ℝ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  -- квадратичная часть: (L/2)·(1/L²) = 1/(2L)
  have hquad : (L / 2) * (1 / L ^ 2) * ‖d‖ ^ 2
      = ‖d‖ ^ 2 / (2 * L) := by
    field_simp
  calc f (x - (1 / L) • d)
      ≤ f x - (1 / L) * ⟪g, d⟫_ℝ + (L / 2) * (1 / L ^ 2) * ‖d‖ ^ 2 :=
        hstep
    _ ≤ f x - (1 / L) * ‖d‖ ^ 2 + ‖d‖ ^ 2 / (2 * L) := by
        rw [hquad]
        exact add_le_add_left hlin _
    _ = f x - ‖d‖ ^ 2 / (2 * L) := by
        have hcalc : f x - (1 / L) * ‖d‖ ^ 2 + ‖d‖ ^ 2 / (2 * L)
            = f x - ‖d‖ ^ 2 / (2 * L) := by
          field_simp
          ring
        rw [hcalc]

/-- При посылках `safeqp_pl_descent`, PL-условии
`2μ·(f x − fstar) ≤ ‖g‖²` и `‖g‖² ≠ 0`:
`f (x − (1/L) • d) − fstar
≤ (1 − μ·(‖d‖²/‖g‖²)/L)·(f x − fstar)`. -/
theorem safeqp_pl_rate (f : X → ℝ) (x : X) (d g : X)
    (fstar L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdescent : ∀ η (u : X), 0 ≤ η →
      f (x - η • u) ≤ f x - η * ⟪g, u⟫_ℝ + (L / 2) * η ^ 2 * ‖u‖ ^ 2)
    (hsafeqp : ‖d‖ ^ 2 ≤ ⟪g, d⟫_ℝ)
    (hpl : 2 * μ * (f x - fstar) ≤ ‖g‖ ^ 2)
    (hg : ‖g‖ ^ 2 ≠ 0) :
    f (x - (1 / L) • d) - fstar
      ≤ (1 - μ * (‖d‖ ^ 2 / ‖g‖ ^ 2) / L) * (f x - fstar) := by
  have hstep := safeqp_pl_descent f x d g L hL hdescent hsafeqp
  -- ‖d‖² ≥ κ·‖g‖² ≥ κ·2μ(E−E*)
  have hκ : ‖d‖ ^ 2 = (‖d‖ ^ 2 / ‖g‖ ^ 2) * ‖g‖ ^ 2 :=
    (div_mul_cancel₀ _ hg).symm
  have hm : (‖d‖ ^ 2 / ‖g‖ ^ 2) * (2 * μ * (f x - fstar))
      ≤ (‖d‖ ^ 2 / ‖g‖ ^ 2) * ‖g‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hpl
      (div_nonneg (pow_nonneg (norm_nonneg d) 2)
        (pow_nonneg (norm_nonneg g) 2))
  have hchain : (‖d‖ ^ 2 / ‖g‖ ^ 2) * (2 * μ * (f x - fstar))
      ≤ ‖d‖ ^ 2 := by linarith [hm, hκ]
  -- сборка
  have h1 : f (x - (1 / L) • d) ≤ f x - ‖d‖ ^ 2 / (2 * L) := hstep
  have hhalf : (‖d‖ ^ 2 / ‖g‖ ^ 2) * μ * (f x - fstar)
      ≤ ‖d‖ ^ 2 / 2 := by
    have hsplit : (‖d‖ ^ 2 / ‖g‖ ^ 2) * μ * (f x - fstar)
        = ((‖d‖ ^ 2 / ‖g‖ ^ 2) * (2 * μ * (f x - fstar))) / 2 := by
      field_simp
    rw [hsplit, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    exact hchain
  have h2 : ‖d‖ ^ 2 / (2 * L)
      ≥ (‖d‖ ^ 2 / ‖g‖ ^ 2) * μ * (f x - fstar) / L := by
    rw [show ‖d‖ ^ 2 / (2 * L) = ‖d‖ ^ 2 / 2 / L from by field_simp]
    exact (div_le_div_iff_of_pos_right hL).mpr hhalf
  have hexp : (1 - μ * (‖d‖ ^ 2 / ‖g‖ ^ 2) / L) * (f x - fstar)
      = (f x - fstar)
        - (‖d‖ ^ 2 / ‖g‖ ^ 2) * μ * (f x - fstar) / L := by
    field_simp
  linarith [h1, h2, hexp]

/-- При тех же посылках, `d = g` и `⟪g, g⟫ = ‖g‖²`:
`f (x − (1/L) • g) − fstar ≤ (1 − μ/L)·(f x − fstar)`. -/
theorem pl_rate_noconflict (f : X → ℝ) (x : X) (g : X)
    (fstar L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdescent : ∀ η (u : X), 0 ≤ η →
      f (x - η • u) ≤ f x - η * ⟪g, u⟫_ℝ + (L / 2) * η ^ 2 * ‖u‖ ^ 2)
    (hpl : 2 * μ * (f x - fstar) ≤ ‖g‖ ^ 2)
    (hg : ‖g‖ ^ 2 ≠ 0)
    (hsq : ⟪g, g⟫_ℝ = ‖g‖ ^ 2) :
    f (x - (1 / L) • g) - fstar
      ≤ (1 - μ / L) * (f x - fstar) := by
  have hsafeqp : ‖g‖ ^ 2 ≤ ⟪g, g⟫_ℝ := by rw [hsq]
  have hrate := safeqp_pl_rate f x g g fstar L μ hL hμ hdescent
    hsafeqp hpl hg
  have hκ : ‖g‖ ^ 2 / ‖g‖ ^ 2 = 1 := div_self hg
  rw [hκ, mul_one] at hrate
  exact hrate

end Hagi
