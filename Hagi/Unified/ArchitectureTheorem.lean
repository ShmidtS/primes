/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.ConeTakeoff
import Hagi.Foundations.Recurrence
import Hagi.Growth.Saturation
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.DistillTransfer
import Hagi.Data.AntiCollapse
import Hagi.Step.SafeQP
import Hagi.Growth.StateBinding
/-!
# StateClosedRenewal — state-closed замыкание C→D→G→S

Динамика на полях состояния:
`C t = (S t).capability`, `D t = usableFrontier (S t)`.

* `state_closed_takeoff`: при шаге
  `C' = C + γ·D`, динамике `D' ≥ ρ·D + β·C`, `ρ ≥ γk`, пороге
  `β ≥ γk² + (1−ρ)k` и старте в конусе —
  `(S 0).capability·(1+γk)^T ≤ (S T).capability`;
* `state_closed_renewal_step`: то же с трением ξ и усиленным
  порогом `β ≥ γk² + (1−ρ)k + ξ/C t` — шаг конуса на полях
  состояния;
* `state_closed_band`: двусторонняя полоса
  `C₀(1+γk)^T ≤ (S T).capability ≤ C* − (1−σ)^T·(C* − C₀)`.

Полю β, PL-окно и `ρ ≥ γk` — пошаговые измеряемые посылки.
-/

open Finset Real

namespace Hagi.Growth

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- При `0 < γ`, `0 < k`, `0 < (S t).capability`, шаге
`C' = C + γ·usableFrontier`, динамике `D' ≥ ρ·D + β·C`,
`ρ ≥ γk`, пороге `β ≥ γk² + (1−ρ)k` и старте в конусе —
`(S 0).capability·(1+γk)^T ≤ (S T).capability`
(композиция `ratio_takeoff` и `cone_ratio_invariant`). -/
theorem state_closed_takeoff (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hCpos : ∀ t, 0 < (S t).capability)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (h_emp_cone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability := by
  exact ratio_takeoff (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k hγ hk h_emp_step
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos h_emp_step h_emp_dyn
      hrhogk hbeta h_emp_cone0) T

/-- Шаг конуса с трением: при шаге `C' = C + γ·D`, динамике
`ρ·D + β·C − ξ t ≤ D'`, `ρ ≥ γk`, пороге
`γk² + (1−ρ)k + ξ t/C t ≤ β`, `0 < C t` и конусе
`k·C t ≤ D t` следует
`k·(S (t+1)).capability ≤ usableFrontier (S (t+1))`. -/
theorem state_closed_renewal_step (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ) (xi : ℕ → ℝ)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      - xi t ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : ∀ t, γ * k ^ 2 + (1 - ρ) * k
      + xi t / (S t).capability ≤ β)
    {t : ℕ}
    (hCpos : 0 < (S t).capability)
    (h_emp_cone : k * (S t).capability ≤ usableFrontier (S t)) :
    k * (S (t + 1)).capability ≤ usableFrontier (S (t + 1)) := by
  have hd := h_emp_dyn t
  have hb := hbeta t
  have hs := h_emp_step t
  set C := (S t).capability with hC
  set D := usableFrontier (S t) with hD
  set C' := (S (t + 1)).capability with hC'
  set D' := usableFrontier (S (t + 1)) with hD'
  -- ключевая алгебра: D' − kC' ≥ (ρ−γk)(D−kC) + margin·C,
  -- margin = β − γk² − (1−ρ)k − ξ/C ≥ 0
  have hkey : ρ * D + β * C - xi t - k * (C + γ * D)
      = (ρ - γ * k) * (D - k * C)
        + (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D - k * C) := by
    have hsub : (0:ℝ) ≤ D - k * C := by linarith [h_emp_cone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ)
      ≤ (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C :=
    mul_nonneg (by linarith [hb]) hCpos.le
  have h3 : D' - k * C'
      ≥ (ρ - γ * k) * (D - k * C)
        + (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C := by
    rw [hs]
    linarith [hkey, hd]
  linarith

/-- При посылках `state_closed_takeoff` и обеих PL-формах с
`(S 0).capability ≤ Cstar` выполнено
`(S 0).capability·(1+γk)^T ≤ (S T).capability
≤ Cstar − (1−σ)^T·(Cstar − (S 0).capability)`. -/
theorem state_closed_band (S : ℕ → GrowthState X)
    (γ ρ β k Cstar σ : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ1 : σ ≤ 1)
    (hCpos : ∀ t, 0 < (S t).capability)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (h_emp_cone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (hpl_up : ∀ t, (S (t + 1)).capability
      ≤ (S t).capability + σ * (Cstar - (S t).capability))
    (hpl_lo : ∀ t, (S t).capability
      + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability)
    (hC0 : (S 0).capability ≤ Cstar) (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability) := by
  exact takeoff_with_saturation (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k Cstar σ hγ hk hσ1 h_emp_step
    hpl_up hpl_lo
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos h_emp_step h_emp_dyn
      hrhogk hbeta h_emp_cone0) hC0 T

end Hagi.Growth
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

namespace Hagi.Step

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

end Hagi.Step
/-!
# Универсальность и long-horizon safety

Форма результата: risk домена `i` за `T` циклов ≤
`T * min_k risk_i(leaf_k) + R + ε0/(1 - ρ)`, где `R` —
regret-бюджет роутера (measured premise), `ε0, ρ` — параметры
геометрического бюджета дрейфа.

Теоремы:
* `geometric_eps_sum` — Σ_{t<T} ε0·ρ^t ≤ ε0/(1−ρ) при 0 ≤ ρ < 1.
* `hedge_domain_guarantee` — если risk t i ≤ best i + r t на
  каждом шаге, то Σ risk ≤ T·best i + Σ r t.
* `universality_longhorizon` — суммарный риск ≤ T·best i +
  R + ε0/(1−ρ); amortized excess/T → 0 при фиксированных
  R и ε0/(1−ρ).
-/

open Finset

namespace Hagi.Autonomy

variable {I K : ℕ}

/-- При `0 ≤ ε0`, `0 ≤ ρ < 1` и любом `T`:
Σ_{t<T} ε0·ρ^t ≤ ε0/(1−ρ). -/
theorem geometric_eps_sum (ε0 ρ : ℝ) (hε : 0 ≤ ε0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, ε0 * ρ ^ t ≤ ε0 / (1 - ρ) := by
  have hne : (1:ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hρ1)
  -- closed-форма по индукции: S(T) = ε0(1−ρ^T)/(1−ρ)
  have hgeom : ∀ T : ℕ, ∑ t ∈ Finset.range T, ε0 * ρ ^ t
      = ε0 * (1 - ρ ^ T) / (1 - ρ) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        field_simp
        ring
  rw [hgeom T, div_le_div_iff_of_pos_right (sub_pos.mpr hρ1)]
  have h1 : (0:ℝ) ≤ 1 - ρ ^ T := by
    rw [sub_nonneg]
    have hp := pow_le_pow_of_le_one hρ (le_of_lt hρ1)
      (Nat.zero_le T)
    simpa using hp
  have h2 : 1 - ρ ^ T ≤ 1 := by
    linarith [h1, pow_nonneg hρ T]
  calc ε0 * (1 - ρ ^ T) ≤ ε0 * 1 :=
        mul_le_mul_of_nonneg_left h2 hε
    _ = ε0 := mul_one ε0

/-- Если `risk t i ≤ best i + r t` для всех `t < T`, то
Σ_{t<T} risk t i ≤ T * best i + Σ_{t<T} r t. -/
theorem hedge_domain_guarantee {T : ℕ}
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ) (r : ℕ → ℝ)
    (i : Fin I)
    (hstep : ∀ t ∈ Finset.range T,
      risk t i ≤ best i + r t) :
    ∑ t ∈ Finset.range T, risk t i
      ≤ T * best i + ∑ t ∈ Finset.range T, r t := by
  have hsplit : ∑ t ∈ Finset.range T, risk t i
      ≤ ∑ t ∈ Finset.range T, (best i + r t) :=
    Finset.sum_le_sum fun t ht => hstep t ht
  have hsum : ∑ t ∈ Finset.range T, (best i + r t)
      = ∑ t ∈ Finset.range T, best i
        + ∑ t ∈ Finset.range T, r t :=
    Finset.sum_add_distrib
  have hconst : ∑ t ∈ Finset.range T, best i
      = ((Finset.range T).card : ℝ) * best i := by
    rw [Finset.sum_const]
    simp
  have hcard : ((Finset.range T).card : ℝ) = (T : ℝ) := by
    rw [Finset.card_range]
  rw [hsum, hconst, hcard] at hsplit
  linarith

/-- Если `risk t i ≤ best i + r t + ε0·ρ^t` для всех `t < T`,
`Σ r t ≤ R`, `0 ≤ ρ < 1`, то Σ_{t<T} risk t i ≤
T * best i + R + ε0/(1−ρ). -/
theorem universality_longhorizon {T : ℕ}
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ)
    (r : ℕ → ℝ) (i : Fin I) (R ε0 ρ : ℝ)
    (hstep : ∀ t ∈ Finset.range T,
      risk t i ≤ best i + r t + ε0 * ρ ^ t)
    (hregret : ∑ t ∈ Finset.range T, r t ≤ R)
    (hε : 0 ≤ ε0) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑ t ∈ Finset.range T, risk t i
      ≤ T * best i + R + ε0 / (1 - ρ) := by
  -- трёхчленная декомпозиция
  have hsum : ∑ t ∈ Finset.range T, risk t i
      ≤ ∑ t ∈ Finset.range T, (best i + r t + ε0 * ρ ^ t) :=
    Finset.sum_le_sum fun t ht => hstep t ht
  have hsplit : ∑ t ∈ Finset.range T, (best i + r t + ε0 * ρ ^ t)
      = (∑ t ∈ Finset.range T, best i)
        + (∑ t ∈ Finset.range T, r t)
        + ∑ t ∈ Finset.range T, ε0 * ρ ^ t := by
    classical
    simp only [Finset.sum_add_distrib]
  have hconst : ∑ t ∈ Finset.range T, best i
      = (T : ℝ) * best i := by
    rw [Finset.sum_const, Finset.card_range]

    ring
  have hgeom := geometric_eps_sum ε0 ρ hε hρ hρ1 T
  rw [hsplit, hconst] at hsum
  nlinarith [hsum, hregret, hgeom]

end Hagi.Autonomy

namespace Hagi
export Hagi.Autonomy (geometric_eps_sum hedge_domain_guarantee universality_longhorizon)
end Hagi
set_option linter.style.header false

/-!
# HAGI Synthesis — horizon-form capstone

All step premises are quantified over the horizon only
(`t ∈ Finset.range T`); `Cstar` and `sigma` are certificate
parameters. The T3 operator premise is an abstract measured
gain stream `g : ℕ → ℝ` (nats/step). Truncated band lemmas
(`cone_invariant_trunc`, `takeoff_lower_trunc`,
`pl_gap_lower_trunc`) prove the growth band from
horizon-only premises; `band_witness` exhibits a concrete
numeric pair satisfying the truncated band premises, so
`hagi_synthesis` is not vacuous. The certificate is usable
while `C0 * (1 + gamma * k) ^ T ≤ Cstar`.
-/

open Finset

namespace Hagi.Unified

variable {Xs V : Type*} [NormedAddCommGroup Xs]
  [InnerProductSpace ℝ Xs]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Truncated cone invariant: from the cone at 0 and
horizon-only step/dynamics premises, D t >= k * C t holds
for every t <= T. -/
theorem cone_invariant_trunc (C D : ℕ → ℝ) (γ ρ β k : ℝ) (T : ℕ)
    (hCpos : ∀ t ∈ Finset.range (T + 1), 0 < C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := Foundations.cone_invariant_horizon C D γ ρ β k T
    hCpos hstep hdyn hrhogk hbeta hcone0

/-- Truncated takeoff lower bound: C T >= C 0 * (1+gamma k)^T
from horizon-only premises (steps t < T only). -/
theorem takeoff_lower_trunc (C D : ℕ → ℝ) (γ k : ℝ) (T : ℕ)
    (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hcone : ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t) :
    C 0 * (1 + γ * k) ^ T ≤ C T := Foundations.takeoff_from_cone C D γ k T
    (mul_nonneg hγ hk) hγ hk hstep hcone

/-- Truncated band UPPER bound: from the upper PL form at
steps t < T, (1-sigma)^T * (Cstar - C 0) <= Cstar - C T,
i.e. C T <= Cstar - (1-sigma)^T * (Cstar - C 0). -/
theorem pl_gap_lower_trunc (C : ℕ → ℝ) (Cstar σ : ℝ) (T : ℕ)
    (hσ1 : σ ≤ 1)
    (hpl_up : ∀ t ∈ Finset.range T,
      C (t + 1) ≤ C t + σ * (Cstar - C t)) :
    (1 - σ) ^ T * (Cstar - C 0) ≤ Cstar - C T := by
  have hgapstep : ∀ t < T,
      (1 - σ) * (Cstar - C t) ≤ Cstar - C (t + 1) := by
    intro t ht
    have h := hpl_up t (Finset.mem_range.mpr ht)
    have hE : (1 - σ) * (Cstar - C t)
        = Cstar - C t - σ * (Cstar - C t) := by ring
    rw [hE]
    linarith [h]
  have hσ0 : (0:ℝ) ≤ 1 - σ := by linarith
  exact Hagi.Foundations.recurrence_lower (1 - σ)
    (fun t => Cstar - C t) T hσ0 hgapstep

/-- Пошаговые сертификаты цикла HAGI на горизонте `T`
(измеряемые h_emp_-посылки): рост (шаг состояния и динамика
фронтира с gain-потоком `g`), конус, PL-окно с параметрами
`Cstar` и `sigma`, Hedge-универсальность и суммируемый
дрейф. Все посылки квантифицированы только по
`t < T`; выполнимость — пока
`C0 * (1 + gamma * k) ^ T ≤ Cstar` (см. `band_witness`). -/
structure HAGICert {I : ℕ} (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ) where
  hCpos : ∀ t ∈ Finset.range (T + 1), 0 < (S t).capability
  hstep : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    = (S t).capability + γ * usableFrontier (S t)
  hop : ∀ t ∈ Finset.range T, ρ * usableFrontier (S t)
    + ηT * g t - ξ
      ≤ usableFrontier (S (t + 1))
  hsuff : ∀ t ∈ Finset.range T, γ * k ^ 2 * (S t).capability
    + (1 - ρ) * k * (S t).capability + ξ
    ≤ ηT * g t
  hrhogk : γ * k ≤ ρ
  hcone0 : k * (S 0).capability ≤ usableFrontier (S 0)
  hpl_up : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    ≤ (S t).capability + σ * (Cstar - (S t).capability)
  hpl_lo : ∀ t ∈ Finset.range T, (S t).capability
    + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability
  hCstar : 0 < Cstar
  hσ0 : 0 < σ
  hσ1 : σ ≤ 1
  hC0 : (S 0).capability ≤ Cstar
  hrisk : ∀ t ∈ Finset.range T, ∀ i : Fin I,
    risk t i ≤ best i + r t + ε0 * ρe ^ t
  hregret : ∑ t ∈ Finset.range T, r t ≤ R
  hε0 : 0 ≤ ε0
  hρe : 0 ≤ ρe
  hρe1 : ρe < 1

/-- При сертификате `HAGICert` на горизонте `T` одновременно:
`C0 * (1 + γk) ^ T ≤ C_T ≤ Cstar − (1−σ)^T · (Cstar − C0)`
и `Σ risk ≤ T * best + R + ε0 / (1 − ρe)`. -/
theorem hagi_synthesis {I : ℕ} (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k)
    (cert : HAGICert S g risk best r
      γ ρ k ξ ηT Cstar σ ε0 ρe R T) :
    ((S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability))
    ∧ ∀ i : Fin I, ∑ t ∈ Finset.range T, risk t i
      ≤ T * best i + R + ε0 / (1 - ρe) := by
  obtain ⟨hCpos, hstep, hop, hsuff, hrhogk, hcone0, hpl_up,
    hpl_lo, hCstar, hσ0, hσ1, hC0, hrisk, hregret, hε0,
    hρe, hρe1⟩ := cert
  constructor
  · -- полоса роста: динамика на горизонте ⟹ конус
    have hdyn : ∀ t ∈ Finset.range T,
        ρ * usableFrontier (S t)
        + (γ * k ^ 2 + (1 - ρ) * k) * (S t).capability
        ≤ usableFrontier (S (t + 1)) := by
      intro t ht
      have h1 := hop t ht
      have h2 := hsuff t ht
      linarith
    have hcone := cone_invariant_trunc
      (fun t => (S t).capability)
      (fun t => usableFrontier (S t))
      γ ρ (γ * k ^ 2 + (1 - ρ) * k) k T
      hCpos hstep hdyn hrhogk
      (by linarith) hcone0
    constructor
    · exact takeoff_lower_trunc
        (fun t => (S t).capability)
        (fun t => usableFrontier (S t)) γ k T
        (le_of_lt hγ) (le_of_lt hk) hstep hcone
    · have hband := pl_gap_lower_trunc
        (fun t => (S t).capability) Cstar σ T hσ1 hpl_up
      linarith
  · intro i
    exact universality_longhorizon risk best r i R ε0 ρe
      (fun t ht => hrisk t ht i) hregret hε0 hρe hρe1

/-- The powers of 1/2 stay in [0,1]. -/
theorem half_pow_bounds (t : ℕ) :
    0 < (1/2 : ℝ) ^ t ∧ (1/2 : ℝ) ^ t ≤ 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [pow_succ]
      obtain ⟨h0, h1⟩ := ih
      constructor
      · positivity
      · nlinarith

/-- Powers of 1/2 are antitone in the exponent. -/
theorem half_pow_anti (t s : ℕ) (h : s ≤ t) :
    (1/2 : ℝ) ^ t ≤ (1/2 : ℝ) ^ s := by
  induction t with
  | zero =>
      have hs : s = 0 := Nat.le_zero.mp h
      subst hs
      rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · have hstep := ih (by omega)
        have hp : 0 < (1/2 : ℝ) ^ s := by positivity
        rw [pow_succ]
        nlinarith
      · have hseq : s = t + 1 := by omega
        rw [hseq]

/-- A concrete witness of the truncated band premises
(`C t = 100 − 99·(1/2)^t`, `D t = 990·(1/2)^t`,
`Cstar = 100`, `sigma = 1/2`, `gamma = 1/20`,
`k = 1/1000`, any `T ≤ 10`): step, dynamics, cone, and PL
window all hold, so the horizon certificate is satisfiable.
The risk/Hedge side is supplied by the measured layer. -/
theorem band_witness :
    (∀ T ≤ 10,
      (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ (t + 1))
            = (100 - 99 * (1/2 : ℝ) ^ t)
              + (1/20) * (990 * (1/2 : ℝ) ^ t))
        ∧ (∀ t ∈ Finset.range T,
          (1/20000) * (990 * (1/2 : ℝ) ^ t)
            + ((1/20) * (1/1000) ^ 2
                + (1 - 1/20000) * (1/1000))
                * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ (t + 1))
        ∧ (∀ t ∈ Finset.range (T + 1),
          (1/1000) * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ t)
        ∧ (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ t)
            + (1/2) * (100 - (100 - 99 * (1/2 : ℝ) ^ t))
            ≤ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
            ∧ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
              ≤ (100 - 99 * (1/2 : ℝ) ^ t)
                + (1/2)
                  * (100 - (100 - 99 * (1/2 : ℝ) ^ t)))) := by
  intro T _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _
    rw [pow_succ]
    field_simp
    ring
  · -- dynamics: 0.00005*D + beta*C <= D'
    intro t _
    -- t < T <= 10  =>  h := (1/2)^t >= (1/2)^9
    have ht9 : t ≤ 9 := by
      have hmem := Finset.mem_range.mp ‹t ∈ Finset.range T›
      have := ‹T ≤ 10›
      omega
    have hlo : (1/512 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have hanti := half_pow_anti 9 t ht9
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    rw [show 990 * (1/2 : ℝ) ^ (t + 1)
        = 495 * (1/2 : ℝ) ^ t from by
      rw [pow_succ]
      ring]
    linarith
  · intro t _
    have hlo : (1/1024 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have ht10 : t ≤ 10 := by
        have hmem := Finset.mem_range.mp ‹t ∈ Finset.range (T + 1)›
        omega
      have hanti := half_pow_anti 10 t ht10
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    linarith
  · intro t _
    -- PL window: EXACT equality at sigma = 1/2
    constructor
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith

/-- Конечный горизонт взлёта+насыщения: точный шаг, точное
насыщение и конус совместимы лишь ограниченное время:
(1+γk)^T ≤ σC*/((γk+σ)·C 0). -/
theorem cert_horizon_bound (C F : ℕ → ℝ)
    (γ k σ Cstar : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ : 0 < σ) (hCstar : 0 < Cstar)
    (hC0 : 0 < C 0) (hT1 : 1 ≤ T)
    (hstep : ∀ t < T, C (t + 1) = C t + γ * F t)
    (hpl : ∀ t < T, C (t + 1) = C t + σ * (Cstar - C t))
    (hcone : ∀ t < T, k * C t ≤ F t) :
    (1 + γ * k) ^ (T - 1)
      ≤ σ * Cstar / ((γ * k + σ) * C 0) := by
  -- ключ: γ·F t = σ(Cstar − C t) из двух точных шагов
  have hgf : ∀ t < T, γ * F t = σ * (Cstar - C t) := by
    intro t ht
    have h1 := hstep t ht
    have h2 := hpl t ht
    rw [h1] at h2
    exact add_left_cancel h2
  -- конус + ключ: (γk+σ)·C t ≤ σ·Cstar
  have hkey : ∀ t < T,
      (γ * k + σ) * C t ≤ σ * Cstar := by
    intro t ht
    have hcone' := hcone t ht
    have hgf' := hgf t ht
    have h1 : γ * (k * C t) ≤ γ * F t :=
      mul_le_mul_of_nonneg_left hcone' hγ.le
    rw [hgf'] at h1
    have h2 : γ * k * C t + σ * C t ≤ σ * Cstar := by
      calc γ * k * C t + σ * C t
          = γ * (k * C t) + σ * C t := by ring
        _ ≤ σ * (Cstar - C t) + σ * C t := by
            exact add_le_add h1 (le_refl _)
        _ = σ * Cstar := by ring
    linarith
  -- взлёт: C t+1 ≥ (1+γk)·C t, индукция: C T ≥ (1+γk)^T·C 0
  have hgrow : ∀ t ≤ T, C 0 * (1 + γ * k) ^ t ≤ C t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro _
        have hstep' := hstep t (by omega)
        have hcone' := hcone t (by omega)
        have hge : (1 + γ * k) * C t ≤ C (t + 1) := by
          have hmul : γ * (k * C t) ≤ γ * F t :=
            mul_le_mul_of_nonneg_left hcone' hγ.le
          rw [hstep']
          calc (1 + γ * k) * C t
              = C t + γ * (k * C t) := by ring
            _ ≤ C t + γ * F t := by
                exact add_le_add_right hmul (C t)
            _ = C t + γ * F t := by rfl
        have hpos : (0:ℝ) ≤ 1 + γ * k := by nlinarith [hγ, hk]
        calc C 0 * (1 + γ * k) ^ (t + 1)
            = C 0 * (1 + γ * k) ^ t * (1 + γ * k) := by ring
          _ ≤ C t * (1 + γ * k) := by
              exact mul_le_mul_of_nonneg_right (ih (by omega)) hpos
          _ = (1 + γ * k) * C t := by ring
          _ ≤ C (t + 1) := hge
  -- сборка (на T−1: hkey доступен для t < T)
  have hT := hkey (T - 1) (by omega)
  have hgrowT := hgrow (T - 1) (by omega)
  have hpos1 : (0:ℝ) < γ * k + σ := by nlinarith [hγ, hk, hσ]
  have hmul : (γ * k + σ) * (C 0 * (1 + γ * k) ^ (T - 1))
      ≤ (γ * k + σ) * C (T - 1) :=
    mul_le_mul_of_nonneg_left hgrowT (le_of_lt hpos1)
  have hfinal : (γ * k + σ) * C 0 * (1 + γ * k) ^ (T - 1)
      ≤ σ * Cstar := by
    calc (γ * k + σ) * C 0 * (1 + γ * k) ^ (T - 1)
        = (γ * k + σ) * (C 0 * (1 + γ * k) ^ (T - 1)) := by ring
      _ ≤ (γ * k + σ) * C (T - 1) := hmul
      _ ≤ σ * Cstar := hT
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (γ * k + σ) * C 0)]
  calc (1 + γ * k) ^ (T - 1) * ((γ * k + σ) * C 0)
      = (γ * k + σ) * C 0 * (1 + γ * k) ^ (T - 1) := by ring
    _ ≤ σ * Cstar := hfinal

/-- **Нетривиальный witness для cert_horizon_bound** (nonvacuity,
единый план §6.1): конкретная траектория, на которой ВСЕ
посылки cert_horizon_bound выполняются одновременно с
ненулевым ростом (T = 1, C 0 = 1 < C 1 = 3/2 < Cstar = 2):

  C t = 2 − (1/2)^t, F t = (1/2)^t, γ = k = σ = 1/2, Cstar = 2,

т.е. точное насыщение C' = C + σ(Cstar − C) и конус
k·C ≤ F на t = 0. Заметим: при t = 1 конус уже нарушен
(3/4 > 1/2) — совместимость взлёта и насыщения живёт лишь на коротком
горизонте, в точности как требует cert_horizon_bound:
(1 + γk)^(T−1) = 1 ≤ σ·Cstar/((γk+σ)·C 0) = 4/3. -/
theorem cert_horizon_witness :
    ∃ (C F : ℕ → ℝ) (γ k σ Cstar : ℝ) (T : ℕ),
      0 < γ ∧ 0 < k ∧ 0 < σ ∧ 0 < Cstar ∧ 0 < C 0 ∧ 1 ≤ T
        ∧ (∀ t < T, C (t + 1) = C t + γ * F t)
        ∧ (∀ t < T, C (t + 1) = C t + σ * (Cstar - C t))
        ∧ (∀ t < T, k * C t ≤ F t)
        ∧ C 0 < C T ∧ C T < Cstar := by
  refine ⟨fun t => 2 - (1 / 2 : ℝ) ^ t, fun t => (1 / 2 : ℝ) ^ t,
    1 / 2, 1 / 2, 1 / 2, 2, 1,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, ?_, ?_, by norm_num, by norm_num⟩
  · intro t ht
    interval_cases t
    norm_num
  · intro t ht
    interval_cases t
    norm_num
  · intro t ht
    interval_cases t
    norm_num

/-- **Граница горизонта для HAGICert-траектории**
(единый план §5.6, композиция):
из полей сертификата hstep + hpl_up + hpl_lo
следует точное равенство насыщения,
и при конусе на всём горизонте
cert_horizon_bound даёт логарифмическую
оценку совместимости взлёта и
насыщения напрямую для capability-поля
состояний. -/
theorem hagi_horizon_bound {I : ℕ} (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin I → ℝ) (best : Fin I → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k)
    (cert : HAGICert S g risk best r
      γ ρ k ξ ηT Cstar σ ε0 ρe R T)
    (hcone : ∀ t ∈ Finset.range T,
      k * (S t).capability ≤ usableFrontier (S t))
    (hT1 : 1 ≤ T) :
    (1 + γ * k) ^ (T - 1)
      ≤ σ * Cstar / ((γ * k + σ) * (S 0).capability) := by
  refine cert_horizon_bound
    (C := fun t => (S t).capability)
    (F := fun t => usableFrontier (S t))
    γ k σ Cstar T hγ hk cert.hσ0 cert.hCstar ?_ hT1 ?_ ?_ ?_
  · exact cert.hCpos 0 (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le T)))
  · intro t ht
    exact cert.hstep t (Finset.mem_range.mpr ht)
  · intro t ht
    exact le_antisymm
      (cert.hpl_up t (Finset.mem_range.mpr ht))
      (cert.hpl_lo t (Finset.mem_range.mpr ht))
  · intro t ht
    exact hcone t (Finset.mem_range.mpr ht)

/-- Явная логарифмическая форма горизонта совместимости
взлёта и насыщения (R349): логарифмируя `cert_horizon_bound`,
получаем явный потолок числа шагов

  T ≤ 1 + (ln(σ·C*) − ln((γk+σ)·C 0)) / ln(1+γk),

если зазор насыщения строго положителен
(`(γk+σ)·C 0 < σ·C*`). Чем больше конус-усиление γk, тем
короче горизонт — экспоненциальный взлёт быстрее упирается в
потолок насыщения. -/
theorem cert_horizon_log_bound (C F : ℕ → ℝ)
    (γ k σ Cstar : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ : 0 < σ) (hCstar : 0 < Cstar)
    (hC0 : 0 < C 0) (hT1 : 1 ≤ T)
    (hgap : (γ * k + σ) * C 0 < σ * Cstar)
    (hstep : ∀ t < T, C (t + 1) = C t + γ * F t)
    (hpl : ∀ t < T, C (t + 1) = C t + σ * (Cstar - C t))
    (hcone : ∀ t < T, k * C t ≤ F t) :
    ((T : ℝ) - 1) * Real.log (1 + γ * k)
      ≤ Real.log (σ * Cstar) - Real.log ((γ * k + σ) * C 0) := by
  have hb := cert_horizon_bound C F γ k σ Cstar T hγ hk hσ hCstar
    hC0 hT1 hstep hpl hcone
  have hpos1 : (0:ℝ) < 1 + γ * k := by nlinarith
  have hpos2 : (0:ℝ) < σ * Cstar / ((γ * k + σ) * C 0) :=
    div_pos (mul_pos hσ hCstar)
      (mul_pos (by nlinarith) hC0)
  have hlog := Real.log_le_log (pow_pos hpos1 _) hb
  rw [Real.log_pow] at hlog
  have hcast : ((T - 1 : ℕ) : ℝ) = ((T:ℝ) - 1) := by
    rw [Nat.cast_sub hT1, Nat.cast_one]
  rw [hcast] at hlog
  rw [Real.log_div (ne_of_gt (mul_pos hσ hCstar))
    (ne_of_gt (mul_pos (by nlinarith : (0:ℝ) < γ * k + σ) hC0))] at hlog
  exact hlog

/-- **Экспонат честности** (R364, аудит v7 §6.2): поля
`hpl_up` и `hpl_lo` сертификата `HAGICert` сравнивают
`C (t+1)` с ОДНОЙ и той же величиной
`C t + σ·(Cstar − C t)` с двух сторон — совместно они
принуждают ТОЧНЫЙ закон насыщения

  C (t + 1) = C t + σ * (Cstar − C t)

на каждом шаге t < T. Насыщение — часть модели (закон
перехода), а не вывод из более слабых принципов; выведенная
граница `pl_gap_lower_trunc` опирается на этот точный закон. -/
theorem saturation_law_forced {I : ℕ} {Xs : Type*}
    [NormedAddCommGroup Xs] [InnerProductSpace ℝ Xs]
    (S : ℕ → GrowthState Xs) (Cstar σ : ℝ) (t : ℕ)
    (hup : (S (t + 1)).capability
      ≤ (S t).capability + σ * (Cstar - (S t).capability))
    (hlo : (S t).capability
      + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability) :
    (S (t + 1)).capability
      = (S t).capability + σ * (Cstar - (S t).capability) :=
  le_antisymm hup hlo

/-- **Бюджет на всём горизонте** (R364, аудит v7 §6.1):
точный счёт бюджета + неотрицательность каждого расхода
дают неотрицательность бюджета на ВСЁМ горизонте
(∀ t ≤ T), а не только в конечной точке: частичные суммы
расходов никогда не превышают B₀. -/
theorem budget_horizon_nonneg (B spend : ℕ → ℝ) (T : ℕ)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hacct : ∀ t ≤ T,
      B t = B 0 - ∑ j ∈ Finset.range t, spend j)
    (hT : 0 ≤ B T) :
    ∀ t ≤ T, 0 ≤ B t := by
  intro t ht
  rw [hacct t ht]
  have hpart : ∑ j ∈ Finset.range t, spend j
      ≤ ∑ j ∈ Finset.range T, spend j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      have hx' := Finset.mem_range.mp hx
      simp only [Finset.mem_range]
      omega
    · intro x hx _
      exact hspend x hx
  have hB : ∑ j ∈ Finset.range T, spend j ≤ B 0 := by
    rw [hacct T (Nat.le_refl T)] at hT
    linarith
  linarith

end Hagi.Unified

namespace Hagi
export Hagi.Unified (cone_invariant_trunc takeoff_lower_trunc pl_gap_lower_trunc HAGICert hagi_synthesis cert_horizon_bound cert_horizon_witness cert_horizon_log_bound saturation_law_forced budget_horizon_nonneg hagi_horizon_bound half_pow_bounds half_pow_anti band_witness)
end Hagi
