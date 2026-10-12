/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Foundations.Recurrence — каноническая рекуррентная лемма

Канонические леммы для линейной рекурренты
`x_{t+1} ≤ rho * x_t + c` на горизонте `t < T`: посылки
только при `t < T`, горизонт `T` — в самой лемме.
-/

open Finset Real

namespace Hagi.Foundations

variable (rho c : ℝ)

/-- Телескоп-тождество геометрической суммы:
(1 - rho) * sum_{i<t} rho^i = 1 - rho^t. -/
theorem geom_telescope (T : ℕ) :
    (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i = 1 - rho ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      have hexp : (1 - rho) * (∑ i ∈ Finset.range T, rho ^ i + rho ^ T)
          = (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i
            + (1 - rho) * rho ^ T := by ring
      rw [hexp, ih, pow_succ]
      ring

/-- **Верхняя рекуррента (горизонтная форма)**: если
x_{t+1} <= rho * x_t + c при t < T и rho ∈ [0,1), то

  x T <= rho^T * x 0 + c * ((1 - rho^T) / (1 - rho)). -/
theorem recurrence_upper (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t + c) :
    x T ≤ rho ^ T * x 0 + c * ((1 - rho ^ T) / (1 - rho)) := by
  -- ключевое тождество индукции: rho * sum_t + 1 = sum_{t+1}
  have hstepid : ∀ t : ℕ,
      rho * ∑ i ∈ Finset.range t, rho ^ i + 1
        = ∑ i ∈ Finset.range (t + 1), rho ^ i := by
    intro t
    have h := geom_telescope rho t
    rw [Finset.sum_range_succ]
    linarith
  have hmain : ∀ t, t ≤ T →
      x t ≤ rho ^ t * x 0 + c * (∑ i ∈ Finset.range t, rho ^ i) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have htlt : t < T := by omega
        have hs := hstep t htlt
        have hih := ih (by omega)
        have hconv : rho * (rho ^ t * x 0 + c * ∑ i ∈ Finset.range t, rho ^ i)
            = rho ^ (t + 1) * x 0 + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) := by
          rw [pow_succ]
          ring
        calc x (t + 1) ≤ rho * x t + c := hs
          _ ≤ rho * (rho ^ t * x 0
                + c * ∑ i ∈ Finset.range t, rho ^ i) + c := by
              have hmul := mul_le_mul_of_nonneg_left hih hrho
              linarith
          _ = rho ^ (t + 1) * x 0
                + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c := by
                rw [hconv]
          _ = rho ^ (t + 1) * x 0
                + c * (∑ i ∈ Finset.range (t + 1), rho ^ i) := by
                have hrw : rho ^ (t + 1) * x 0
                    + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c
                    = rho ^ (t + 1) * x 0
                      + c * (rho * ∑ i ∈ Finset.range t, rho ^ i + 1) := by
                  ring
                rw [hrw, hstepid t]
  have hgeom : ∑ i ∈ Finset.range T, rho ^ i
      = (1 - rho ^ T) / (1 - rho) := by
    have hne : 1 - rho ≠ 0 :=
      sub_ne_zero_of_ne (ne_of_lt hrho1).symm
    have hsum := geom_telescope rho T
    field_simp
    linarith [hsum]
  have h := hmain T (le_refl T)
  rw [hgeom] at h
  exact h

/-- **Чистая рекуррента (c = 0)**: x_{t+1} <= rho * x_t при
t < T и rho ≥ 0 ⟹ x T <= rho^T * x 0. Требования rho < 1
НЕ нужно (в отличие от recurrence_upper с c ≠ 0): случай
rho = 1 — тривиальная нестрогая нерастущесть. -/
theorem recurrence_pure (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t) :
    x T ≤ rho ^ T * x 0 := by
  have hmain : ∀ t : ℕ, t ≤ T →
      x t ≤ rho ^ t * x 0 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hmul : rho * x t ≤ rho * (rho ^ t * x 0) :=
          mul_le_mul_of_nonneg_left hih hrho
        rw [pow_succ]
        calc x (t + 1) ≤ rho * x t := hs
          _ ≤ rho * (rho ^ t * x 0) := hmul
          _ = rho ^ t * rho * x 0 := by ring
  exact hmain T (le_refl T)

/-- **Нижняя рекуррента (c = 0, горизонт)**: x_{t+1} >= rho * x_t
при t < T и rho >= 0 ⟹ rho^T * x 0 <= x T. -/
theorem recurrence_lower (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, rho * x t ≤ x (t + 1)) :
    rho ^ T * x 0 ≤ x T := by
  have hmain : ∀ t : ℕ, t ≤ T → rho ^ t * x 0 ≤ x t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hstepmul : rho ^ t * x 0 * rho ≤ x t * rho :=
          mul_le_mul_of_nonneg_right hih hrho
        rw [pow_succ]
        calc rho ^ t * rho * x 0 = rho ^ t * x 0 * rho := by ring
          _ ≤ x t * rho := hstepmul
          _ = rho * x t := by ring
          _ ≤ x (t + 1) := hs
  exact hmain T (le_refl T)

/-- Геометрическая хвостовая граница: для `rho ∈ [0,1)`
конечная геометрическая сумма `∑ i < T, rho ^ i ≤ 1 / (1 - rho)`. -/
theorem geom_sum_le_inv (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    ∑ i ∈ Finset.range T, rho ^ i ≤ 1 / (1 - rho) := by
  have hpos : 0 < 1 - rho := by linarith
  have hid := geom_telescope rho T
  have h1 : rho ^ T ≥ 0 := by positivity
  have hle : 1 - rho ^ T ≤ 1 := by linarith
  have hsplit : (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i ≤ 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hfinal : (1 - rho) * (1 / (1 - rho)) = 1 := by field_simp
  have hmono : (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i
      ≤ (1 - rho) * (1 / (1 - rho)) := by
    rw [hfinal]
    exact hsplit
  have hdiv : (1 / (1 - rho)) * (1 - rho) = 1 := by field_simp
  nlinarith [hmono, hpos]

/-- Предел сжатия: если `x (t + 1) ≤ rho * x t + delta` для
всех `t` и `rho < 1`, то `x T ≤ rho ^ T * x 0 + delta / (1 - rho)`. -/
theorem contraction_limit (x : ℕ → ℝ) (delta : ℝ) (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, x (t + 1) ≤ rho * x t + delta) :
    x T ≤ rho ^ T * x 0 + delta / (1 - rho) := by
  have hexact : ∀ t : ℕ, t ≤ T →
      x t ≤ rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have h1 := hstep t
        have hchain : x (t + 1)
            ≤ rho * (rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i) + delta := by
          calc x (t + 1) ≤ rho * x t + delta := h1
            _ ≤ rho * (rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i) + delta := by
                have hmul := mul_le_mul_of_nonneg_left (ih (by omega)) hrho
                linarith
        rw [Finset.sum_range_succ, pow_succ]
        have htel := geom_telescope rho t
        nlinarith [hchain, htel, hdelta]
  have hsum := geom_sum_le_inv rho T hrho hrho1
  have hfin := hexact T (le_refl T)
  have hdelta' : delta * ∑ i ∈ Finset.range T, rho ^ i ≤ delta / (1 - rho) := by
    calc delta * ∑ i ∈ Finset.range T, rho ^ i
        ≤ delta * (1 / (1 - rho)) := mul_le_mul_of_nonneg_left hsum hdelta
      _ = delta / (1 - rho) := by field_simp
  linarith

/-- **The linear compounding law.** If each cycle improves the
mean by at least `c`, the mean after `k` cycles is at most
`M₀ − k • c`. -/
theorem genMean_compound (M₀ c : ℝ) (_hc : 0 < c)
    (step : ℕ → ℝ → ℝ)
    (hstep : ∀ k M, step k M ≤ M - c)
    (iter : ℕ → ℝ) (hiter0 : iter 0 = M₀)
    (hiterS : ∀ k, iter (k + 1) = step k (iter k)) :
    ∀ k : ℕ, iter k ≤ M₀ - (k : ℝ) * c := by
  intro k
  induction k with
  | zero => rw [hiter0]; norm_num
  | succ n ih =>
      have h1 := hstep n (iter n)
      have h2 : iter (n + 1) ≤ iter n - c := by
        rw [hiterS n]
        exact h1
      -- the goal: iter (n+1) <= M0 - (n+1)c
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      have hgoal : iter n - c ≤ M₀ - ((n + 1 : ℕ) : ℝ) * c := by
        rw [hcast]
        linarith [ih]
      linarith [h2, hgoal]

/-- If `G (t + 1) ≤ ρ * G t + D` for all `t` with
`0 ≤ ρ < 1` and `G 0 ≤ G₀`, then
`G t ≤ ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)` for every `t`. -/
theorem genGap_decay (ρ D G₀ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (_hD : 0 ≤ D) (G : ℕ → ℝ) (hG0 : G 0 ≤ G₀)
    (hstep : ∀ t, G (t + 1) ≤ ρ * G t + D) :
    ∀ t, G t ≤ ρ ^ t * G₀ + (D * (1 - ρ ^ t)) / (1 - ρ) := by
  intro t
  induction t with
  | zero =>
      have hρ0 : (ρ : ℝ) ^ 0 = 1 := by simp
      rw [hρ0]
      norm_num
      exact hG0
  | succ t ih =>
      have h1 := hstep t
      have hexp : ρ * ρ ^ t = ρ ^ (t + 1) := by
        rw [pow_succ]
        ring
      have hne : (1 - ρ) ≠ 0 := by
        have := ne_of_lt hρ1
        exact fun h => this (by linarith)
      have h2 : ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D
          = ρ ^ (t + 1) * G₀ + D * (1 - ρ ^ (t + 1)) / (1 - ρ) := by
        rw [pow_succ]
        field_simp
        ring
      have hcomb : ρ * G t + D
          ≤ ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := by
        calc ρ * G t + D
            ≤ ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := by
              refine add_le_add_left ?_ D
              exact mul_le_mul_of_nonneg_left ih hρ
          _ = ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := rfl
      -- the goal: G (t+1) <= ρ^{t+1} G0 + D(1-ρ^{t+1})/(1-ρ)
      have hfinal : ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D
          ≤ ρ ^ (t + 1) * G₀ + D * (1 - ρ ^ (t + 1)) / (1 - ρ) :=
        le_of_eq h2
      linarith [h1, hcomb, hfinal]


/-- Конечная геометрическая сумма:
`(a − 1)·Σ_{i<n} a^i = a^n − 1` (любое a). -/
theorem geom_range_identity (a : ℝ) (n : ℕ) :
    (a - 1) * ∑ i ∈ Finset.range n, a^i = a^(n:ℕ) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ a n]
      have e1 : (a - 1) * a^n = a^n * a - a^n := by ring
      have e2 : (a - 1) * (∑ x ∈ Finset.range n, a ^ x + a ^ n)
          = (a - 1) * ∑ x ∈ Finset.range n, a ^ x + (a - 1) * a ^ n := by ring
      rw [e2, ih, e1]
      ring

/-- Если `0 ≤ a`, `0 ≤ s` и `D (t+1) ≤ a·D t + s` при всех t,
то `D t ≤ a^t·D 0 + s·Σ_{i<t} a^i` (любое a ≥ 0;
при `D 0 = 0` и `a < 1` — `D t ≤ s/(1−a)`). -/
theorem disp_recurrence_general {D : ℕ → ℝ} {a s : ℝ}
    (ha : 0 ≤ a) (_hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ a * D t + s) :
    ∀ t, D t ≤ a^t * D 0 + s * ∑ i ∈ Finset.range t, a^i := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 := hstep t
      have hgeom := geom_range_identity a t
      have hsum : ∑ i ∈ Finset.range (t+1), a^i = 1 + a * ∑ i ∈ Finset.range t, a^i := by
        rw [Finset.sum_range_succ]
        nlinarith [hgeom]
      calc D (t+1) ≤ a * D t + s := h1
        _ ≤ a * (a^t * D 0 + s * ∑ i ∈ Finset.range t, a^i) + s := by
            refine add_le_add ?_ (le_refl s)
            exact mul_le_mul_of_nonneg_left ih ha
        _ = a^(t+1) * D 0 + s * (a * ∑ i ∈ Finset.range t, a^i) + s := by
            rw [pow_succ]; ring
        _ = a^(t+1) * D 0 + s * ∑ i ∈ Finset.range (t+1), a^i := by
            rw [hsum]; ring

/-!
## Grokking timescale (R366)

Formal core of the spectral theory of grokking
(arXiv:2609.26679): for homogeneous networks with squared
loss and L2 weight decay, the generalization (grokking)
timescale is controlled by the product `η·λ` of learning
rate and weight decay — residual components decay with rate
`η·λ`, so the time to drive a residual from `r₀` below `ε`
scales as `ln(r₀/ε)/(η·λ)`.

`grokking_threshold_time`: an exact exponential residual
dynamic `r(t+1) = r(t) − η·λ·r(t)` reaches the threshold
`ε` by time `T = ⌈ln(r₀/ε)/(η·λ)⌉` — the inverse-product
scaling law, derived from `(1−ηλ)^T ≤ exp(−ηλT)`.

## References

[1] arXiv:2609.26679 (2026).
-/

/-- The key one-sided exponential bound: for `0 ≤ x ≤ 1`,
`(1−x)^T ≤ exp(−x·T)`. -/
theorem one_sub_pow_le_exp (x : ℝ) (T : ℕ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ T ≤ Real.exp (-(x * T)) := by
  rcases eq_or_lt_of_le hx1 with h1 | h1
  · -- x = 1: LHS = 0^T ≤ exp(-T)
    subst h1
    cases T with
    | zero => norm_num
    | succ T' =>
        have hz : (1 - 1 : ℝ) ^ (T' + 1) = 0 := by
          rw [sub_self, zero_pow]
          norm_num
        rw [hz]
        exact Real.exp_nonneg _
  · -- 0 ≤ x < 1: strict base, take logs
    have hbase : 0 < 1 - x := by linarith
    have hlog1 : Real.log (1 - x) ≤ -x := by
      have h := Real.log_le_sub_one_of_pos hbase
      linarith
    have hln : Real.log ((1 - x) ^ T) = (T:ℝ) * Real.log (1 - x) := by
      rw [Real.log_pow]
    have hmono : (T:ℝ) * Real.log (1 - x) ≤ -x * (T:ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0:ℝ) ≤ (T:ℝ))
      linarith
    have hfinal : Real.log ((1 - x) ^ T) ≤ -x * (T:ℝ) := by
      rw [hln]
      exact hmono
    calc (1 - x) ^ T = Real.exp (Real.log ((1 - x) ^ T)) := by
          rw [Real.exp_log (pow_pos hbase T)]
      _ ≤ Real.exp (-x * (T:ℝ)) := Real.exp_le_exp.mpr hfinal
      _ = Real.exp (-(x * T)) := by congr 1; push_cast; ring

/-- **Grokking threshold time** (R366): under the exact
residual dynamics `r(t+1) = r(t) − η·λ·r(t)` with `η·λ ∈
(0,1]`, the residual at time `T ≥ ln(r₀/ε)/(η·λ)` is at most
`ε` — the inverse-product scaling of the generalization
timescale in `η·λ` (the formal core of the grokking phase
geometry). -/
theorem grokking_threshold_time (eta lam r0 eps : ℝ)
    (heta : 0 < eta) (hlam : 0 < lam) (hr0 : 0 < r0)
    (heps : 0 < eps) (hepsr : eps ≤ r0)
    (hprod : eta * lam ≤ 1)
    (r : ℕ → ℝ)
    (hrec : ∀ t, r (t + 1) = r t - eta * lam * r t)
    (hinit : r 0 = r0)
    (T : ℕ) (hT : Real.log (r0 / eps) / (eta * lam) ≤ T) :
    r T ≤ eps := by
  have hprod0 : 0 ≤ eta * lam := by positivity
  -- closed form: r T = r0 * (1 - eta*lam)^T
  have hform : ∀ t, r t = r0 * (1 - eta * lam) ^ t := by
    intro t
    induction t with
    | zero => simp [hinit]
    | succ t ih =>
        rw [hrec t, ih, pow_succ]
        ring
  rw [hform T]
  have hexp := one_sub_pow_le_exp (eta * lam) T hprod0 hprod
  have hbound : r0 * Real.exp (-(eta * lam * T)) ≤ eps := by
    -- r0 * exp(-(ηλT)) ≤ r0 * exp(-(ηλ·(ln(r0/eps)/(ηλ)))) = eps
    have hexp_le : Real.exp (-(eta * lam * (T:ℝ)))
        ≤ Real.exp (-(eta * lam * (Real.log (r0 / eps) / (eta * lam)))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hT, mul_pos heta hlam]
    have hcancel : eta * lam * (Real.log (r0 / eps) / (eta * lam))
        = Real.log (r0 / eps) := by
      field_simp
    rw [hcancel] at hexp_le
    have hfin : r0 * Real.exp (-(Real.log (r0 / eps))) = eps := by
      have hrpos : (0:ℝ) < r0 / eps := by positivity
      have hinv : Real.exp (-(Real.log (r0 / eps))) = (r0 / eps)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hrpos]
      rw [hinv]
      field_simp
    calc r0 * Real.exp (-(eta * lam * (T:ℝ)))
          ≤ r0 * Real.exp (-(Real.log (r0 / eps))) := by
            exact mul_le_mul_of_nonneg_left hexp_le hr0.le
      _ = eps := hfin
  calc r0 * (1 - eta * lam) ^ T
      = r0 * (1 - eta * lam) ^ T := rfl
    _ ≤ r0 * Real.exp (-(eta * lam * (T:ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hr0.le
    _ ≤ eps := hbound

/-- **Grokking-хвост поверх certified-спуска** (R368):
композиция certified-телескопа и grokking-остатка. Если
потенциал раскладывается как `Φ t = Φ_core t + r t`, где
core-часть убывает certified-шагами (decrease_t ≥ 0 на каждом
шаге), а остаток (probe/генерализационная компонента) следует
grokking-динамике `r(t+1) = r(t) − ηλ·r(t)`, то к моменту
`T ≥ ln(r₀/ε)/(ηλ)`

  Φ T ≤ Φ 0 − ∑ decrease_t + ε:

certified-спуск PLUS погашенный grokking-хвост. Планировщик
(η = 1/L кап, λ из целевого времени, R346/R347/R366)
управляет моментом, когда хвост перестаёт доминировать. -/
theorem certified_descent_with_grokking_tail
    (eta lam r0 eps : ℝ)
    (heta : 0 < eta) (hlam : 0 < lam) (hr0 : 0 < r0)
    (heps : 0 < eps) (hepsr : eps ≤ r0) (hprod : eta * lam ≤ 1)
    (phi dec : ℕ → ℝ) (r : ℕ → ℝ)
    (hphi : ∀ t, phi t = phi 0 - ∑ j ∈ Finset.range t, dec j + r t)
    (hdec : ∀ t, 0 ≤ dec t)
    (hrec : ∀ t, r (t + 1) = r t - eta * lam * r t)
    (hinit : r 0 = r0)
    (T : ℕ) (hT : Real.log (r0 / eps) / (eta * lam) ≤ T) :
    phi T ≤ phi 0 - ∑ t ∈ Finset.range T, dec t + eps := by
  have hgr := grokking_threshold_time eta lam r0 eps heta hlam
    hr0 heps hepsr hprod r hrec hinit T hT
  have := hphi T
  linarith

/-!
## Growing-batch stabilization (R371)

Formal core of the growing-batch convergence results
(Improved Convergence Rates for Stochastic Multi-Gradient
Descent, Corollary 3.1 family; plan §2): under the standard
quadratic-descent recursion

  E(t+1) ≤ ρ·E(t) + η²·σ²/b(t),  ρ = 1 − ηL < 1,

a GEOMETRICALLY growing batch b(t) = b₀·δ^t (δ ≥ 1) makes
the accumulated noise term CONSTANT in T:

  E(T) ≤ ρ^T·E(0) + η²σ² / (b₀·(1 − ρδ⁻¹))     (ρ·δ⁻¹ < 1)

— the noise floor does not accumulate: the tail is
extinguished exactly as the grokking residual (R366/R368),
and the horizon bound is the contraction floor
c/(1−ρ) from `recurrence_upper`. The learning-rate cap
η = 1/L (R347) plus batch scaling (R346) plus this
stabilization complete the schedule algebra.
-/

/-- **Growing-batch stabilization**: under the recursion
`E(t+1) ≤ ρ·E(t) + c·δ^(-t)` with `ρ = 1 − ηL ∈ (0,1)`,
`δ ≥ 1` and `ρ·δ > 1` (batch grows faster than the
contraction decays), for every horizon `T ≥ 1`

  E(T) ≤ ρ^T·E(0) + c·ρ^(T−1) / (1 − (ρδ)⁻¹),

where `c = η²σ²/b₀`: the accumulated stochastic noise dies
at the CONTRACTION rate — geometrically growing batches
extinguish the noise tail completely (plan §2, growing-batch
family of Improved Convergence Rates, Corollary 3.1). -/
theorem growing_batch_stabilized (E : ℕ → ℝ)
    (rho eta L sigma2 b0 delta : ℝ)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hrho_eq : rho = 1 - eta * L)
    (hs2 : 0 ≤ sigma2) (hb0 : 0 < b0) (hdelta : 1 ≤ delta)
    (hrd : 1 < rho * delta)
    (hrec : ∀ t, E (t + 1) ≤ rho * E t
      + eta ^ 2 * sigma2 / (b0 * delta ^ t))
    (T : ℕ) (hT : 1 ≤ T) :
    E T ≤ rho ^ T * E 0
      + (eta ^ 2 * sigma2 / b0) * rho ^ (T - 1)
        / (1 - (rho * delta)⁻¹) := by
  set c : ℝ := eta ^ 2 * sigma2 / b0 with hc
  have hc0 : (0:ℝ) ≤ c := by positivity
  -- exact majorant: E t ≤ rho^t E0 + c * sum_{j<t} rho^(t-1-j) * delta^(-j)
  have hmain : ∀ t : ℕ, E t ≤ rho ^ t * E 0
      + c * (∑ j ∈ Finset.range t,
          rho ^ (t - 1 - j) * (delta ^ (j:ℕ))⁻¹) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hstep := hrec t
        have hsplit : ∑ j ∈ Finset.range (t + 1),
            rho ^ (t + 1 - 1 - j) * (delta ^ (j:ℕ))⁻¹
            = rho * ∑ j ∈ Finset.range t,
                rho ^ (t - 1 - j) * (delta ^ (j:ℕ))⁻¹
              + (delta ^ (t:ℕ))⁻¹ := by
          rw [Finset.sum_range_succ]
          have hlast : rho ^ (t + 1 - 1 - t) * (delta ^ (t:ℕ))⁻¹
              = (delta ^ (t:ℕ))⁻¹ := by
            have h0 : t + 1 - 1 - t = 0 := by omega
            rw [h0, pow_zero, one_mul]
          rw [hlast, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          have hlt : j < t := Finset.mem_range.mp ‹_›
          have hj : t + 1 - 1 - j = (t - 1 - j) + 1 := by omega
          show rho ^ (t + 1 - 1 - j) * (delta ^ (j:ℕ))⁻¹
            = rho * (rho ^ (t - 1 - j) * (delta ^ (j:ℕ))⁻¹)
          rw [hj, pow_succ]
          ring
        calc E (t + 1) ≤ rho * E t
              + eta ^ 2 * sigma2 / (b0 * delta ^ t) := hstep
          _ = rho * E t + c * (delta ^ (t:ℕ))⁻¹ := by
              have hd0 : (0:ℝ) < delta ^ t := by positivity
              rw [hc]
              field_simp
          _ ≤ rho * (rho ^ t * E 0
              + c * ∑ j ∈ Finset.range t,
                  rho ^ (t - 1 - j) * (delta ^ (j:ℕ))⁻¹)
              + c * (delta ^ (t:ℕ))⁻¹ :=
              add_le_add (mul_le_mul_of_nonneg_left ih hrho.le) le_rfl
          _ = rho ^ (t + 1) * E 0
              + c * (rho * ∑ j ∈ Finset.range t,
                  rho ^ (t - 1 - j) * (delta ^ (j:ℕ))⁻¹
                + (delta ^ (t:ℕ))⁻¹) := by
              rw [pow_succ]
              ring
          _ = rho ^ (t + 1) * E 0
              + c * ∑ j ∈ Finset.range (t + 1),
                  rho ^ (t + 1 - 1 - j) * (delta ^ (j:ℕ))⁻¹ := by
              rw [hsplit]
  -- the exact tail sums as rho^(t-1) * sum (rho*delta)^(-j)
  have hrpdinv : (0:ℝ) ≤ (rho * delta)⁻¹ := by positivity
  have hrpd1 : (rho * delta)⁻¹ < 1 := by
    rw [inv_lt_one₀ (mul_pos hrho (by linarith : (0:ℝ) < delta))]
    exact hrd
  have htail : ∑ j ∈ Finset.range T,
      rho ^ (T - 1 - j) * (delta ^ (j:ℕ))⁻¹
      = rho ^ (T - 1)
        * ∑ j ∈ Finset.range T, ((rho * delta) ^ (j:ℕ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hmem : j < T := Finset.mem_range.mp ‹_›
    have hj' : j ≤ T - 1 := by omega
    have hpow : rho ^ (T - 1)
        = rho ^ (T - 1 - j) * rho ^ j := by
      rw [← pow_add]
      congr 1
      omega
    have hinvpow : ((rho * delta) ^ (j:ℕ))⁻¹
        = (rho ^ j)⁻¹ * (delta ^ (j:ℕ))⁻¹ := by
      rw [mul_pow, mul_inv]
    show rho ^ (T - 1 - j) * (delta ^ (j:ℕ))⁻¹
      = rho ^ (T - 1) * ((rho * delta) ^ (j:ℕ))⁻¹
    rw [hpow, hinvpow]
    field_simp
  have hgeom0 := geom_sum_le_inv (rho := (rho * delta)⁻¹) T hrpdinv hrpd1
  have hgeom : ∑ j ∈ Finset.range T, ((rho * delta) ^ (j:ℕ))⁻¹
      ≤ 1 / (1 - (rho * delta)⁻¹) := by
    have heq : ∑ j ∈ Finset.range T, ((rho * delta) ^ (j:ℕ))⁻¹
        = ∑ j ∈ Finset.range T, (rho * delta)⁻¹ ^ (j:ℕ) :=
      Finset.sum_congr rfl fun j _ => (inv_pow (rho * delta) j).symm
    rw [heq]
    exact hgeom0
  have hfinal := hmain T
  rw [htail] at hfinal
  have hrhoT : (0:ℝ) ≤ rho ^ (T - 1) := by positivity
  calc E T ≤ rho ^ T * E 0
        + c * (rho ^ (T - 1)
          * ∑ j ∈ Finset.range T, ((rho * delta) ^ (j:ℕ))⁻¹) := hfinal
    _ ≤ rho ^ T * E 0
        + c * (rho ^ (T - 1) * (1 / (1 - (rho * delta)⁻¹))) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgeom hrhoT) hc0)
    _ = rho ^ T * E 0
        + (eta ^ 2 * sigma2 / b0) * rho ^ (T - 1)
          / (1 - (rho * delta)⁻¹) := by
        rw [hc]
        field_simp

end Hagi.Foundations

namespace Hagi
export Hagi.Foundations (one_sub_pow_le_exp grokking_threshold_time certified_descent_with_grokking_tail growing_batch_stabilized)
end Hagi

