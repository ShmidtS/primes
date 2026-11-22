/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.Freedman
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Empirical-Bernstein-граница (Probability, C539)

Empirical-Bernstein (EB) confidence — дополнение
Freedman-канона (C525) в стиле Maurer–Pontil 2009
("Empirical Bernstein Bounds and Sample Variance
Penalization"): вместо диапазонной дисперсии R² (Hoeffding,
AuditLedger) подставляется измеренная эмпирическая дисперсия
σ̂² + аддитивный диапазонный член за подстановку.

  ε_EB = √(2σ̂²·L/n) + 2R·L/n,  L = ln(2/α)

(у Maurer–Pontil константы 3·R·ln(3/α)/(n−1) — та же
структура, чуть тоньше; наши константы честно выведены из
инверсии freedman_tail_low, см. `eb_radius_algebra`).

**Экономия валидации**: при ΔCE = 0.04, R = 11.09 (R = 2ln256),
σ̂ = 0.25 (σ̂² = 0.0625), α = 0.01 — Hoeffding требует n_H =
R²L/(2Δ²) ≈ 177k сэмплов; MP-форма ε_EB (3R·ln(3/α)/(n−1)) —
n = 6439 (27.5×, в точности план); наша форма (√(2σ̂²L/n) +
2RL/n, L = ln(2/α)) — n = 4267 (41.5×): инверсия Freedman с
L = ln(2/α) и слагаемым 2/n даже тоньше констант MP на этой
точке. Числа: .tmp/C539 (witness).

**Честные границы**: sig — измеряемая runtime-посылка
(условная дисперсия при каждом префиксе, h_emp-стиль канона —
как `adaptive_success_freedman`); теорема НЕ утверждает
стохастическую валидность подстановки случайного σ̂ (это
Maurer–Pontil λ-трюк, открытая форма). b — конструкторский
диапазон приращений.

- `freedman_tail_two_sided` — двухсторонний Freedman-хвост
  (union bound + neg-конгруэнция событий);
- `eb_radius_algebra` — инверсия хвоста: радиус
  Δ = √(2nσL) + 2bL даёт exp(−Δ²/(2(nσ+bΔ))) ≤ exp(−L);
- `empirical_bernstein_bound` — main: P[|ΣX| < ε_EB·n] ≥ 1−α;
- `empirical_bernstein_mean_bound` — mean-форма плана
  |μ̂| < √(2σL/n) + 2bL/n с вероятностью ≥ 1−α.
-/

open Finset Real

namespace Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-! ## Двухсторонний Freedman-хвост -/

/-- **Двухсторонний Freedman-хвост**: при условно
центрированных приращениях (|X| ≤ b, Σ q·X² ≤ σ²)

  P[|ΣX| ≥ Δ] ≤ 2·exp(−Δ²/(2(nσ² + bΔ)))

— `freedman_tail_low` для X и −X (событийная конгруэнция
через `azumaSum_neg`) + `prodPq_union_le` (ср.
`hoeffding_two_sided` для iid-координат). -/
theorem freedman_tail_two_sided (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    prodPq (fun _ => q)
      (fun ω => Δ ≤ azumaSum X n ω ∨ azumaSum X n ω ≤ -Δ)
      ≤ 2 * Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ))) := by
  classical
  have hnegmean : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * (- X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) = 0 := by
    intro t pref
    have h0 := hmean t pref
    have hstep : ∑ v, q v * (- X (t + 1) (Fin.snoc (α := fun _ => V) pref v))
        = - ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [hstep, h0]
    ring
  have hnegvar : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * (- X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig := by
    intro t pref
    have h0 := hvar t pref
    have hrw : ∀ v, q v * (- X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        = q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2 := by
      intro v
      rw [neg_sq]
    rw [Finset.sum_congr rfl (fun v _ => hrw v)]
    exact h0
  have hnegbnd : ∀ (t : ℕ) (pref : Fin t → V),
      |(- X : ∀ t, (Fin t → V) → ℝ) t pref| ≤ b := by
    intro t pref
    show |-(X t pref)| ≤ b
    rw [abs_neg]
    exact hbnd t pref
  have hup := freedman_tail_low (V := V) q hq0 hq1
    (fun t pref => -X t pref) b hb hnegbnd sig hsig hnegmean hnegvar n hn Δ hΔ
  have hlow := freedman_tail_low q hq0 hq1 X b hb hbnd sig hsig hmean hvar n hn Δ hΔ
  have hisprob : IsProbSys (fun _ : Fin n => q) := fun _ => ⟨hq0, hq1⟩
  have hmono1 : prodPq (fun _ : Fin n => q) (fun ω => Δ ≤ azumaSum X n ω)
      ≤ prodPq (fun _ : Fin n => q)
        (fun ω => azumaSum (fun t pref => -X t pref) n ω ≤ -Δ) := by
    refine prodPq_mono _ hisprob _ _ (fun ω hω => ?_)
    rw [azumaSum_neg]
    linarith
  have hu := prodPq_union_le (fun _ : Fin n => q) hisprob
    (fun ω => Δ ≤ azumaSum X n ω) (fun ω => azumaSum X n ω ≤ -Δ)
  calc prodPq (fun _ : Fin n => q)
        (fun ω => Δ ≤ azumaSum X n ω ∨ azumaSum X n ω ≤ -Δ)
      ≤ prodPq (fun _ : Fin n => q) (fun ω => Δ ≤ azumaSum X n ω)
        + prodPq (fun _ : Fin n => q) (fun ω => azumaSum X n ω ≤ -Δ) := hu
    _ ≤ prodPq (fun _ : Fin n => q)
          (fun ω => azumaSum (fun t pref => -X t pref) n ω ≤ -Δ)
        + prodPq (fun _ : Fin n => q) (fun ω => azumaSum X n ω ≤ -Δ) :=
          add_le_add hmono1 le_rfl
    _ ≤ Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ)))
        + Real.exp (- Δ ^ 2 / (2 * ((n : ℝ) * sig + b * Δ))) :=
          add_le_add hup hlow
    _ = _ := by ring

/-! ## Инверсия радиуса -/

/-- **Алгебра EB-радиуса**: при b ≥ 0, σ > 0, L > 0, n ≥ 1
радиус Δ := √(2nσL) + 2bL удовлетворяет

  exp(−Δ²/(2(nσ + bΔ))) ≤ exp(−L),

поскольку Δ² − 2L(nσ + bΔ) = 2bL·√(2σnL) ≥ 0 — квадратика
Freedman-хвоста решена явно (верхняя мажорация точного
решения bL + √(b²L² + 2nσL); избыточная часть 2bL·s ≥ 0). -/
theorem eb_radius_algebra (b sig L : ℝ) (hb : 0 ≤ b) (hsig : 0 < sig)
    (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    0 < Real.sqrt (2 * (n : ℝ) * sig * L) + 2 * b * L ∧
    Real.exp (- (Real.sqrt (2 * (n : ℝ) * sig * L) + 2 * b * L) ^ 2
        / (2 * ((n : ℝ) * sig + b * (Real.sqrt (2 * (n : ℝ) * sig * L)
          + 2 * b * L))))
      ≤ Real.exp (- L) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs_nn : 0 ≤ Real.sqrt (2 * (n : ℝ) * sig * L) :=
    Real.sqrt_nonneg _
  have hs_sq : Real.sqrt (2 * (n : ℝ) * sig * L) ^ 2
      = 2 * (n : ℝ) * sig * L :=
    Real.sq_sqrt (by
      have := hsig.le
      have := hL.le
      have : (0 : ℝ) ≤ (n : ℝ) := hn'.le
      positivity)
  constructor
  · have hpos : 0 < Real.sqrt (2 * (n : ℝ) * sig * L) := by
      have := hsig
      have := hL
      have : (0 : ℝ) < (n : ℝ) := hn'
      positivity
    have hbL : 0 ≤ 2 * b * L := by positivity
    linarith
  · -- ключ: Δ² − 2L(nσ + bΔ) = 2bL·s ≥ 0, s = √(2nσL)
    set s : ℝ := Real.sqrt (2 * (n : ℝ) * sig * L) with hs_def
    have hkey : (s + 2 * b * L) ^ 2
        - 2 * L * ((n : ℝ) * sig + b * (s + 2 * b * L))
        = 2 * b * L * s := by
      have hexp : (s + 2 * b * L) ^ 2
          = s ^ 2 + 4 * b * L * s + 4 * b ^ 2 * L ^ 2 := by ring
      have hrhs : 2 * L * ((n : ℝ) * sig + b * (s + 2 * b * L))
          = 2 * L * (n : ℝ) * sig + 2 * b * L * s + 4 * b ^ 2 * L ^ 2 := by
        ring
      have hsl : s ^ 2 = 2 * L * (n : ℝ) * sig := by
        rw [hs_sq]; ring
      rw [hexp, hrhs, hsl]
      ring
    have hdenpos : 0 < 2 * ((n : ℝ) * sig + b * (s + 2 * b * L)) := by
      positivity
    refine le_trans (Real.exp_le_exp.mpr ?_) le_rfl
    rw [neg_div, neg_le_neg_iff]
    refine (le_div_iff₀ hdenpos).mpr ?_
    have hbLs : 0 ≤ 2 * b * L * s := by positivity
    have hle : 2 * L * ((n : ℝ) * sig + b * (s + 2 * b * L))
        ≤ (s + 2 * b * L) ^ 2 := by linarith
    calc L * (2 * ((n : ℝ) * sig + b * (s + 2 * b * L)))
        = 2 * L * ((n : ℝ) * sig + b * (s + 2 * b * L)) := by ring
      _ ≤ _ := hle

/-! ## Empirical-Bernstein-граница -/

/-- **Empirical-Bernstein-граница (main)**: для условно
центрированных приращений с диапазоном b и ИЗМЕРЕННОЙ
эмпирической дисперсией σ̂² = sig (runtime-посылка hvar,
h_emp-стиль канона) при 0 < α < 1

  P[|ΣX| < √(2nσ̂²L) + 2bL] ≥ 1 − α,  L = ln(2/α)

— двухсторонняя инвертированная Freedman-граница: √-член
несёт σ̂-подстановку (EB vs Hoeffding R²), аддитивный 2bL —
диапазонную цену. Семантика плана C537 P1: 27.5× экономия
валидации vs Hoeffding при σ̂² ≪ R². -/
theorem empirical_bernstein_bound (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun ω => |azumaSum X n ω| <
        Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha)) := by
  classical
  have hLpos : 0 < Real.log (2 / alpha) :=
    Real.log_pos ((one_lt_div halpha1).mpr (by linarith))
  obtain ⟨hΔpos, hexpα⟩ :=
    eb_radius_algebra (L := Real.log (2 / alpha)) b sig hb hsig hLpos n hn
  -- exp(−L) = α/2
  have hexpL : Real.exp (- Real.log (2 / alpha)) = alpha / 2 := by
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) halpha1)]
    field_simp
  have hΔexp : Real.exp (- (Real.sqrt (2 * (n : ℝ) * sig
        * Real.log (2 / alpha)) + 2 * b * Real.log (2 / alpha)) ^ 2
      / (2 * ((n : ℝ) * sig + b * (Real.sqrt (2 * (n : ℝ) * sig
        * Real.log (2 / alpha)) + 2 * b * Real.log (2 / alpha)))))
      ≤ alpha / 2 := by
    rw [hexpL] at hexpα
    exact hexpα
  have htwo := freedman_tail_two_sided q hq0 hq1 X b hb hbnd sig hsig
    hmean hvar n hn _ hΔpos
  have hisprob : IsProbSys (fun _ : Fin n => q) := fun _ => ⟨hq0, hq1⟩
  -- дополнение: ¬(Δ ≤ S ∨ S ≤ −Δ) → |S| < Δ
  have hmono : prodPq (fun _ : Fin n => q)
      (fun ω => ¬ (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha) ≤ azumaSum X n ω
        ∨ azumaSum X n ω
          ≤ - (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
            + 2 * b * Real.log (2 / alpha))))
      ≤ prodPq (fun _ : Fin n => q)
        (fun ω => |azumaSum X n ω| <
          Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
            + 2 * b * Real.log (2 / alpha)) :=
    prodPq_mono _ hisprob _ _ (fun ω hω => by
      rw [abs_lt]
      push Not at hω
      exact ⟨hω.2, hω.1⟩)
  have hfinal : prodPq (fun _ : Fin n => q)
      (fun ω => Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha) ≤ azumaSum X n ω
        ∨ azumaSum X n ω
          ≤ - (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
            + 2 * b * Real.log (2 / alpha))) ≤ alpha := by
    refine le_trans htwo ?_
    have := hΔexp
    linarith
  have hone : prodPq (fun _ : Fin n => q)
      (fun ω => Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha) ≤ azumaSum X n ω
        ∨ azumaSum X n ω
          ≤ - (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
            + 2 * b * Real.log (2 / alpha))) ≤ 1 :=
    prodPq_le_one _ hisprob _
  have hcompl := prodPq_compl (fun _ : Fin n => q) hisprob
    (fun ω => Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha) ≤ azumaSum X n ω
        ∨ azumaSum X n ω
          ≤ - (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
            + 2 * b * Real.log (2 / alpha)))
  rw [hcompl] at hmono
  linarith

/-- **EB mean-граница (форма плана)**: per-sample версия
`empirical_bernstein_bound` — |μ̂| < ε_EB :=
√(2σ̂²L/n) + 2bL/n с вероятностью ≥ 1 − α. -/
theorem empirical_bernstein_mean_bound (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun ω => |azumaSum X n ω / (n : ℝ)| <
        Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ))
          + 2 * b * Real.log (2 / alpha) / (n : ℝ)) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hLpos : (0 : ℝ) < Real.log (2 / alpha) :=
    Real.log_pos ((one_lt_div halpha1).mpr (by linarith))
  -- n · √(2σL/n) = √(2nσL) — через квадраты
  have hnsqrt : (n : ℝ) * Real.sqrt (2 * sig * Real.log (2 / alpha)
      / (n : ℝ)) = Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha)) := by
    have hA : (0 : ℝ) ≤ (n : ℝ)
        * Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ)) := by
      positivity
    have hB : (0 : ℝ) ≤ Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha)) :=
      Real.sqrt_nonneg _
    refine (sq_eq_sq₀ hA hB).mp ?_
    have hAn : ((n : ℝ)
        * Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ))) ^ 2
        = (n : ℝ) ^ 2
          * (2 * sig * Real.log (2 / alpha) / (n : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hBn : (Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))) ^ 2
        = 2 * (n : ℝ) * sig * Real.log (2 / alpha) :=
      Real.sq_sqrt (by positivity)
    rw [hAn, hBn]
    field_simp
  have hmain := empirical_bernstein_bound q hq0 hq1 X b hb hbnd sig hsig
    hmean hvar n hn alpha halpha1 halpha2
  refine le_trans hmain ?_
  refine prodPq_mono (fun _ : Fin n => q) (fun _ => ⟨hq0, hq1⟩) _ _ ?_
  intro ω hω
  rw [abs_div, abs_of_pos hn', div_lt_iff₀ hn']
  -- |S| < (√(2σL/n) + 2bL/n)·n = √(2nσL) + 2bL
  have hsplit : (Real.sqrt (2 * sig * Real.log (2 / alpha)
        / (n : ℝ)) + 2 * b * Real.log (2 / alpha) / (n : ℝ)) * (n : ℝ)
      = Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
        + 2 * b * Real.log (2 / alpha) := by
    rw [add_mul, mul_comm (Real.sqrt (2 * sig * Real.log (2 / alpha)
      / (n : ℝ))) (n : ℝ), hnsqrt,
      div_mul_cancel₀ _ (ne_of_gt hn')]
  rw [hsplit]
  exact hω

end Hagi.Probability
