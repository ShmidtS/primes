/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Probability.GibbsCore
import Hagi.Probability.GibbsCooling
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.FannesPinsker
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.MomentBounds
import Hagi.Probability.FreedmanTwoSided

set_option linter.style.header false

/-!
# MirrorHedge — консолидированный канон зеркального шага (C236)

Единый модуль для семейства экспоненциальных весов: Gibbs-концентрация
(R498+), MWU-потенциал (R433+), зеркальный шаг (вариационный принцип),
Hedge-роутинг и survivor-склейка аудита v5 (C228).
Слияние C236: файлы Probability/GibbsConcentration, Probability/MWU,
Optimization/MirrorDescent, Autonomy/Hedge, Autonomy/HedgeSurvivor
перенесены сюда байт-в-байт (пространства имён сохранены).
-/

section C236_gc
namespace Hagi.Probability

open Finset Real Filter

/-- **Экспоненциальное затухание флуктуаций энергии Гиббса (R498)**:
если все энергии лежат в [E*, E* + Δ] и есть зазор δ > 0,
то дисперсия энергии при распределении Гиббса не превосходит
Δ² · (n−1) · exp(−δ/T). Доказательство связывает R393
(экспоненциальная оценка избытка среднего) с R496
(Бхатия—Дэвис: Var ≤ (b−μ)(μ−a)). Это даёт сертифицированную
границу энергетических флуктуаций для термостатного stop-gate. -/
theorem gibbs_energy_variance_bound
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : V → ℝ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
    let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
    let μ : ℝ := ∑ v : V, p v * E v
    ∑ v : V, p v * (E v - μ) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
  let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
  let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
  let μ : ℝ := ∑ v : V, p v * E v
  change ∑ v : V, p v * (E v - μ) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T)
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hp : ∀ v : V, 0 < p v := by
    intro v
    dsimp [p]
    exact div_pos (Real.exp_pos _) hZpos
  have hp1 : ∑ v : V, p v = 1 := by
    have hsd : ∑ v : V, Real.exp (-(E v) / T) / Z
        = (∑ v : V, Real.exp (-(E v) / T)) / Z :=
      (Finset.sum_div Finset.univ (fun v => Real.exp (-(E v) / T)) Z).symm
    rw [hsd]
    exact div_self hZpos.ne'
  -- Convert the normalized Gibbs mean into the partition-function form R393.
  have hμeq : μ =
      (∑ v : V, E v * Real.exp (-(E v) / T)) / Z := by
    calc
      μ = ∑ v : V, p v * E v := rfl
      _ = ∑ v : V, (E v * Real.exp (-(E v) / T)) / Z := by
        apply Finset.sum_congr rfl
        intro v _
        change (Real.exp (-(E v) / T) / Z) * E v
          = (E v * Real.exp (-(E v) / T)) / Z
        ring
      _ = (∑ v : V, E v * Real.exp (-(E v) / T)) / Z := by
        rw [Finset.sum_div]
  have hmean := gibbs_expected_energy_bound E δ T hT vstar Δ hmin hgap hΔ
  have hμupper : μ ≤ E vstar
      + Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
    rw [hμeq]
    simpa [Z] using hmean
  have hΔ0 : (0:ℝ) ≤ Δ := by
    have h := hΔ vstar
    simpa using h
  have hconst : ∑ v : V, p v * E vstar = E vstar := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (p v) (E vstar)),
      ← Finset.mul_sum, hp1, mul_one]
  have hμlower : E vstar ≤ μ := by
    calc
      E vstar = ∑ v : V, p v * E vstar := hconst.symm
      _ ≤ ∑ v : V, p v * E v :=
        Finset.sum_le_sum (fun v _ =>
          mul_le_mul_of_nonneg_left (hmin v) (le_of_lt (hp v)))
      _ = μ := rfl
  have hconstB : ∑ v : V, p v * (E vstar + Δ) = E vstar + Δ := by
    rw [Finset.sum_congr rfl
        (fun v _ => mul_comm (p v) (E vstar + Δ)),
      ← Finset.mul_sum, hp1, mul_one]
  have hμleB : μ ≤ E vstar + Δ := by
    calc
      μ = ∑ v : V, p v * E v := rfl
      _ ≤ ∑ v : V, p v * (E vstar + Δ) :=
        Finset.sum_le_sum (fun v _ =>
          mul_le_mul_of_nonneg_left (by linarith [hΔ v]) (le_of_lt (hp v)))
      _ = E vstar + Δ := hconstB
  have hmeanExcess : μ - E vstar
      ≤ Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
    linarith [hμupper]
  -- Apply the sharper Bhatia-Davis variance inequality (R496).
  have hbd := bhatia_davis p E (E vstar) (E vstar + Δ) hp hp1
    hmin (fun v => by linarith [hΔ v])
  have hvar : ∑ v : V, p v * (E v - μ) ^ 2
      ≤ (E vstar + Δ - μ) * (μ - E vstar) := by
    simpa [μ] using hbd
  have hfactor1 : E vstar + Δ - μ ≤ Δ := by
    linarith [hμlower]
  have hfactor2 : (0:ℝ) ≤ μ - E vstar := by
    linarith [hμlower]
  calc
    ∑ v : V, p v * (E v - μ) ^ 2
        ≤ (E vstar + Δ - μ) * (μ - E vstar) := hvar
    _ ≤ Δ * (μ - E vstar) :=
      mul_le_mul_of_nonneg_right hfactor1 hfactor2
    _ ≤ Δ * (Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T)) :=
      mul_le_mul_of_nonneg_left hmeanExcess hΔ0
    _ = Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by ring

/-- Термостатный variance-stop сертификат: если
Δ²·(n−1)·e^{−δ/T} <= eps, то Var_{p_T}(E) <= eps. -/
theorem thermostat_var_stop {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (δ T eps : ℝ)
    (hδ : 0 < δ) (hT : 0 < T) (heps : 0 ≤ eps)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ)
    (hgate : Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-δ / T) ≤ eps) :
    let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
    let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
    let μ : ℝ := ∑ v : V, p v * E v
    ∑ v : V, p v * (E v - μ) ^ 2 ≤ eps := by
  intro Z p μ
  exact le_trans (gibbs_energy_variance_bound E δ T hδ hT vstar Δ
    hmin hgap hΔ) hgate

/-- Явный температурный порог: при T <= δ / ln(Δ²(n−1)/eps)
гейт выполнен (eps > 0, Δ²(n−1) > eps-ветка). -/
theorem thermostat_threshold {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (δ T eps : ℝ)
    (hδ : 0 < δ) (hT : 0 < T) (heps : 0 < eps)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ)
    (hΔpos : 0 < Δ)
    (hcard : 0 < (((Finset.univ.erase vstar).card : ℕ) : ℝ))
    (hTle : T ≤ δ / Real.log (Δ ^ 2
      * (((Finset.univ.erase vstar).card : ℕ) : ℝ) / eps)) :
    Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-(δ / T)) ≤ eps := by
  set c : ℝ := Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ) with hc
  have hcpos : (0:ℝ) < c := by
    rw [hc]
    positivity
  -- log(c/eps) > 0 since T > 0 and T <= delta/log(c/eps) implies log(c/eps) > 0
  have hlogpos : (0:ℝ) < Real.log (c / eps) := by
    by_contra hlog
    push_neg at hlog
    rcases lt_or_eq_of_le hlog with hlogneg | hlog0
    · have h1 : δ / Real.log (c / eps) < 0 :=
        div_neg_of_pos_of_neg hδ hlogneg
      have h2 : T ≤ δ / Real.log (c / eps) := hTle
      linarith
    · rw [hlog0] at hTle
      have hdiv : δ / (0:ℝ) ≤ 0 := by
        apply div_nonpos_of_nonneg_of_nonpos
        · exact le_of_lt hδ
        · norm_num
      have : T ≤ 0 := le_trans hTle hdiv
      linarith
  -- so c/eps > 1, i.e. eps < c
  have hceps : eps < c := by
    have h1 : (1:ℝ) ≤ c / eps := by
      have := Real.one_le_exp (by linarith : (0:ℝ) ≤ Real.log (c / eps))
      rw [Real.exp_log (show (0:ℝ) < c / eps from div_pos hcpos heps)] at this
      exact this
    rw [le_div_iff₀ heps] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · -- c = eps contradicts log(c/eps) > 0
      rw [one_mul] at h
      rw [← h] at hlogpos
      rw [div_self heps.ne'] at hlogpos
      rw [Real.log_one] at hlogpos
      linarith
  have hdTpos : (0:ℝ) < δ / T := div_pos hδ hT
  -- key: log(c/eps) <= delta/T from T <= delta/L
  have hkey : Real.log (c / eps) ≤ δ / T := by
    rw [le_div_iff₀ hT]
    have := hTle
    rw [le_div_iff₀ hlogpos] at this
    -- this : T * log(c/eps) <= delta
    linarith [this]
  -- exp(-L) = (c/eps)^{-1} = eps/c; c * eps/c = eps
  have hexplog : Real.exp (-(Real.log (c / eps))) = eps / c := by
    rw [Real.exp_neg, Real.exp_log (show (0:ℝ) < c / eps from div_pos hcpos heps)]
    rw [inv_div]
  calc c * Real.exp (-(δ / T))
      ≤ c * Real.exp (-(Real.log (c / eps))) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (show -(δ / T) ≤ -(Real.log (c / eps)) from
              neg_le_neg hkey)) (le_of_lt hcpos)
    _ = c * (eps / c) := by rw [hexplog]
    _ = eps := mul_div_cancel₀ eps (by linarith : c ≠ 0)

/-- Сходимость флуктуаций к нулю вдоль графика T_n = δ/(n+1):
Var_{p_{T_n}}(E) <= Δ²(n−1)e^{−(n+1)} -> 0. -/
theorem gibbs_var_tendsto_zero {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    Tendsto (fun n => ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
      * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2)
      atTop (nhds 0) := by
  -- temperature schedule
  have hTn : ∀ n, (0:ℝ) < δ/((n+1 : ℕ) : ℝ) := fun n =>
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  -- per-n bound from gibbs_energy_variance_bound
  have hbd : ∀ n : ℕ, ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
      * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / (δ/((n+1 : ℕ) : ℝ))) := by
    intro n
    exact gibbs_energy_variance_bound E δ (δ/((n+1 : ℕ) : ℝ)) hδ
      (hTn n) vstar Δ hmin hgap hΔ
  -- collapse -δ/(δ/(n+1)) = -(n+1)
  have hkey : ∀ n : ℕ, -δ / (δ/((n+1 : ℕ) : ℝ))
      = -((n+1 : ℕ) : ℝ) := by
    intro n
    field_simp
  -- the bound tends to 0: const * (const * exp(-(n+1)))
  have hzero : Tendsto (fun n => Δ ^ 2
      * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
      * Real.exp (-((n+1 : ℕ) : ℝ))) atTop (nhds 0) := by
    have hexp : Tendsto (fun n => Real.exp (-((n+1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
    have hconst : Tendsto (fun n : ℕ => Δ ^ 2
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) atTop
        (nhds (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ))) :=
      tendsto_const_nhds
    simpa [mul_zero] using hconst.mul hexp
  -- squeeze: 0 <= Var_n <= bound_n -> 0
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
      * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2 := by
    intro n
    refine Finset.sum_nonneg (fun v _ => ?_)
    have hZpos : (0:ℝ) < ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))) :=
      Finset.sum_pos (fun w _ => Real.exp_pos _)
        ⟨Classical.arbitrary V, Finset.mem_univ (Classical.arbitrary V)⟩
    exact mul_nonneg
      (div_pos (Real.exp_pos _) hZpos).le (sq_nonneg _)
  -- rewrite the bound into the exp(-(n+1)) form for the squeeze
  have hbd2 : ∀ n : ℕ, ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
      * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2
      ≤ Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-((n+1 : ℕ) : ℝ)) := by
    intro n
    rw [← hkey n]
    exact hbd n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
    hzero hnn hbd2

/-- Явная граница шагов: при (n+1) >= ln(c/eps), c = Δ²(n−1),
Var_{p_{T_n}}(E) <= eps, T_n = delta/(n+1).  Если c <= eps —
тривиально (граница <= c <= eps). -/
theorem gibbs_var_steps_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (δ : ℝ) (eps : ℝ)
    (hδ : 0 < δ) (heps : 0 < eps)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ)
    (hcard : 0 < (((Finset.univ.erase vstar).card : ℕ) : ℝ))
    (hΔpos : 0 < Δ)
    (n : ℕ)
    (hn : (Real.log (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ) / eps) : ℝ) ≤ (n + 1 : ℕ)) :
    ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
      * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
        / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2
      ≤ eps := by
  -- everything in explicit form (no set — R504/R512 lessons)
  have hcpos : (0:ℝ) < (Δ ^ 2
      * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) :=
    mul_pos (sq_pos_of_pos hΔpos) hcard
  have hTn : (0:ℝ) < δ/((n+1 : ℕ) : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr n.succ_pos)
  have hbd := gibbs_energy_variance_bound E δ (δ/((n+1 : ℕ) : ℝ)) hδ
    hTn vstar Δ hmin hgap hΔ
  have hkey : -δ / (δ/((n+1 : ℕ) : ℝ)) = -((n+1 : ℕ) : ℝ) := by
    field_simp
  rw [hkey] at hbd
  by_cases hce : (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) ≤ eps
  · -- degenerate: bound <= c * 1 <= eps
    have hexp1 : Real.exp (-((n+1 : ℕ) : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
          / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
        * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
          / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2
        ≤ (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          * Real.exp (-((n+1 : ℕ) : ℝ)) := hbd
      _ ≤ (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hexp1 (le_of_lt hcpos)
      _ ≤ eps := by rwa [mul_one]
  · -- main: log(c/eps) > 0 and exp(-(n+1)) <= eps/c
    have hlogpos : (0:ℝ) < Real.log (Δ ^ 2
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ) / eps) := by
      by_contra hlog
      push_neg at hlog
      have hexp : Real.exp (Real.log (Δ ^ 2
          * (((Finset.univ.erase vstar).card : ℕ) : ℝ) / eps)) ≤ 1 :=
        Real.exp_le_one_iff.mpr hlog
      have h1 : Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
          / eps ≤ 1 := by
        rwa [Real.exp_log (div_pos hcpos heps)] at hexp
      rw [div_le_iff₀ heps, one_mul] at h1
      linarith
    have hexplog : Real.exp (-(Real.log (Δ ^ 2
        * (((Finset.univ.erase vstar).card : ℕ) : ℝ) / eps)))
        = eps / (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (div_pos hcpos heps), inv_div]
    have hexp : Real.exp (-((n+1 : ℕ) : ℝ))
        ≤ eps / (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ)) :=
      le_trans (Real.exp_le_exp.mpr (neg_le_neg hn)) (le_of_eq hexplog)
    -- final chain: Var <= c*exp(-(n+1)) <= c*(eps/c) = eps
    calc ∑ v, (Real.exp (-(E v)/(δ/((n+1 : ℕ) : ℝ)))
          / ∑ w, Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ))))
        * (E v - ∑ w, (Real.exp (-(E w)/(δ/((n+1 : ℕ) : ℝ)))
          / ∑ u, Real.exp (-(E u)/(δ/((n+1 : ℕ) : ℝ)))) * E w) ^ 2
        ≤ (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          * Real.exp (-((n+1 : ℕ) : ℝ)) := hbd
      _ ≤ (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ))
          * (eps / (Δ ^ 2 * (((Finset.univ.erase vstar).card : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (le_of_lt hcpos)
      _ = eps := mul_div_cancel₀ eps (by
            exact ne_of_gt hcpos)

/-- Standalone mean-excess certificate in P-form:
⟨E⟩_{p_T} - E* <= Δ(n−1)e^{−δ/T} (R393 repackaged with
normalized Gibbs weights).  Combined with var_le_delta_excess
R513 yields the variance gate directly from the excess
certificate (no exponential indentation). -/
theorem gibbs_excess_mean_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (E : V → ℝ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (vstar : V) (Δ : ℝ)
    (hmin : ∀ v, E vstar ≤ E v)
    (hgap : ∀ v, v ≠ vstar → E vstar + δ ≤ E v)
    (hΔ : ∀ v, E v - E vstar ≤ Δ) :
    let Z : ℝ := ∑ v, Real.exp (-(E v) / T)
    let p : V → ℝ := fun v => Real.exp (-(E v) / T) / Z
    ∑ v : V, p v * E v - E vstar
      ≤ Δ * (((Finset.univ.erase vstar).card : ℕ) : ℝ)
        * Real.exp (-δ / T) := by
  intro Z p
  have hZpos : (0:ℝ) < Z :=
    Finset.sum_pos (fun v _ => Real.exp_pos _)
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hp1 : ∑ v : V, p v = 1 := by
    have hsd : ∑ v : V, Real.exp (-(E v) / T) / Z
        = (∑ v : V, Real.exp (-(E v) / T)) / Z :=
      (Finset.sum_div Finset.univ (fun v => Real.exp (-(E v) / T)) Z).symm
    rw [hsd]
    exact div_self hZpos.ne'
  have hμeq : ∑ v : V, p v * E v
      = (∑ v : V, E v * Real.exp (-(E v) / T)) / Z := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [show p v * E v = (E v * Real.exp (-(E v) / T)) / Z from by
      rw [div_mul_eq_mul_div, mul_comm]]
  have hmean := gibbs_expected_energy_bound E δ T hT vstar Δ hmin hgap hΔ
  have hconst : ∑ v : V, p v * E vstar = E vstar := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (p v) (E vstar)),
      ← Finset.mul_sum, hp1, mul_one]
  -- R393 is already in P-form: ⟨E⟩ ≤ E* + Δ(n−1)e^{−δ/T}
  have hR := gibbs_expected_energy_bound E δ T hT vstar Δ hmin hgap hΔ
  -- hR : (∑ E e)/Z ≤ E* + Δ(n−1)e^{−δ/T}; goal: (∑ E e)/Z − E* ≤ Δ(n−1)e^{−δ/T}
  linarith
open Finset Real

open Finset Real in
/-- **Safety of a lower-bound entropy proxy (R463)**:
if the entropy estimate Ĥ never exceeds the true h,
then the surrogate free energy E − Ĥ majorizes the
true E − h, and the surprise certificate s ≤ E − h is
preserved by construction. -/
theorem proxy_cert_preserved (E h hhat s : ℝ)
    (hlow : hhat ≤ h) (hcert : s ≤ E - h) :
    s ≤ E - hhat := by
  linarith

/-- **Loss of the certificate for an upper-bound
entropy proxy (R463)**: if the proxy strictly exceeds
the true entropy and the true free energy exactly
meets the certificate, the surrogate free energy
falls strictly below it — the AIF bound is not
guaranteed (arXiv 2607.13612, Prop 2(ii)). -/
theorem proxy_cert_lost (E h hhat s : ℝ)
    (hup : h < hhat) (hexact : E - h = s) :
    E - hhat < s := by
  linarith

/-- **Gibbs certificate bridge (R463)**: at the
Gibbs equilibrium the surprise certificate
s ≤ F = −T·ln Z (R462 identity) is preserved by any
lower-bound entropy proxy Ĥ ≤ T·S_γ. -/
theorem gibbs_cert_bridge {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (hhat s : ℝ)
    (hlow : hhat ≤ T * (-(∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)))))
    (hcert : s ≤ -T * Real.log (∑ v : V,
      Real.exp (-(E v)/T))) :
    s ≤ (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)) * E v) - hhat := by
  have hid := gibbs_free_energy_identity E T hT
  linarith

open Real in
/-- **Three-source gap decomposition (R464)**:
the surrogate-true free-energy gap decomposes
exactly into prior-miscalibration, estimator bias
and optimization slack (arXiv 2607.13612, Prop 1). -/
theorem gap_decomposition (F Fhat g1 g2 g3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3) :
    abs (Fhat - F) = abs (g1 + g2 + g3) := by
  rw [hgap]

/-- **Estimator bias is nonpositive for a lower-bound
entropy proxy (R464)**: Gap II = Ĥ − h ≤ 0 whenever
the proxy underestimates the entropy. -/
theorem gapII_nonpos (h hhat : ℝ) (hlow : hhat ≤ h) :
    hhat - h ≤ 0 := by
  linarith

/-- **Graceful degradation, linear slack (R464)**:
if the gap sources obey |g1| ≤ c1, |g2| ≤ c2,
|g3| ≤ c3 then the surrogate-true gap obeys the
triangle bound (arXiv 2607.13612, Cor 2(i)). -/
theorem gap_graceful (F Fhat g1 g2 g3 c1 c2 c3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3)
    (h1 : abs g1 ≤ c1) (h2 : abs g2 ≤ c2)
    (h3 : abs g3 ≤ c3) :
    abs (Fhat - F) ≤ c1 + c2 + c3 := by
  rw [hgap, add_assoc]
  calc abs (g1 + (g2 + g3))
      ≤ abs g1 + abs (g2 + g3) :=
        abs_add_le g1 (g2 + g3)
    _ ≤ abs g1 + (abs g2 + abs g3) := by
        have := abs_add_le g2 g3
        linarith
    _ ≤ c1 + c2 + c3 := by
        linarith [h1, h2, h3]

open Real in
/-- **Autoregressive error compounding (R465)**:
if the predictor is L-Lipschitz so each step maps
e_t ↦ e_{t+1} ≤ L·e_t, the H-step executed error
compounds geometrically (arXiv 2607.13612, Thm 2(ii),
L^{2H}-structure in the squared metric). -/
theorem compounding_bound (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, e (t+1) ≤ L * e t)
    (n : ℕ) : e n ≤ L^n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := he n
      calc e (n+1) ≤ L * e n := h1
        _ ≤ L * (L^n * e 0) := by
            exact mul_le_mul_of_nonneg_left ih hL
        _ = L^(n+1) * e 0 := by
            rw [pow_succ]; ring

/-- **Squared-metric compounding is L^(2H) (R465)**:
in the squared metric the same step recursion gives
e_H^2 ≤ (L^2)^H·e_0^2 — the O(L^(2H)) term of
arXiv 2607.13612, Thm 2(ii). -/
theorem compounding_sq (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, 0 ≤ e t)
    (hsq : ∀ t, e (t+1)^2 ≤ (L^2) * e t^2)
    (n : ℕ) : e n^2 ≤ (L^2)^n * e 0^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := hsq n
      have hL2 : (0:ℝ) ≤ L^2 := by nlinarith [hL]
      calc e (n+1)^2 ≤ L^2 * e n^2 := h1
        _ ≤ L^2 * ((L^2)^n * e 0^2) := by
            exact mul_le_mul_of_nonneg_left ih hL2
        _ = (L^2)^(n+1) * e 0^2 := by
            rw [pow_succ]; ring

open Finset Real in
/-- **Mutual information is nonnegative (R466)**:
I(X;Y) = KL(ρ ‖ μ₁×μ₂) ≥ 0 — the information a
joint distribution carries about the dependence
of its marginals never decreases below zero
(direct R447 application; equivalent to R459). -/
theorem mutual_info_nonneg {V W : Type*} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W]
    [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (0:ℝ) ≤ ∑ p : V × W, ρ p * Real.log
      (ρ p / ((∑ w : W, ρ (p.1, w))
        * (∑ v : V, ρ (v, p.2)))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  set μ₂ : W → ℝ := fun w => ∑ v : V, ρ (v, w) with hμ₂
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  have hμ₂pos : ∀ w, 0 < μ₂ w := by
    intro w
    have := Finset.sum_pos (fun v _ => hρ (v, w))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [hμ₂]; exact this
  set γ : V × W → ℝ := fun p => μ₁ p.1 * μ₂ p.2 with hγ
  have hγpos : ∀ p, 0 < γ p := fun p => by
    rw [hγ]; exact mul_pos (hμ₁pos p.1) (hμ₂pos p.2)
  have hμ₁s : ∑ v : V, μ₁ v = 1 := by
    rw [hμ₁, ← Fintype.sum_prod_type]; exact hρ1
  have hμ₂s : ∑ w : W, μ₂ w = 1 := by
    rw [hμ₂, Finset.sum_comm, ← Fintype.sum_prod_type]; exact hρ1
  have hγ1 : ∑ p : V × W, γ p = 1 := by
    show ∑ p : V × W, μ₁ p.1 * μ₂ p.2 = 1
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, μ₁ (v, w).1 * μ₂ (v, w).2 = μ₁ v := by
      intro v
      simp only []
      rw [← Finset.mul_sum, hμ₂s, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    exact hμ₁s
  -- the KL expression is definitionally the one in R447
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  exact hKL

/-- **EFE ceiling (R466)**: expected free energy
decomposes as G = P − I with pragmatic value P and
epistemic (information) part I ≥ 0; hence the EFE
never exceeds the pragmatic value — the
state-epistemic gap is exactly the mutual
information (arXiv 2607.13612, Prop 6 structure). -/
theorem efe_ceiling (G P I : ℝ)
    (hdecomp : G = P - I) (hI : 0 ≤ I) :
    G ≤ P := by
  linarith

open Real in
/-- **Amortised EFE policy guarantee (R467)**: if the
learned surrogate Ĝ uniformly approximates the true
expected free energy within slack c, the policy
minimising Ĝ executes within 2c of the optimum
(arXiv 2607.13612, Prop 7 structure). -/
theorem amortized_policy_bound {Pol : Type*}
    (Ghat G : Pol → ℝ) (pih pis : Pol) (c : ℝ)
    (happrox : ∀ pi, abs (Ghat pi - G pi) ≤ c)
    (hmin : ∀ pi, Ghat pih ≤ Ghat pi) :
    G pih ≤ G pis + 2 * c := by
  have hA : ∀ pi : Pol, Ghat pi - G pi ≤ c :=
    fun pi => (abs_le.mp (happrox pi)).2
  have hB : ∀ pi : Pol, G pi - Ghat pi ≤ c :=
    fun pi => by
      have h := abs_le.mp (happrox pi)
      linarith
  have h3 := hmin pis
  linarith [hA pih, hA pis, hB pih]

/-!
# Концентрация меры Гиббса (хаб R386-R496)

Модуль-хаб: содержимое разнесено по тематическим файлам
(GibbsCooling, GibbsInfoCore, EntropyConvexity, CertGaps,
PinskerTV, ChernoffCGF, MomentBounds); импорт этого файла
даёт все декларации прежнего единого модуля. Внешние
потребители (Thermostat, MWU) не изменились.
-/

end Hagi.Probability


end C236_gc

section C236_mwu
namespace Hagi.Probability


/-!
# MWU — мост к multiplicative weights (R433–)

Одношаговый потенциал-анализ экспоненциальных весов
(hedge-ядро без рядов, RAG-опора: arXiv 2608.09389,
EW-regret ≤ M√(2 ln A·T)). База: R432
(gibbs_energy_gap_crude). Здесь: логарифм
нормировочной константы после одного обновления
весов контролируется потерями:
ln Z' ≥ −2η·⟨ℓ⟩_w при η·ℓ ≤ 1/2.
Ключ: (1+2x)(1−x) ≥ 1 при x ≤ 1/2 ⟹
e^{−2x} ≤ 1−x (без calculus).
-/

open Finset Real

theorem mwu_potential_step {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≥ -2 * η * (∑ v, w v * ℓ v) := by
  set L : ℝ := ∑ v, w v * ℓ v with hL
  -- per-v: 1 - ηℓ v <= exp(-(η ℓ v))
  have hper : ∀ v : V, 1 - η * ℓ v ≤ Real.exp (-(η * ℓ v)) :=
    fun v => Real.one_sub_le_exp_neg (η * ℓ v)
  -- weighted: sum w (1 - ηℓ) <= Z'
  have hsum1 : ∑ v, w v * (1 - η * ℓ v)
      ≤ ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- sum w (1 - ηℓ) = 1 - η L
  have hterm : ∀ v : V, w v * (1 - η * ℓ v)
      = w v - w v * (η * ℓ v) := fun v => by ring
  have hsplit : ∑ v, w v * (1 - η * ℓ v)
      = ∑ v, w v - ∑ v, w v * (η * ℓ v) := by
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib]
  have hmul : ∑ v, w v * (η * ℓ v) = η * L := by
    rw [hL, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hw1] at hsplit
  rw [hsplit, hmul] at hsum1
  -- x := η L in [0, 1/2]
  have hLnn : (0:ℝ) ≤ L :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hw v)) (hℓ v))
  have hx : (0:ℝ) ≤ η * L := mul_nonneg (le_of_lt hη) hLnn
  have hxle : η * L ≤ 1/2 := by
    -- η L = Σ w (η ℓ) <= Σ w (1/2) = 1/2
    have hterm2 : ∀ v : V, w v * (η * ℓ v) ≤ w v * (1/2) :=
      fun v => mul_le_mul_of_nonneg_left (hsmall v) (le_of_lt (hw v))
    calc η * L = ∑ v, w v * (η * ℓ v) := hmul.symm
      _ ≤ ∑ v, w v * (1/2) := Finset.sum_le_sum (fun v _ => hterm2 v)
      _ = 1/2 := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) ((1:ℝ)/2)),
            ← Finset.mul_sum, hw1, mul_one]
  -- exp(-2x) <= 1 - x for x in [0, 1/2]
  have he2 : Real.exp (-(2*(η*L))) ≤ 1 - η*L := by
    have h1 := Real.add_one_le_exp (2*(η*L))
    have hmul2 : (1 + 2*(η*L)) * (1 - η*L) ≥ 1 := by
      have hxs : (η*L)^2 ≤ (η*L)/2 := by nlinarith [hxle, hx]
      nlinarith [hxs, hx]
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ (exp_pos (2*(η*L)))).mpr
      (by nlinarith [h1, hmul2,
        mul_nonneg (exp_pos (2*(η*L))).le (show (0:ℝ) ≤ 1 - η*L by linarith)])
  -- log chain
  have hlog := Real.log_le_log (exp_pos (-(2*(η*L)))) (le_trans he2 hsum1)
  rw [Real.log_exp] at hlog
  linarith

/-- **Нижняя грань потенциала (R434)**:
ln Z' ≤ −η·ℓ_min — вклад минимизатора
потерь доминирует:
e^{−ηℓ_v} ≤ e^{−ηℓ_min} почленно ⟹
Z' ≤ e^{−ηℓ_min}. Вместе с R433
(верхняя грань): −η·ℓ_min
≤ −ln Z' ≤ 2η·⟨ℓ⟩_w — потенциал
зажат с обеих сторон. -/
theorem mwu_potential_lower {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hη : 0 < η) :
    ∃ vmin : V, Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≤ -(η * ℓ vmin) := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  -- per-v: exp(-(η ℓ v)) <= exp(-(η ℓ vmin))
  have hper : ∀ v : V, Real.exp (-(η * ℓ v)) ≤ Real.exp (-(η * ℓ vmin)) := by
    intro v
    apply Real.exp_le_exp.mpr
    have h1 : ℓ vmin ≤ ℓ v := hvmin v
    have h2 : -(η * ℓ v) ≤ -(η * ℓ vmin) := by
      have : η * ℓ vmin ≤ η * ℓ v :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hη)
      linarith
    exact h2
  -- weighted sum bound
  have hsum : ∑ v, w v * Real.exp (-(η * ℓ v))
      ≤ ∑ v, w v * Real.exp (-(η * ℓ vmin)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- = exp(...) * sum w = exp(...)
  have hsplit : ∑ v, w v * Real.exp (-(η * ℓ vmin))
      = Real.exp (-(η * ℓ vmin)) * ∑ v, w v := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) (Real.exp (-(η * ℓ vmin)))),
      Finset.mul_sum]
  rw [hw1, mul_one] at hsplit
  rw [hsplit] at hsum
  -- log mono
  have hZpos : (0:ℝ) < ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (hw v) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hlog := Real.log_le_log hZpos hsum
  rwa [Real.log_exp] at hlog

/-- **Сертификат зажатия потенциала
(R435)**: η·ℓ_min ≤ −ln Z' ≤ 2η·⟨ℓ⟩_w —
одна теорема для потребителя
(композиция R434 + R433).
Следствие: ℓ_min ≤ 2⟨ℓ⟩_w —
одношаговая гарантия
без-регретности; многошаговый
телескоп построится на
ней индукцией. -/
theorem mwu_potential_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v, w v * ℓ v) := by
  obtain ⟨vmin, hlow⟩ := mwu_potential_lower w ℓ η hw hw1 hη
  have hhigh := mwu_potential_step w ℓ η hw hw1 hℓ hη hsmall
  refine ⟨vmin, ?_, ?_⟩
  · linarith
  · linarith

/-- **MWU с uniform-стартом (R436)**:
специализация R435 на веса
1/n — классический hedge с
равномерным начальным
распределением над
экспертами V. Кумулятивные
потери ℓ := L (сумма по шагам)
дают телескопический
потенциал: η·L_min ≤ −ln W ≤
2η·⟨L⟩_{unif}. -/
theorem mwu_uniform_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v) := by
  have hw : ∀ v : V, (0:ℝ) < 1/(Fintype.card V : ℝ) := by
    intro v
    apply div_pos (by norm_num)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hw1 : ∑ v : V, (1/(Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
    rw [nsmul_eq_mul, one_div, mul_inv_cancel₀ (ne_of_gt hn)]
  exact mwu_potential_squeeze (fun _ => 1/(Fintype.card V : ℝ)) ℓ η hw hw1 hℓ hη hsmall

/-- **Классический ln n-член (R437)**:
−ln W ≤ ln n + η·L_min для uniform-hedge
(W ≥ (1/n)·e^{−ηL_min} через
один член суммы).
Вместе с R436 (верхняя
2η-грань): полная regret-пара
для экспоненциальных
весов: ln n + ηL_min ≥ −ln W ≥ ηL_min —
запас на инициализацию ровно
ln n. -/
theorem mwu_potential_upper_uniform {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ vmin : V, -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v))))
      ≤ Real.log (Fintype.card V : ℝ) + η * ℓ vmin := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hZpos : (0:ℝ) < ∑ v : V, (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (by positivity) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hsingle : (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ vmin))
      ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ v)) :=
    single_le_sum (f := fun v => (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)))
      (fun v _ => mul_nonneg (by positivity) (exp_pos _).le)
      (Finset.mem_univ vmin)
  have hpos2 : (0:ℝ) < (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)) :=
    mul_pos (by positivity) (exp_pos _)
  have hlog := Real.log_le_log hpos2 hsingle
  have hsplit : Real.log ((1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)))
      = -(Real.log (Fintype.card V : ℝ) + η * ℓ vmin) := by
    have hne1 : (1/(Fintype.card V : ℝ)) ≠ 0 := by positivity
    have hne2 : Real.exp (-(η * ℓ vmin)) ≠ 0 := by positivity
    rw [Real.log_mul hne1 hne2, Real.log_exp,
      Real.log_div (one_ne_zero) (ne_of_gt hn), Real.log_one,
      zero_sub, neg_add_eq_sub]
    ring
  rw [hsplit] at hlog
  linarith

/-- **Телескоп MWU-весов (R438)**:
∏_{t<T} e^{−η·ℓ_t(v)} = e^{−η·∑_{t<T} ℓ_t(v)}
(индукция, exp_add). Замкнутая
форма ненормированных
экспоненциальных весов:
u_T(v) = e^{−ηL_v}. Соединяется с
R436/R437 (W = (1/n)∑ e^{−ηL_v}) — полная
многошаговая механика. -/
theorem mwu_prod_exp {V : Type*} (ℓs : ℕ → V → ℝ) (η : ℝ)
    (T : ℕ) (v : V) :
    ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))
      = Real.exp (-(η * ∑ t ∈ Finset.range T, ℓs t v)) := by
  induction T with
  | zero => simp
  | succ t ih =>
    rw [Finset.prod_range_succ_comm, Finset.sum_range_succ, ih,
      ← Real.exp_add]
    congr 1
    ring

/-- **Замкнутая форма разбиения (R439)**:
∑_v ∏_t e^{−ηℓ_t(v)} = ∑_v e^{−ηL_v}
(почленная композиция R438).
Ненормированная статистика
алгоритма — чисто
Гиббс-статистика
кумулятивных потерь:
мост MWU ↔ Гиббс замыкается
на уровне разбиения. -/
theorem mwu_partition_sum {V : Type*} [Fintype V] (ℓs : ℕ → V → ℝ) (η : ℝ)
    (T : ℕ) :
    ∑ v : V, ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))
      = ∑ v : V, Real.exp (-(η * ∑ t ∈ Finset.range T, ℓs t v)) :=
  Finset.sum_congr rfl (fun v _ => mwu_prod_exp ℓs η T v)


/-- **Гиббс = hedge при η = 1/T (R441)** —
мост вертикалей:
hedge-сертификат Гиббс-статистики:
(1/T)E_min ≤ −ln((1/n)∑e^{−E/T}) ≤
2(1/T)⟨E⟩_unif. Температура —
обратный learning rate: охлаждение
термостата = ускорение
обучения. Вся MWU-механика
(R432-R440) автоматически
переносится на термодинамику. -/
theorem gibbs_hedge_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hE : ∀ v, 0 ≤ E v)
    (hsmall : ∀ v, (1/T) * E v ≤ 1/2) :
    ∃ vmin : V, (1/T) * E vmin
      ≤ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(E v)/T)))
      ∧ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(E v)/T)))
        ≤ 2 * (1/T) * (∑ v : V, (1/(Fintype.card V : ℝ)) * E v) := by
  have hkey : ∀ v : V, Real.exp (-(E v)/T)
      = Real.exp (-((1/T) * E v)) := by
    intro v
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun v _ => hkey v), Finset.mul_sum]
  have hη : (0:ℝ) < 1/T := by positivity
  exact mwu_uniform_squeeze E (1/T) hE hη hsmall
/-- **Двойная верхняя грань (R443)**:
−ln W ≤ min(2η·⟨ℓ⟩_unif,
ln n + η·ℓ_min) — две
конкурирующие оценки
в одной теореме:
база для η-оптимизации
(уравнивание двух членов даёт
классический оптимальный
learning rate). -/
theorem mwu_double_upper {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V,
      -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
      ∧ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v))))
        ≤ Real.log (Fintype.card V : ℝ) + η * ℓ vmin := by
  obtain ⟨_, _, h2⟩ := mwu_uniform_squeeze ℓ η hℓ hη hsmall
  rw [← Finset.mul_sum] at h2
  obtain ⟨vmin, h3⟩ := mwu_potential_upper_uniform ℓ η hη
  rw [← Finset.mul_sum] at h3
  exact ⟨vmin, h2, h3⟩

/-- **η-сбалансированная граница (R444)**:
−ln W ≤ 2√(η·⟨ℓ⟩·ln n) при
η·⟨ℓ⟩ ≤ ln n (равновесие
двух оценок R443 через
среднее геометрическое:
f ≤ X, f ≤ Y, f ≥ 0 ⟹ f² ≤ XY;
Y ≤ 2 ln n при балансе).
Классическая структура
regret-границ MWU. -/
theorem mwu_sqrt_bound {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2)
    (hn : (0:ℝ) < Real.log (Fintype.card V : ℝ))
    (hbal : η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
      ≤ Real.log (Fintype.card V : ℝ)) :
    -(Real.log ((1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v))))
      ≤ 2 * Real.sqrt (η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
        * Real.log (Fintype.card V : ℝ)) := by
  obtain ⟨_, h2, _⟩ := mwu_double_upper ℓ η hℓ hη hsmall
  set Lbar : ℝ := ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v with hL
  -- explicit minimizer
  obtain ⟨v0, hv0⟩ : ∃ v0 : V, ∀ v : V, ℓ v0 ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image
      (Finset.univ : Finset V) ℓ Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  have hLnn : (0:ℝ) ≤ Lbar :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (by positivity) (hℓ v))
  -- direct bound: -log W <= log n + eta * Lbar
  have hminle : ℓ v0 ≤ Lbar := by
    have hsumle : (Fintype.card V : ℝ)
        * ((1/(Fintype.card V : ℝ)) * ℓ v0)
        ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v := by
      calc (Fintype.card V : ℝ)
          * ((1/(Fintype.card V : ℝ)) * ℓ v0)
          = ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v0 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v :=
            Finset.sum_le_sum (fun v _ =>
              mul_le_mul_of_nonneg_left (hv0 v) (by positivity))
    have hrewrite : (Fintype.card V : ℝ)
        * ((1/(Fintype.card V : ℝ)) * ℓ v0) = ℓ v0 := by
      field_simp
    rw [hrewrite] at hsumle
    rw [hL]
    exact hsumle
  set f : ℝ := -(Real.log ((1/(Fintype.card V : ℝ))
      * ∑ v : V, Real.exp (-(η * ℓ v)))) with hfdef
  have hη0 : (0:ℝ) ≤ η := le_of_lt hη
  have hf : (0:ℝ) ≤ f := by
    have hW : (1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v)) ≤ 1 := by
      have hle : ∑ v : V, Real.exp (-(η * ℓ v))
          ≤ (Fintype.card V : ℝ) := by
        calc ∑ v : V, Real.exp (-(η * ℓ v))
            ≤ ∑ v : V, (1:ℝ) :=
              Finset.sum_le_sum (fun v _ =>
                Real.exp_le_one_iff.mpr
                  (neg_nonpos.mpr (mul_nonneg hη0 (hℓ v))))
          _ = (Fintype.card V : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                mul_one]
      have hnn : (0:ℝ) < (Fintype.card V : ℝ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
      have hone : (1/(Fintype.card V : ℝ))
          * (Fintype.card V : ℝ) = 1 := by field_simp
      have hstep := mul_le_mul_of_nonneg_left hle
        (by positivity : (0:ℝ) ≤ 1/(Fintype.card V : ℝ))
      have := hstep.trans_eq hone
      exact this
    have hWpos : (0:ℝ) < (1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v)) :=
      mul_pos (by positivity)
        (Finset.sum_pos (fun v _ => exp_pos _) ⟨v0, Finset.mem_univ _⟩)
    have hlog := Real.log_le_log hWpos hW
    rw [Real.log_one] at hlog
    simp only [hfdef]
    linarith
  have hupper2 : f
      ≤ Real.log (Fintype.card V : ℝ) + η * Lbar := by
    have hstep : η * ℓ v0 ≤ η * Lbar :=
      mul_le_mul_of_nonneg_left hminle hη0
    have hsingle : (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ v0))
        ≤ (1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v)) := by
      rw [Finset.mul_sum]
      exact single_le_sum
        (f := fun v => (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v)))
        (fun v _ => mul_nonneg (by positivity) (exp_pos _).le)
        (Finset.mem_univ v0)
    have hpos2 : (0:ℝ) < (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v0)) :=
      mul_pos (by positivity) (exp_pos _)
    have hlog := Real.log_le_log hpos2 hsingle
    have hsplit : Real.log ((1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v0)))
        = -(Real.log (Fintype.card V : ℝ) + η * ℓ v0) := by
      have hne1 : (1/(Fintype.card V : ℝ)) ≠ 0 := by positivity
      have hne2 : Real.exp (-(η * ℓ v0)) ≠ 0 := by positivity
      have hnn : (0:ℝ) < (Fintype.card V : ℝ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
      rw [Real.log_mul hne1 hne2, Real.log_exp,
        Real.log_div (one_ne_zero) (ne_of_gt hnn), Real.log_one,
        zero_sub, neg_add_eq_sub]
      ring
    rw [hsplit] at hlog
    simp only [hfdef] at hlog ⊢
    linarith
  -- geometric combination: f^2 <= X * Y with X = 2 eta Lbar, Y = log n + eta Lbar
  have hXY : f * f ≤ (2 * η * Lbar) * (Real.log (Fintype.card V : ℝ)
      + η * Lbar) :=
    mul_le_mul h2 hupper2 hf
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη0) hLnn)
  -- Y <= 2 log n
  have hY : Real.log (Fintype.card V : ℝ) + η * Lbar
      ≤ 2 * Real.log (Fintype.card V : ℝ) := by linarith
  have hprod : (2 * η * Lbar) * (Real.log (Fintype.card V : ℝ) + η * Lbar)
      ≤ (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))) := by
    have hsq : (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        = 4 * (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
      have h1 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ η * Lbar
        * Real.log (Fintype.card V : ℝ))
      calc (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
          * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
          = 4 * (Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))
            * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))) := by
            ring
        _ = 4 * (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
            rw [← sq, h1]
    rw [hsq]
    nlinarith [hbal, hLnn, hn, le_of_lt hη, hY]
  -- f = sqrt(f^2) <= sqrt(prod) = 2 sqrt(...)
  have hfsq : Real.sqrt (f * f) = f := by
    rw [← sq f, Real.sqrt_sq hf]
  rw [← hfsq]
  calc Real.sqrt (f * f)
      ≤ Real.sqrt ((2 * η * Lbar) * (Real.log (Fintype.card V : ℝ)
        + η * Lbar)) := Real.sqrt_le_sqrt hXY
    _ ≤ Real.sqrt ((2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))) :=
        Real.sqrt_le_sqrt hprod
    _ = 2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
        have h2 := Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.sqrt
          (η * Lbar * Real.log (Fintype.card V : ℝ)))
        rw [← sq, h2]



open Classical in
/-- The selected inverse-weighted loss collapses to the fixed target loss by
finite-sum cancellation. This finite-sum identity uses no normalization,
nonnegativity or nonempty hypothesis. -/
theorem selectedLoss_sum_real {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  simp_rw [mul_ite, mul_zero]
  rw [Fintype.sum_ite_eq' b]
  exact mul_div_cancel₀ (ℓ b) hb

open Classical in
/-- Under a PMF, observing only a selected action's loss with inverse
propensity yields exactly its expectation for each fixed arm with positive
selection probability.  This is not a variance or learning-regret claim. -/
theorem pmfMean_selectedLoss {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  have hbReal : (p b).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
  exact selectedLoss_sum_real (fun a => (p a).toReal) ℓ b hbReal


open scoped Classical in
/-- If a target loss is zero, its selected inverse-weighted estimator is zero
even when that target has zero propensity. Otherwise nonzero propensity
suffices: zero-loss arms need not be observed. -/
theorem selectedLoss_sum_real_support {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  rcases hb with hb | hzero
  · exact selectedLoss_sum_real p ℓ b hb
  · simp_rw [mul_ite, mul_zero]
    rw [Fintype.sum_ite_eq' b]
    simp [hzero]

open scoped Classical in
/-- Finite-PMF unbiasedness only needs the propensity required to recover
that fixed target. A zero target can have zero selection probability. -/
theorem pmfMean_selectedLoss_support {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  exact selectedLoss_sum_real_support (fun a => (p a).toReal) ℓ b
    (hb.imp (fun hb => ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩)
      (fun hzero => hzero))

open scoped Classical in
/-- Exact finite variance of one selected inverse-propensity observation.
At zero target loss, both sides are zero even at zero propensity. This is
not a variance upper bound or a claim of reduced computational cost. -/
theorem pmfMean_selectedLoss_variance {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
      - (pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0)) ^ 2
      = (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
  have hmean :
      pmfMean p (fun a =>
        if a = b then ℓ a / (p a).toReal else 0) = ℓ b :=
    pmfMean_selectedLoss_support p ℓ b hb
  rw [hmean]
  by_cases hpb : p b = 0
  · have hzeroLoss : ℓ b = 0 :=
      hb.elim (fun hne => (hne hpb).elim) (fun hzero => hzero)
    have hzero : ∀ a,
        (if a = b then ℓ a / (p a).toReal else 0) = 0 := by
      intro a
      split_ifs with ha
      · subst a
        simp [hzeroLoss]
      · rfl
    simp [pmfMean, hzero, hzeroLoss]
  · have hpbReal : (p b).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hpb, p.apply_ne_top b⟩
    have hmoment :
        pmfMean p (fun a =>
          (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
          = (ℓ b) ^ 2 / (p b).toReal := by
      calc
        pmfMean p (fun a =>
            (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
            = ∑ a, if a = b then
                (p a).toReal * (ℓ a / (p a).toReal) ^ 2 else 0 := by
          simp only [pmfMean]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp [div_pow]
        _ = (p b).toReal * (ℓ b / (p b).toReal) ^ 2 := by
          rw [Fintype.sum_ite_eq' b]
        _ = (ℓ b) ^ 2 / (p b).toReal := by
          rw [div_pow]
          field_simp [hpbReal]
    rw [hmoment]
    ring


open scoped Classical

/-- One selected observation's expected sum of coordinate-wise squared
errors for a fixed finite loss vector. PmfMean is linear, so this also
expresses its expected Euclidean squared error; no independence claim. -/
noncomputable def selectedLossMSE {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : ℝ :=
  ∑ b, pmfMean p (fun a =>
    ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)

/-- Loss-magnitude-proportional propensity. The positive normalizer
ensures a genuine PMF, including zero propensity for zero losses.
This normalized construction is for one fixed finite loss vector. -/
noncomputable def selectedLoss_optimalPropensity {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) : PMF V := by
  let q : V → ℝ := fun i => |ℓ i| / ∑ a, |ℓ a|
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (abs_nonneg (ℓ i)) hL.le
  have hq_sum : ∑ i, q i = 1 := by
    dsimp [q]
    calc
      (∑ i, |ℓ i| / ∑ a, |ℓ a|) = (∑ i, |ℓ i|) / ∑ a, |ℓ a| :=
        (Finset.sum_div _ _ _).symm
      _ = 1 := div_self hL.ne'
  refine PMF.ofFintype (fun i => ENNReal.ofReal (q i)) ?_
  calc
    ∑ i, ENNReal.ofReal (q i) = ENNReal.ofReal (∑ i, q i) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => hq_nonneg i)).symm
    _ = 1 := by rw [hq_sum, ENNReal.ofReal_one]

@[simp] theorem selectedLoss_optimalPropensity_apply {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) (b : V) :
    (selectedLoss_optimalPropensity ℓ hL b).toReal =
      |ℓ b| / ∑ i, |ℓ i| := by
  change (ENNReal.ofReal (|ℓ b| / ∑ i, |ℓ i|)).toReal =
    |ℓ b| / ∑ i, |ℓ i|
  exact ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (ℓ b)) hL.le)

/-- Exact objective under target-wise support. The formula identifies
sum-of-coordinate-error MSE with the trace of marginal variances;
there is no covariance-independence or scalar-total-variance claim. -/
theorem selectedLossMSE_eq_sum {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ)
    (h_support : ∀ b, p b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE p ℓ =
      (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
  unfold selectedLossMSE
  calc
    ∑ b, pmfMean p (fun a =>
        ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)
        = ∑ b, (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
      apply Finset.sum_congr rfl
      intro b _
      have hmean := pmfMean_selectedLoss_support p ℓ b (h_support b)
      have hvar := pmfMean_selectedLoss_variance p ℓ b (h_support b)
      rw [pmfMean_sq_sub, hmean]
      rw [hmean] at hvar
      linarith
    _ = (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Exact MSE attained by loss-magnitude-proportional propensity.
Zero losses may have zero mass without losing unbiasedness. -/
theorem selectedLoss_optimalPropensity_mse {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      (∑ i, |ℓ i|) ^ 2 - ∑ i, (ℓ i) ^ 2 := by
  have h_support : ∀ b,
      selectedLoss_optimalPropensity ℓ hL b ≠ 0 ∨ ℓ b = 0 := by
    intro b
    by_cases hzero : ℓ b = 0
    · exact Or.inr hzero
    · apply Or.inl
      have hne : (selectedLoss_optimalPropensity ℓ hL b).toReal ≠ 0 := by
        rw [selectedLoss_optimalPropensity_apply]
        exact div_ne_zero (abs_ne_zero.mpr hzero) hL.ne'
      exact (ENNReal.toReal_ne_zero.mp hne).1
  rw [selectedLossMSE_eq_sum _ _ h_support]
  have hsecond : ∑ b,
      (ℓ b) ^ 2 / (selectedLoss_optimalPropensity ℓ hL b).toReal =
        ∑ b, |ℓ b| * ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro b _
    rw [selectedLoss_optimalPropensity_apply]
    by_cases hzero : ℓ b = 0
    · simp [hzero]
    · rw [← sq_abs]
      field_simp [abs_ne_zero.mpr hzero, hL.ne']
  rw [hsecond, ← Finset.sum_mul]
  ring

/-- Global finite MSE optimum among supported PMFs, proved using
zero-safe finite Cauchy-Schwarz, not stationary-point optimality. -/
theorem selectedLoss_optimalPropensity_mse_le {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ ≤
      selectedLossMSE q ℓ := by
  have hCS : (∑ i, |ℓ i|) ^ 2 ≤
      (∑ i, (ℓ i) ^ 2 / (q i).toReal) * ∑ i, (q i).toReal := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact div_nonneg (sq_nonneg (ℓ i)) ENNReal.toReal_nonneg
    · intro i _
      exact ENNReal.toReal_nonneg
    · intro i _
      by_cases hzero : (q i).toReal = 0
      · have hqi : q i = 0 := by
          have hz : q i = 0 ∨ q i = ⊤ :=
            (ENNReal.toReal_eq_zero_iff (q i)).mp hzero
          exact hz.resolve_right (q.apply_ne_top i)
        have hloss : ℓ i = 0 := (h_support i).elim
          (fun hne => (hne hqi).elim) (fun hzero => hzero)
        simp [hzero, hloss]
      · rw [sq_abs]
        exact le_of_eq (div_mul_cancel₀ ((ℓ i) ^ 2) hzero).symm
  have hbound : (∑ i, |ℓ i|) ^ 2 ≤
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    simpa only [pmf_weight_sum q, mul_one] using hCS
  rw [selectedLoss_optimalPropensity_mse,
    selectedLossMSE_eq_sum q ℓ h_support]
  linarith


open scoped Classical

/-- Selected-coordinate MSE is a sum of expectations of nonnegative
squared errors, so it is nonnegative for every finite PMF and loss. -/
theorem selectedLossMSE_nonneg {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : 0 ≤ selectedLossMSE p ℓ := by
  unfold selectedLossMSE
  apply Finset.sum_nonneg
  intro b _
  apply pmfMean_nonneg
  intro a _
  exact sq_nonneg _

/-- Zero total absolute loss means every fixed loss is zero. There is
no normalization need and no nonzero selected coordinate can occur. -/
theorem selectedLossMSE_eq_zero_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ = 0 := by
  have hzero (b : V) : ℓ b = 0 := by
    have habs : |ℓ b| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => abs_nonneg (ℓ i))).mp hL b (Finset.mem_univ b)
    exact abs_eq_zero.mp habs
  simp [selectedLossMSE, hzero]

/-- In the zero-normalizer branch, every supplied PMF has zero MSE and
is therefore a minimizer. This explicitly avoids a uniqueness claim. -/
theorem selectedLossMSE_le_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p q : PMF V) (ℓ : V → ℝ)
    (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ ≤ selectedLossMSE q ℓ := by
  rw [selectedLossMSE_eq_zero_of_abs_sum_eq_zero p ℓ hL]
  exact selectedLossMSE_nonneg q ℓ

/-- With positive total loss magnitude, the loss-proportional PMF is the
unique supported least-MSE proposal. The proof recovers the constant
nonzero-weight ratios using strict Jensen, with zero-weight losses
handled by the given support rather than an all-positive-assumption. -/
theorem selectedLoss_optimalPropensity_eq_of_mse_eq {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0)
    (h_mse : selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      selectedLossMSE q ℓ) :
    selectedLoss_optimalPropensity ℓ hL = q := by
  have hmul (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) = |ℓ i| := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) =
            |ℓ i| / (q i).toReal * (q i).toReal := mul_comm _ _
        _ = |ℓ i| := div_mul_cancel₀ _ hzero
  have hsq (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
        (ℓ i) ^ 2 / (q i).toReal := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
            ((q i).toReal * (|ℓ i| / (q i).toReal)) *
              (|ℓ i| / (q i).toReal) := by ring
        _ = |ℓ i| * (|ℓ i| / (q i).toReal) := by rw [hmul i]
        _ = |ℓ i| ^ 2 / (q i).toReal := by ring
        _ = (ℓ i) ^ 2 / (q i).toReal := by rw [sq_abs]
  have hmean : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) =
      ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact hmul i
  have hsecond : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsq i
  rw [selectedLoss_optimalPropensity_mse] at h_mse
  have hobjective := selectedLossMSE_eq_sum q ℓ h_support
  have hvalue : (∑ i, (ℓ i) ^ 2 / (q i).toReal) =
      (∑ i, |ℓ i|) ^ 2 := by
    linarith
  have hjensen := (strictConvexOn_pow (n := 2) (by norm_num)).map_sum_eq_iff'
    (t := Finset.univ)
    (w := fun i => (q i).toReal)
    (p := fun i => |ℓ i| / (q i).toReal)
    (fun i _ => ENNReal.toReal_nonneg)
    (pmf_weight_sum q)
    (fun i _ => div_nonneg (abs_nonneg (ℓ i)) ENNReal.toReal_nonneg)
  have hw_eq : ∀ b, (q b).toReal ≠ 0 →
      |ℓ b| / (q b).toReal = ∑ i, |ℓ i| := by
    have hsquare : (∑ i, (q i).toReal * (|ℓ i| / (q i).toReal)) ^ 2 =
        ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 := by
      rw [hmean, hsecond, hvalue]
    have hj := hjensen.mp hsquare
    intro b hb
    have hb_eq := hj b (Finset.mem_univ b) hb
    simpa only [smul_eq_mul, hmean] using hb_eq
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff'
    ((selectedLoss_optimalPropensity ℓ hL).apply_ne_top b)
    (q.apply_ne_top b)).mp
  rw [selectedLoss_optimalPropensity_apply]
  by_cases hzero : (q b).toReal = 0
  · have hqi : q b = 0 :=
      ((ENNReal.toReal_eq_zero_iff (q b)).mp hzero).resolve_right
        (q.apply_ne_top b)
    have hloss : ℓ b = 0 := (h_support b).elim
      (fun hne => (hne hqi).elim) (fun hz => hz)
    simp [hzero, hloss]
  · apply (div_eq_iff hL.ne').mpr
    calc
      |ℓ b| = (∑ i, |ℓ i|) * (q b).toReal :=
        (div_eq_iff hzero).mp (hw_eq b hzero)
      _ = (q b).toReal * ∑ i, |ℓ i| := mul_comm _ _

/-- Positive-normalizer optimal propensity supports every nonzero target
coordinate. Zero propensity forces that coordinate's target loss to vanish. -/
theorem selectedLoss_optimalPropensity_support {V : Type*} [Fintype V]
    (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    ∀ b, selectedLoss_optimalPropensity ell hL b ≠ 0 ∨ ell b = 0 := by
  intro b
  by_cases hzero : ell b = 0
  · exact Or.inr hzero
  · apply Or.inl
    have hne : (selectedLoss_optimalPropensity ell hL b).toReal ≠ 0 := by
      rw [selectedLoss_optimalPropensity_apply]
      exact div_ne_zero (abs_ne_zero.mpr hzero) hL.ne'
    exact (ENNReal.toReal_ne_zero.mp hne).1

/-- For positive total absolute loss, the optimal supported estimator has
zero MSE exactly when its propensity is a singleton mass. This finite trace
criterion does not assert determinism of real-valued losses generally, nor
that the losses used to construct the normalized distribution are cheap. -/
theorem selectedLoss_optimalPropensity_mse_eq_zero_iff_apply_eq_one
    {V : Type*} [Fintype V] (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell = 0 ↔
      ∃ b, selectedLoss_optimalPropensity ell hL b = 1 := by
  classical
  let q : V → ℝ := fun b =>
    (selectedLoss_optimalPropensity ell hL b).toReal
  have hq_apply (b : V) : q b = |ell b| / ∑ i, |ell i| := by
    dsimp [q]
    rw [selectedLoss_optimalPropensity_apply]
  have hq_nonneg (b : V) : 0 ≤ q b := ENNReal.toReal_nonneg
  have hq_sum : ∑ b, q b = 1 := by
    simpa only [q] using pmf_weight_sum (selectedLoss_optimalPropensity ell hL)
  have hq_le_one (b : V) : q b ≤ 1 := by
    calc
      q b ≤ ∑ a, q a := Finset.single_le_sum
        (fun a _ => hq_nonneg a) (Finset.mem_univ b)
      _ = 1 := hq_sum
  have hmul (b : V) : q b * (∑ i, |ell i|) = |ell b| := by
    rw [hq_apply]
    exact div_mul_cancel₀ _ hL.ne'
  have hsq (b : V) :
      (ell b) ^ 2 = (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
    calc
      (ell b) ^ 2 = |ell b| ^ 2 := (sq_abs _).symm
      _ = (q b * (∑ i, |ell i|)) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) (hmul b).symm
      _ = (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by ring
  have hsquares : ∑ b, (ell b) ^ 2 =
      ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
    exact Finset.sum_congr rfl (fun b _ => hsq b)
  have hmse : selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell =
      (∑ i, |ell i|) ^ 2 * ∑ b, q b * (1 - q b) := by
    rw [selectedLoss_optimalPropensity_mse]
    calc
      (∑ i, |ell i|) ^ 2 - ∑ b, (ell b) ^ 2 =
          (∑ i, |ell i|) ^ 2 * (∑ b, q b) -
            ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
        rw [hq_sum, mul_one, hsquares]
      _ = (∑ b, (∑ i, |ell i|) ^ 2 * q b) -
            ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
        rw [Finset.mul_sum]
      _ = ∑ b, ((∑ i, |ell i|) ^ 2 * q b -
            (∑ i, |ell i|) ^ 2 * (q b) ^ 2) :=
        (Finset.sum_sub_distrib _ _).symm
      _ = ∑ b, (∑ i, |ell i|) ^ 2 * (q b * (1 - q b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (∑ i, |ell i|) ^ 2 * ∑ b, q b * (1 - q b) :=
        (Finset.mul_sum _ _ _).symm
  constructor
  · intro hmse_zero
    have hsum_zero : ∑ b, q b * (1 - q b) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 hL.ne')
      rwa [← hmse]
    have hterm_zero (b : V) : q b * (1 - q b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        mul_nonneg (hq_nonneg a) (sub_nonneg.mpr (hq_le_one a)))).mp
          hsum_zero b (Finset.mem_univ b)
    have hq_zero_or_one (b : V) : q b = 0 ∨ q b = 1 := by
      rcases mul_eq_zero.mp (hterm_zero b) with hb | hb
      · exact Or.inl hb
      · exact Or.inr (sub_eq_zero.mp hb).symm
    obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := q) (by rw [hq_sum]; exact one_ne_zero)
    have hbq : q b = 1 := (hq_zero_or_one b).resolve_left hb
    refine ⟨b, ?_⟩
    apply (ENNReal.toReal_eq_toReal_iff'
      ((selectedLoss_optimalPropensity ell hL).apply_ne_top b)
      ENNReal.one_ne_top).mp
    change q b = (1 : ENNReal).toReal
    rw [hbq, ENNReal.toReal_one]
  · rintro ⟨b, hb⟩
    have hbq : q b = 1 := by
      change (selectedLoss_optimalPropensity ell hL b).toReal = 1
      rw [hb, ENNReal.toReal_one]
    have hothers : ∀ a, a ≠ b → q a = 0 := by
      intro a ha
      have hadd := Finset.add_sum_erase Finset.univ q (Finset.mem_univ b)
      rw [hbq, hq_sum] at hadd
      have hzero : ∑ x ∈ Finset.univ.erase b, q x = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hq_nonneg x)).mp hzero a
          (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
    rw [hmse]
    have hzero : ∀ a, q a * (1 - q a) = 0 := by
      intro a
      by_cases ha : a = b
      · subst a
        rw [hbq]
        ring
      · rw [hothers a ha]
        ring
    rw [Finset.sum_eq_zero (fun a _ => hzero a), mul_zero]


/-- For positive total absolute loss, the optimal supported estimator
has zero MSE exactly when there is one genuinely nonzero loss
coordinate (all other coordinates are zero). -/
theorem selectedLoss_optimalPropensity_mse_eq_zero_iff_single_nonzero
    {V : Type*} [Fintype V] (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell = 0 ↔
      ∃ b, ell b ≠ 0 ∧ ∀ a, a ≠ b → ell a = 0 := by
  classical
  rw [selectedLoss_optimalPropensity_mse_eq_zero_iff_apply_eq_one]
  constructor
  · rintro ⟨b, hb⟩
    have hbne : ell b ≠ 0 := by
      intro hzero
      have hbreal : (selectedLoss_optimalPropensity ell hL b).toReal = 1 :=
        (ENNReal.toReal_eq_one_iff _).mpr hb
      rw [selectedLoss_optimalPropensity_apply, hzero, abs_zero, zero_div] at hbreal
      exact zero_ne_one hbreal
    refine ⟨b, hbne, ?_⟩
    intro a ha
    have hnot : a ∉ (selectedLoss_optimalPropensity ell hL).support := by
      rw [((selectedLoss_optimalPropensity ell hL).apply_eq_one_iff b).mp hb]
      simp [ha]
    have ha0 : selectedLoss_optimalPropensity ell hL a = 0 :=
      ((selectedLoss_optimalPropensity ell hL).apply_eq_zero_iff a).mpr hnot
    have hareal : (selectedLoss_optimalPropensity ell hL a).toReal = 0 := by
      rw [ha0, ENNReal.toReal_zero]
    rw [selectedLoss_optimalPropensity_apply] at hareal
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp hareal).resolve_right (ne_of_gt hL))
  · rintro ⟨b, hb, hothers⟩
    refine ⟨b, ?_⟩
    apply (ENNReal.toReal_eq_one_iff _).mp
    have hsum : ∑ i, |ell i| = |ell b| := by
      apply Fintype.sum_eq_single b
      intro a ha
      rw [hothers a ha, abs_zero]
    rw [selectedLoss_optimalPropensity_apply, hsum]
    exact div_self (abs_ne_zero.mpr hb)


/-- For positive total absolute loss, the optimal supported estimator
strictly beats a normalized uniform reference exactly when not all loss
magnitudes are equal. -/
theorem selectedLoss_optimalPropensity_mse_lt_uniform_iff
    {V : Type*} [Fintype V] (ell : V → ℝ)
    (hL : 0 < ∑ i, |ell i|) (q : PMF V)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card V : ℝ)) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell <
      selectedLossMSE q ell ↔ ¬ (∀ i j, |ell i| = |ell j|) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun i => |ell i|) hL.ne'
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hq (b : V) : q b ≠ 0 := by
    apply (ENNReal.toReal_ne_zero.mp ?_).1
    rw [h_unit]
    exact one_div_ne_zero hcard.ne'
  have h_support : ∀ b, q b ≠ 0 ∨ ell b = 0 :=
    fun b => Or.inl (hq b)
  have hle := selectedLoss_optimalPropensity_mse_le ell hL q h_support
  constructor
  · intro hlt hconst
    have hL_const : (∑ i, |ell i|) =
        (Fintype.card V : ℝ) * |ell o| := by
      calc
        (∑ i, |ell i|) = ∑ _i : V, |ell o| :=
          Finset.sum_congr rfl (fun i _ => hconst i o)
        _ = (Fintype.card V : ℝ) * |ell o| := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpq : selectedLoss_optimalPropensity ell hL = q := by
      apply PMF.ext
      intro b
      apply (ENNReal.toReal_eq_toReal_iff'
        ((selectedLoss_optimalPropensity ell hL).apply_ne_top b)
        (q.apply_ne_top b)).mp
      rw [selectedLoss_optimalPropensity_apply, h_unit,
        hconst b o, hL_const]
      field_simp [hcard.ne', ho]
    exact (ne_of_lt hlt) (congrArg (fun p => selectedLossMSE p ell) hpq)
  · intro hnot
    apply lt_of_le_of_ne hle
    intro heq
    apply hnot
    have hpq := selectedLoss_optimalPropensity_eq_of_mse_eq
      ell hL q h_support heq
    have hnorm (i : V) : |ell i| / (∑ j, |ell j|) =
        1 / (Fintype.card V : ℝ) := by
      rw [← selectedLoss_optimalPropensity_apply ell hL i, hpq, h_unit]
    intro i j
    apply mul_right_cancel₀ hL.ne'
    exact (div_eq_div_iff hL.ne' hL.ne').mp
      ((hnorm i).trans (hnorm j).symm)


/-- Expected squared Euclidean error of one inverse-propensity selected
vector for the fixed full-sum target.  This is a sum-target objective,
not an arithmetic-mean or covariance-matrix claim. -/
noncomputable def selectedGradientMSE {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I) : ℝ :=
  pmfMean p (fun b => ‖(p b).toReal⁻¹ • g b - ∑ a, g a‖ ^ 2)

/-- Coordinate expansion of the selected-vector squared-error trace. -/
private theorem selectedGradientMSE_trace {B I : Type*}
    [Fintype B] [Fintype I] (p : PMF B) (m : B → EuclideanSpace ℝ I)
    (v : EuclideanSpace ℝ I) :
    pmfMean p (fun b => ‖(p b).toReal⁻¹ • m b - v‖ ^ 2) =
      ∑ i, pmfMean p (fun b =>
        ((p b).toReal⁻¹ * m b i - v i) ^ 2) := by
  unfold pmfMean
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ b, (p b).toReal *
        ∑ i, (((p b).toReal⁻¹ • m b - v) i) ^ 2) =
        ∑ b, ∑ i, (p b).toReal *
          ((p b).toReal⁻¹ * m b i - v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul]
    _ = ∑ i, ∑ b, (p b).toReal *
          ((p b).toReal⁻¹ * m b i - v i) ^ 2 := Finset.sum_comm

/-- Exact selected-gradient MSE under target-wise support.  Zero gradients
may have zero propensity; without support there is no such closed form. -/
theorem selectedGradientMSE_eq_sum {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I)
    (h_support : ∀ b, p b ≠ 0 ∨ g b = 0) :
    selectedGradientMSE p g =
      (∑ b, ‖g b‖ ^ 2 / (p b).toReal) - ‖∑ a, g a‖ ^ 2 := by
  have hmean (i : I) :
      pmfMean p (fun b => (p b).toReal⁻¹ * g b i) = (∑ a, g a) i := by
    unfold pmfMean
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : p b = 0
    · have hzero : g b = 0 := (h_support b).elim (fun hne => (hne hb).elim) (fun hzero => hzero)
      simp [hb, hzero]
    · have hbReal : (p b).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
      field_simp
  have hmoment (i : I) :
      pmfMean p (fun b => ((p b).toReal⁻¹ * g b i) ^ 2) =
        ∑ b, (g b i) ^ 2 / (p b).toReal := by
    unfold pmfMean
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : p b = 0
    · have hzero : g b = 0 := (h_support b).elim (fun hne => (hne hb).elim) (fun hzero => hzero)
      simp [hb, hzero]
    · have hbReal : (p b).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
      field_simp
  have hcomponent (i : I) :
      pmfMean p (fun b => ((p b).toReal⁻¹ * g b i - (∑ a, g a) i) ^ 2) =
        (∑ b, (g b i) ^ 2 / (p b).toReal) - ((∑ a, g a) i) ^ 2 := by
    rw [pmfMean_sq_sub, hmean, hmoment]
    ring
  unfold selectedGradientMSE
  rw [selectedGradientMSE_trace p g (∑ a, g a)]
  simp_rw [hcomponent]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  · calc
      (∑ b, ∑ i, (g b i) ^ 2 / (p b).toReal) =
          ∑ b, (∑ i, (g b i) ^ 2) / (p b).toReal := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_div]
      _ = ∑ b, ‖g b‖ ^ 2 / (p b).toReal := by
        apply Finset.sum_congr rfl
        intro b _
        rw [EuclideanSpace.real_norm_sq_eq]
  · rw [EuclideanSpace.real_norm_sq_eq]

/-- Exact MSE attained by norm-proportional selected-gradient sampling. -/
private theorem selectedGradientMSE_optimalPropensity_value {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g =
      (∑ b, ‖g b‖) ^ 2 - ‖∑ a, g a‖ ^ 2 := by
  have h_support : ∀ b,
      selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL) b ≠ 0 ∨ g b = 0 := by
    simpa only [abs_norm, norm_eq_zero] using
      selectedLoss_optimalPropensity_support (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)
  rw [selectedGradientMSE_eq_sum _ _ h_support]
  have hsecond : ∑ b, ‖g b‖ ^ 2 /
      (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL) b).toReal =
        ∑ b, ‖g b‖ * ∑ a, ‖g a‖ := by
    apply Finset.sum_congr rfl
    intro b _
    rw [selectedLoss_optimalPropensity_apply]
    simp only [abs_norm]
    by_cases hzero : g b = 0
    · simp [hzero]
    · field_simp [norm_eq_zero, hL.ne', hzero]
  rw [hsecond, ← Finset.sum_mul]
  ring

/-- The norm-proportional proposal minimizes selected-gradient MSE among
all target-wise supported finite PMFs. -/
theorem selectedGradientMSE_optimalPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_support : ∀ b, q b ≠ 0 ∨ g b = 0) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g ≤
      selectedGradientMSE q g := by
  have scalar_support : ∀ b, q b ≠ 0 ∨ ‖g b‖ = 0 := by
    simpa only [norm_eq_zero] using h_support
  rw [selectedGradientMSE_optimalPropensity_value g hL,
    selectedGradientMSE_eq_sum q g h_support]
  have scalar_le := selectedLoss_optimalPropensity_mse_le
    (fun b => ‖g b‖) (by simpa only [abs_norm] using hL) q scalar_support
  simp only [selectedLoss_optimalPropensity_mse,
    selectedLossMSE_eq_sum q (fun b => ‖g b‖) scalar_support,
    abs_norm] at scalar_le
  linarith

/-- Norm-proportional selection strictly improves on normalized uniform
selection exactly when some batch gradients have different Euclidean norms. -/
theorem selectedGradientMSE_optimalPropensity_lt_uniform_iff {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card B : ℝ)) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g <
      selectedGradientMSE q g ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun b => ‖g b‖) hL.ne'
  have hcard : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have support_q : ∀ b, q b ≠ 0 ∨ g b = 0 := by
    intro b
    apply Or.inl
    apply (ENNReal.toReal_ne_zero.mp ?_).1
    rw [h_unit]
    exact one_div_ne_zero hcard.ne'
  have scalar_support : ∀ b, q b ≠ 0 ∨ ‖g b‖ = 0 := by
    simpa only [norm_eq_zero] using support_q
  calc
    selectedGradientMSE
          (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g <
        selectedGradientMSE q g ↔
        selectedLossMSE
          (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL))
          (fun b => ‖g b‖) < selectedLossMSE q (fun b => ‖g b‖) := by
      rw [selectedGradientMSE_optimalPropensity_value g hL,
        selectedGradientMSE_eq_sum q g support_q,
        selectedLoss_optimalPropensity_mse,
        selectedLossMSE_eq_sum q (fun b => ‖g b‖) scalar_support]
      simp only [abs_norm]
      constructor <;> intro h <;> linarith
    _ ↔ ¬ (∀ i j, |‖g i‖| = |‖g j‖|) :=
      selectedLoss_optimalPropensity_mse_lt_uniform_iff
        (fun b => ‖g b‖) (by simpa only [abs_norm] using hL) q h_unit
    _ ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by simp only [abs_norm]


/-- Expected squared Euclidean error of the arithmetic-mean estimator
obtained from one inverse-propensity selected batch gradient. -/
noncomputable def selectedMeanGradientMSE {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I) : ℝ :=
  (Fintype.card B : ℝ)⁻¹ ^ 2 * selectedGradientMSE p g

/-- On a nonempty finite batch, the scaled sum-gradient MSE is exactly the
expected squared error for the estimator `(n*q)⁻¹ • g` and target `n⁻¹ • G`.
No support hypothesis is needed: this is algebra, including zero masses. -/
theorem selectedMeanGradientMSE_eq_sum {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I)
    (h_card : 0 < Fintype.card B) :
    selectedMeanGradientMSE p g =
      pmfMean p (fun b =>
        ‖((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
          (Fintype.card B : ℝ)⁻¹ • ∑ a, g a‖ ^ 2) := by
  have h_card_real : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr h_card
  have h_scale (b : B) :
      ‖((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
          (Fintype.card B : ℝ)⁻¹ • ∑ a, g a‖ ^ 2 =
        (Fintype.card B : ℝ)⁻¹ ^ 2 *
          ‖(p b).toReal⁻¹ • g b - ∑ a, g a‖ ^ 2 := by
    have hvector :
        ((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
            (Fintype.card B : ℝ)⁻¹ • ∑ a, g a =
          (Fintype.card B : ℝ)⁻¹ •
            ((p b).toReal⁻¹ • g b - ∑ a, g a) := by
      simp only [smul_sub, smul_smul]
      rw [mul_inv_rev, mul_comm ((p b).toReal⁻¹) ((Fintype.card B : ℝ)⁻¹)]
    rw [hvector, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos h_card_real]
    ring
  unfold selectedMeanGradientMSE selectedGradientMSE
  rw [← pmfMean_const_mul]
  apply congrArg (pmfMean p)
  funext b
  exact (h_scale b).symm

/-- Norm-proportional selection minimizes arithmetic-mean selected-gradient
MSE among every target-wise supported finite competitor. -/
theorem selectedMeanGradientMSE_optimalPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_support : ∀ b, q b ≠ 0 ∨ g b = 0) :
    selectedMeanGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
          (by simpa only [abs_norm] using hL)) g ≤
      selectedMeanGradientMSE q g := by
  unfold selectedMeanGradientMSE
  exact mul_le_mul_of_nonneg_left
    (selectedGradientMSE_optimalPropensity_le g hL q h_support) (sq_nonneg _)

/-- Arithmetic-mean selection strictly improves on normalized uniform
selection exactly when batch-gradient Euclidean norms are not all equal. -/
theorem selectedMeanGradientMSE_optimalPropensity_lt_uniform_iff
    {B I : Type*} [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card B : ℝ)) :
    selectedMeanGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
          (by simpa only [abs_norm] using hL)) g <
      selectedMeanGradientMSE q g ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by
  obtain ⟨o, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun b => ‖g b‖) hL.ne'
  have h_card : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hfactor : (0 : ℝ) < (Fintype.card B : ℝ)⁻¹ ^ 2 :=
    sq_pos_of_pos (inv_pos_of_pos h_card)
  unfold selectedMeanGradientMSE
  constructor
  · intro h
    apply (selectedGradientMSE_optimalPropensity_lt_uniform_iff
      g hL q h_unit).mp
    exact lt_of_mul_lt_mul_left h hfactor.le
  · intro h
    exact mul_lt_mul_of_pos_left
      ((selectedGradientMSE_optimalPropensity_lt_uniform_iff
        g hL q h_unit).mpr h) hfactor


open scoped Classical BigOperators
open Real

/-- Any norm upper bound gives a nonnegative allocation weight, and a zero
weight forces the corresponding gradient to vanish.  For the induced
propensity, the selected-gradient trace is at most the squared total norm
bound minus the squared norm of the target gradient sum. -/
theorem selectedGradientMSE_upperBoundPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (a : B → ℝ) (hA : 0 < ∑ b, |a b|) (h_bound : ∀ b, ‖g b‖ ≤ a b) :
    selectedGradientMSE (selectedLoss_optimalPropensity a hA) g ≤
      (∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2 := by
  let p := selectedLoss_optimalPropensity a hA
  have h_zero (b : B) (hb : |a b| = 0) : g b = 0 := by
    have ha : a b = 0 := abs_eq_zero.mp hb
    have hn : ‖g b‖ ≤ 0 := by simpa only [ha] using h_bound b
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have h_support : ∀ b, p b ≠ 0 ∨ g b = 0 := by
    intro b
    by_cases hb : |a b| = 0
    · exact Or.inr (h_zero b hb)
    · apply Or.inl
      apply (ENNReal.toReal_ne_zero.mp ?_).1
      dsimp only [p]
      rw [selectedLoss_optimalPropensity_apply]
      exact div_ne_zero hb hA.ne'
  have hpoint (b : B) :
      ‖g b‖ ^ 2 / (p b).toReal ≤ (∑ c, |a c|) * |a b| := by
    dsimp only [p]
    rw [selectedLoss_optimalPropensity_apply]
    by_cases hb : |a b| = 0
    · simp [h_zero b hb, hb]
    · have hbpos : 0 < |a b| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hb)
      have hsquare : ‖g b‖ ^ 2 ≤ |a b| ^ 2 := by
        nlinarith [norm_nonneg (g b), h_bound b, sq_abs (a b)]
      rw [div_div_eq_mul_div]
      apply (div_le_iff₀ hbpos).2
      calc
        ‖g b‖ ^ 2 * (∑ c, |a c|) ≤ |a b| ^ 2 * (∑ c, |a c|) :=
          mul_le_mul_of_nonneg_right hsquare hA.le
        _ = (∑ c, |a c|) * |a b| * |a b| := by ring
  have hsum : (∑ b, ‖g b‖ ^ 2 / (p b).toReal) ≤ (∑ b, |a b|) ^ 2 := by
    calc
      (∑ b, ‖g b‖ ^ 2 / (p b).toReal) ≤ ∑ b, (∑ c, |a c|) * |a b| :=
        Finset.sum_le_sum (fun b _ => hpoint b)
      _ = (∑ c, |a c|) * ∑ b, |a b| := (Finset.mul_sum _ _ _).symm
      _ = (∑ b, |a b|) ^ 2 := by ring
  change selectedGradientMSE p g ≤ (∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2
  rw [selectedGradientMSE_eq_sum p g h_support]
  exact sub_le_sub_right hsum _

/-- The arithmetic-mean error inherits the propensity upper bound with the
exact squared inverse-cardinality scaling, without a separate
cardinal-positivity premise. -/
theorem selectedMeanGradientMSE_upperBoundPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (a : B → ℝ) (hA : 0 < ∑ b, |a b|) (h_bound : ∀ b, ‖g b‖ ≤ a b) :
    selectedMeanGradientMSE (selectedLoss_optimalPropensity a hA) g ≤
      (Fintype.card B : ℝ)⁻¹ ^ 2 *
        ((∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2) := by
  unfold selectedMeanGradientMSE
  exact mul_le_mul_of_nonneg_left
    (selectedGradientMSE_upperBoundPropensity_le g a hA h_bound) (sq_nonneg _)

end Hagi.Probability

export Hagi.Probability (mwu_potential_step)
end C236_mwu

section C236_md
/-
MirrorDescent: единый вариационный принцип.

Зеркальный шаг с энтропийным зеркалом: для любой ссылки ρ₀
(равномерной в Гиббсе, предыдущих весов в MWU/Hedge,
априорных убеждений в Active Inference) решение задачи
argmin_{ρ ∈ Δ} { ⟨ρ, ℓ⟩ + T·KL(ρ‖ρ₀) } — мера
γ_v ∝ ρ₀_v·e^{−ℓ_v/T}: Гиббс, MWU-обновление и EFE-минимум
AIF — одно и то же аналитическое решение с минимальным
значением −T·log Z. Тождество:
T·KL(ρ‖γ) = ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) + T·log Z.
-/

namespace Hagi.Optimization

open Finset

/-- Зеркальный шаг (энтропийное зеркало): γ_v = ρ₀_v·e^{−ℓ_v/T}/Z,
где Z = Σ_v ρ₀_v·e^{−ℓ_v/T} — нормировка. -/
noncomputable def mirrorStep {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) : V → ℝ :=
  fun v => ρ₀ v * Real.exp (-(ℓ v)/T)
    / ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)

/-- Позитивность зеркального шага при T > 0 и ρ₀ > 0. -/
theorem mirrorStep_pos {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (v : V) :
    0 < mirrorStep ρ₀ ℓ T v := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  unfold mirrorStep
  exact div_pos (mul_pos (hρ₀ v) (Real.exp_pos _)) hZpos

/-- Зеркальный шаг — распределение: сумма равна 1. -/
theorem mirrorStep_sum_one {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    ∑ v, mirrorStep ρ₀ ℓ T v = 1 := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  unfold mirrorStep
  rw [← Finset.sum_div]
  exact div_self hZpos.ne'

/-- ТОЖДЕСТВО ЗЕРКАЛЬНОГО ШАГА: для γ = mirrorStep ρ₀ ℓ T и
любого ρ ∈ Δ:
T·KL(ρ‖γ) = ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) + T·log Z.
Следствие неотрицательности KL: ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀)
минимизируется мерой γ, минимум равен −T·log Z —
Гиббс (ρ₀ равномерна), MWU-обновление (ρ₀ = предыдущие
веса) и EFE-минимум AIF — одно и то же решение. -/
theorem mirror_descent_identity {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    T * (∑ v, ρ v * Real.log (ρ v
        / mirrorStep ρ₀ ℓ T v))
      = (∑ v, ρ v * ℓ v)
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v))
        + T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)) := by
  have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) :=
    Finset.sum_pos (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  set Z := ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T) with hZ
  have hlogγ : ∀ v : V, Real.log (mirrorStep ρ₀ ℓ T v)
      = Real.log (ρ₀ v) - ℓ v / T - Real.log Z := by
    intro v
    unfold mirrorStep
    have hnum : (0:ℝ) < ρ₀ v * Real.exp (-(ℓ v)/T) :=
      mul_pos (hρ₀ v) (Real.exp_pos _)
    rw [Real.log_div hnum.ne' hZpos.ne',
      Real.log_mul (hρ₀ v).ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  -- почленное разложение под суммой
  have hsplit : ∀ v : V,
      T * (ρ v * Real.log (ρ v / mirrorStep ρ₀ ℓ T v))
      = ρ v * ℓ v
        + T * (ρ v * Real.log (ρ v / ρ₀ v))
        + ρ v * (T * Real.log Z) := by
    intro v
    rw [Real.log_div (hρ v).ne' (hγpos v).ne',
      Real.log_div (hρ v).ne' (hρ₀ v).ne', hlogγ v]
    field_simp
    ring
  -- суммирование трёх частей
  rw [Finset.mul_sum,
    Finset.sum_congr rfl (fun v _ => hsplit v),
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum,
    ← Finset.sum_mul, hρ1, one_mul]

/-- НИЖНЯЯ ГРАНЬ ЗЕРКАЛЬНОГО ШАГА (унификация): для любого
ρ ∈ Δ выполнено ⟨ρ,ℓ⟩ + T·KL(ρ‖ρ₀) ≥ −T·log Z, где
Z = Σ ρ₀·e^{−ℓ/T}; равенство достигается на γ = mirrorStep:
единая нижняя грань для меры Гиббса, MWU/Hedge-потенциала
и свободной энергии EFE из Active Inference. -/
theorem mirror_descent_floor {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T))
      ≤ (∑ v, ρ v * ℓ v)
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
  classical
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hKL : (0:ℝ) ≤ ∑ v, ρ v * Real.log (ρ v
      / mirrorStep ρ₀ ℓ T v) :=
    finite_kl_nonneg ρ (mirrorStep ρ₀ ℓ T) hρ hρ1 hγpos hγ1
  have hid := mirror_descent_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  have hTnn : (0:ℝ) ≤ T := le_of_lt hT
  have hTKL : (0:ℝ) ≤ T * (∑ v, ρ v * Real.log (ρ v
      / mirrorStep ρ₀ ℓ T v)) := mul_nonneg hTnn hKL
  linarith

/-- ДОСТИЖИМОСТЬ ПОЛА ЗЕРКАЛЬНОГО ШАГА: на мере
γ = mirrorStep ρ₀ ℓ T свободная энергия ⟨γ,ℓ⟩+T·KL(γ‖ρ₀)
равна в точности −T·log Z — нижняя грань mirror_descent_floor
достигается: γ — минимизатор вариационной задачи,
полнота унификации Гиббса/MWU/EFE. -/
theorem mirror_descent_attainment {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ)
    (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      + T * (∑ v, mirrorStep ρ₀ ℓ T v
          * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v))
      = -T * Real.log (∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have h := mirror_descent_identity ρ₀ ℓ T hT hρ₀
    (mirrorStep ρ₀ ℓ T) hγpos hγ1
  have hsum : (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v
        / mirrorStep ρ₀ ℓ T v)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    rw [div_self (hγpos v).ne', Real.log_one, mul_zero]
  rw [hsum, mul_zero] at h
  linarith

/-- МОСТ MWU ↔ ЗЕРКАЛЬНЫЙ СПУСК: hedge-обновление
γ = mirrorStep w ℓ (1/η) — в точности зеркальный шаг с
T = 1/η; комбинируя достижимость пола (F(γ) = −T log Z) с
оценкой нормировки MWU (log Z ≥ −2η⟨ℓ⟩_w при ηℓ ≤ 1/2),
получаем F(γ) ≤ 2⟨ℓ⟩_w: свободная энергия обновлённой смеси
не более удвоенных текущих средних потерь — мост между
экспоненциальными весами и вариационным принципом. -/
theorem hedge_free_energy_step {V : Type*} [Fintype V]
    [Nonempty V] (w ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    (∑ v, mirrorStep w ℓ (1/η) v * ℓ v)
      + (1/η) * (∑ v, mirrorStep w ℓ (1/η) v
          * Real.log (mirrorStep w ℓ (1/η) v / w v))
      ≤ 2 * (∑ v, w v * ℓ v) := by
  -- достижимость: F(γ) = −(1/η)·log Z
  have hT : (0:ℝ) < 1/η := one_div_pos.mpr hη
  have hatt := mirror_descent_attainment w ℓ (1/η) hT hw
  -- MWU-оценка нормировки: log Z ≥ −2η⟨ℓ⟩_w
  have hmwu := mwu_potential_step w ℓ η hw hw1 hℓ hη hsmall
  -- Z в обоих утверждениях совпадает: exp(−ηℓ) = exp(−ℓ/(1/η))
  have hZeq : (∑ v, w v * Real.exp (-(ℓ v)/(1/η)))
      = ∑ v, w v * Real.exp (-(η * ℓ v)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    field_simp
  rw [hZeq] at hatt
  -- F(γ) = (1/η)·(−log Z) ≤ (1/η)·2η⟨ℓ⟩_w = 2⟨ℓ⟩_w
  have hneg : -Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≤ 2 * η * (∑ v, w v * ℓ v) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hneg hT.le
  have hconv : (1/η) * (2 * η * (∑ v, w v * ℓ v))
      = 2 * (∑ v, w v * ℓ v) := by
    field_simp
  have hsplit : (∑ v, mirrorStep w ℓ (1/η) v * ℓ v)
      + (1/η) * (∑ v, mirrorStep w ℓ (1/η) v
          * Real.log (mirrorStep w ℓ (1/η) v / w v))
      = (1/η) * (-Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))) := by
    rw [hatt]
    ring
  rw [hsplit]
  calc (1/η) * (-Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
      ≤ (1/η) * (2 * η * (∑ v, w v * ℓ v)) := hmul
    _ = 2 * (∑ v, w v * ℓ v) := hconv

/-- EFE-ШАГ ACTIVE INFERENCE = ЗЕРКАЛЬНЫЙ ШАГ: при разложении
потерь ℓ = surprise − information gain минимизатор ожидаемой
свободной энергии — мера mirrorStep ρ₀ (s−g) T, и её свободная
энергия равна в точности −T·log Z(s−g): третий член
унификации Гиббс == MWU == EFE. -/
theorem aif_efe_attainment {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ s g : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    (∑ v, mirrorStep ρ₀ (fun v => s v - g v) T v * (s v - g v))
      + T * (∑ v, mirrorStep ρ₀ (fun v => s v - g v) T v
          * Real.log (mirrorStep ρ₀ (fun v => s v - g v) T v
            / ρ₀ v))
      = -T * Real.log (∑ w, ρ₀ w
          * Real.exp (-(s w - g w)/T)) :=
  mirror_descent_attainment ρ₀ (fun v => s v - g v) T hT hρ₀

/-- EFE-ДОМИНИРОВАНИЕ: EFE-шаг не хуже любого убеждения ρ ∈ Δ:
−T·log Z(s−g) ≤ ⟨ρ, s−g⟩ + T·KL(ρ‖ρ₀) — ожидаемая свободная
энергия mirrorStep-убеждения доминируется снизу единой
вариационной гранью (специализация mirror_descent_floor). -/
theorem aif_efe_floor {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ s g : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ w, ρ₀ w * Real.exp (-(s w - g w)/T))
      ≤ (∑ v, ρ v * (s v - g v))
        + T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) :=
  mirror_descent_floor ρ₀ (fun v => s v - g v) T hT hρ₀
    ρ hρ hρ1

/-- ГИББС = ЗЕРКАЛЬНЫЙ ШАГ С РАВНОМЕРНОЙ ССЫЛКОЙ:
вариационная грань Гиббса (R421, gibbs_variational)
выводится из mirror_descent_floor при ρ₀ = 1/n:
-T·log(Σ e^{-ℓ/T}) ≤ ⟨ρ,ℓ⟩ + T·Σ ρ log ρ —
слагаемые T·log n сокращаются: мера Гиббса, MWU и EFE —
три проекции одного зеркального шага. -/
theorem gibbs_from_mirror {V : Type*} [Fintype V] [Nonempty V]
    (ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    -T * Real.log (∑ v, Real.exp (-(ℓ v)/T))
      ≤ (∑ v, ρ v * ℓ v) + T * (∑ v, ρ v * Real.log (ρ v)) := by
  classical
  exact Hagi.Probability.gibbs_variational ℓ T hT ρ hρ hρ1


/-- ОДНОШАГОВОЕ ТОЖДЕСТВО ПРОГРЕССА зеркального спуска:
для любого ρ ∈ Δ и шага γ = mirrorStep ρ₀ ℓ T:
⟨ρ,ℓ⟩ − F(γ) = T·(KL(ρ‖γ) − KL(ρ‖ρ₀)), где F(γ) — свободная
энергия γ (достигаемый пол): превышение любых потерь над
полом равно приросту расстояния Брегмана до цели ρ — база
телескопирования регрета MWU/Hedge. -/
theorem mirror_progress_identity {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    (∑ v, ρ v * ℓ v)
      - ((∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
          + T * (∑ v, mirrorStep ρ₀ ℓ T v
              * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)))
      = T * ((∑ v, ρ v * Real.log (ρ v
              / mirrorStep ρ₀ ℓ T v))
          - (∑ v, ρ v * Real.log (ρ v / ρ₀ v))) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hid := mirror_descent_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  rw [hatt]
  linarith

/-- Итерированные зеркальные веса: w₀ = ρ₀,
w_{k+1} = mirrorStep w_k (ℓ_k) T — траектория hedge/MWU
при постоянной температуре T. -/
noncomputable def mirrorIterate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) : ℕ → V → ℝ
  | 0 => ρ₀
  | k+1 => mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T

/-- Позитивность траектории сохраняется. -/
theorem mirrorIterate_pos {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (k : ℕ) :
    ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v := by
  induction k with
  | zero => exact hρ₀
  | succ n ih =>
      intro v
      unfold mirrorIterate
      exact mirrorStep_pos _ _ T hT ih v

/-- Траектория остаётся распределением. -/
theorem mirrorIterate_sum_one {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (k : ℕ) :
    ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 := by
  induction k with
  | zero => exact hρ₀1
  | succ n ih =>
      unfold mirrorIterate
      exact mirrorStep_sum_one _ _ T hT
        (mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n)

/-- ОДНОШАГОВОЕ НЕРАВЕНСТВО РЕГРЕТА: обновлённые веса γ
проигрывают цели ρ* не более убыли T·KL:
⟨γ,ℓ⟩ − ⟨ρ*,ℓ⟩ ≤ T·(KL(ρ*‖ρ₀) − KL(ρ*‖γ)) — следствие
тождества прогресса и неотрицательности KL(γ‖ρ₀). -/
theorem mirror_step_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) - (∑ v, ρ v * ℓ v)
      ≤ T * ((∑ v, ρ v * Real.log (ρ v / ρ₀ v))
        - (∑ v, ρ v * Real.log (ρ v
            / mirrorStep ρ₀ ℓ T v))) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  have hklγ : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    have h := finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀
      hγpos hγ1 hρ₀ hρ₀1
    exact mul_nonneg (le_of_lt hT) h
  -- hprog: ⟨ρ,ℓ⟩ − (⟨γ,ℓ⟩ + T·KL(γ‖ρ₀)) = T(KL(ρ‖γ) − KL(ρ‖ρ₀))
  have hprog := mirror_progress_identity ρ₀ ℓ T hT hρ₀ ρ hρ hρ1
  linarith

/-- ТЕЛЕСКОПИРОВАННЫЙ РЕГРЕТ HEDGE/MWU: суммарное превышение
потерь обновляемых весов w_{k+1} = mirrorStep w_k ℓ_k T над
любой фиксированной целью ρ* ≤ T·KL(ρ*‖w₀) — KL-убыль
телескопирует, регрет ограничен начальным расстоянием
Брегмана: полная формализация regret-границы зеркального
спуска (база MWU/Hedge-анализа). -/
theorem mirror_regret {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ρ : V → ℝ) (hρ : ∀ v, 0 < ρ v) (hρ1 : ∑ v, ρ v = 1)
    (n : ℕ) :
    ∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
  -- индукция по n с одношаговым неравенством
  have key : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
        ((∑ v, mirrorIterate ρ₀ ℓs T (k+1) v * ℓs k v)
          - (∑ v, ρ v * ℓs k v)))
      + T * (∑ v, ρ v * Real.log (ρ v
          / mirrorIterate ρ₀ ℓs T n v))
      ≤ T * (∑ v, ρ v * Real.log (ρ v / ρ₀ v)) := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have h0 : ∀ v, mirrorIterate ρ₀ ℓs T 0 v = ρ₀ v :=
          fun v => rfl
        simp only [h0, zero_add]
        exact le_of_eq rfl
    | succ m ih =>
        rw [Finset.sum_range_succ]
        -- одношаговое неравенство на шаге m
        have hposm : ∀ v, 0 < mirrorIterate ρ₀ ℓs T m v :=
          mirrorIterate_pos ρ₀ ℓs T hT hρ₀ m
        have h1m : ∑ v, mirrorIterate ρ₀ ℓs T m v = 1 :=
          mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 m
        have hstep := mirror_step_regret
          (mirrorIterate ρ₀ ℓs T m) (ℓs m) T hT hposm h1m
          ρ hρ hρ1
        -- w_{m+1} = mirrorStep w_m ℓ_m T по определению
        have hdef : mirrorIterate ρ₀ ℓs T (m+1)
            = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
          simp only [mirrorIterate]
        rw [hdef]
        linarith
  have h := key n
  -- финальный KL ≥ 0 → регрет ≤ границы
  have hposn : ∀ v, 0 < mirrorIterate ρ₀ ℓs T n v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ n
  have h1n : ∑ v, mirrorIterate ρ₀ ℓs T n v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ₀1 n
  have hkl : (0:ℝ) ≤ T * (∑ v, ρ v * Real.log (ρ v
      / mirrorIterate ρ₀ ℓs T n v)) :=
    mul_nonneg (le_of_lt hT)
      (finite_kl_nonneg ρ (mirrorIterate ρ₀ ℓs T n)
        hρ hρ1 hposn h1n)
  linarith


/-- ПОЛУГРУППОВОЙ ЗАКОН ЗЕРКАЛЬНОГО ШАГА: два
последовательных зеркальных шага (ℓ₁, затем ℓ₂, одна
температура T) равны одному шагу с суммарными потерями
ℓ₁+ℓ₂ — экспоненциальные веса перемножаются, нормировки
согласованы (Z₂·Z₁ = Z₁₂): траектория hedge за n шагов
есть один шаг с кумулятивными потерями. -/
theorem mirror_step_semigroup {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T
      = mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hZ₂ : (0:ℝ) < ∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hγpos w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have he : ∀ w : V, Real.exp (-(ℓ₁ w)/T)
      * Real.exp (-(ℓ₂ w)/T)
      = Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    rw [← Real.exp_add]
    congr 1
    ring
  -- почленно: γ₁(w)·e^{−ℓ₂/T}·Z₁ = ρ₀(w)·e^{−(ℓ₁+ℓ₂)/T}
  have hterm : ∀ w : V, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T)
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    unfold mirrorStep
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZ₁.ne',
      show ρ₀ w * Real.exp (-(ℓ₁ w)/T)
          * Real.exp (-(ℓ₂ w)/T)
        = ρ₀ w * (Real.exp (-(ℓ₁ w)/T)
            * Real.exp (-(ℓ₂ w)/T)) from by ring, he w]
  -- суммарно: Z₂·Z₁ = Z₁₂
  have hsum : (∑ w, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T))
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun w _ => hterm w)
  -- поэлементное совпадение
  funext v
  have htermv : mirrorStep ρ₀ ℓ₁ T v
      * Real.exp (-(ℓ₂ v)/T)
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T)) :=
    eq_div_of_mul_eq hZ₁.ne' (hterm v)
  have hL : mirrorStep (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T v
      = (mirrorStep ρ₀ ℓ₁ T v * Real.exp (-(ℓ₂ v)/T))
        / (∑ w, mirrorStep ρ₀ ℓ₁ T w
            * Real.exp (-(ℓ₂ w)/T)) := rfl
  have hR : mirrorStep ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T v
      = ρ₀ v * Real.exp (-(ℓ₁ v + ℓ₂ v)/T)
        / (∑ w, ρ₀ w
            * Real.exp (-(ℓ₁ w + ℓ₂ w)/T)) := by
    dsimp only [mirrorStep]
  rw [hL, hR, htermv, ← hsum]
  field_simp

/-- НУЛЕВЫЕ ПОТЕРИ: зеркальный шаг при ℓ = 0 возвращает
ссылку (Z = Σρ₀·e⁰ = 1): тождественное обновление. -/
theorem mirrorStep_zero_loss {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    mirrorStep ρ₀ (fun _ => 0) T = ρ₀ := by
  have hexp : ∀ w : V, Real.exp (-(0:ℝ)/T) = 1 := by
    intro w
    have hz : (-(0:ℝ)/T) = 0 := by
      rw [neg_zero, zero_div]
    rw [hz, Real.exp_zero]
  have hZ : (∑ w, ρ₀ w * Real.exp (-(0:ℝ)/T)) = 1 := by
    rw [Finset.sum_congr rfl (fun w _ => by rw [hexp w, mul_one])]
    exact hρ₀1
  funext v
  have hnum : ρ₀ v * Real.exp (-(0:ℝ)/T) = ρ₀ v := by
    rw [hexp v, mul_one]
  unfold mirrorStep
  rw [hZ, div_one, hnum]

/-- N-КРАТНЫЙ ПОЛУГРУППОВОЙ ЗАКОН: траектория hedge за n
шагов есть ОДИН зеркальный шаг с кумулятивными потерями
Σ_{k<n} ℓ_k: экспоненциальные веса накапливают потери
аддитивно, нормировки глобальны. -/
theorem mirrorIterate_cumulative {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ)
    (hT : 0 < T) (hρ₀ : ∀ v, 0 < ρ₀ v)
    (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    mirrorIterate ρ₀ ℓs T n
      = mirrorStep ρ₀
          (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ ℓs T 0 = ρ₀ := rfl
      rw [h0]
      exact (mirrorStep_zero_loss ρ₀ T hT hρ₀ hρ₀1).symm
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ ℓs T (m+1)
          = mirrorStep (mirrorIterate ρ₀ ℓs T m) (ℓs m) T := by
        simp only [mirrorIterate]
      rw [hdef, ih, mirror_step_semigroup ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀]
      congr 1
      funext v
      simp only [Finset.sum_range_succ]

/-- МОНОТОННОСТЬ ЭНЕРГИИ HEDGE: зеркальный шаг по потерям ℓ
никогда не поднимает ожидаемые потери по ним:
⟨mirrorStep ρ₀ ℓ T, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩. Цепочка:
⟨γ,ℓ⟩ ≤ F(γ) (KL(γ‖ρ₀) ≥ 0), F(γ) = −T·log Z
(attainment), −T·log Z ≤ ⟨ρ₀,ℓ⟩ (Йенсен выпуклости exp:
e^{−⟨ρ₀,ℓ⟩/T} ≤ Z). -/
theorem mirror_energy_decrease {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v) ≤ (∑ v, ρ₀ v * ℓ v) := by
  have hγpos : ∀ v, 0 < mirrorStep ρ₀ ℓ T v :=
    mirrorStep_pos ρ₀ ℓ T hT hρ₀
  have hγ1 : ∑ v, mirrorStep ρ₀ ℓ T v = 1 :=
    mirrorStep_sum_one ρ₀ ℓ T hT hρ₀
  -- KL(γ‖ρ₀) ≥ 0
  have hkl : (0:ℝ) ≤ ∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v) :=
    finite_kl_nonneg (mirrorStep ρ₀ ℓ T) ρ₀ hγpos hγ1 hρ₀ hρ₀1
  -- attainment: F(γ) = −T·log Z
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- Йенсен: e^{−⟨ρ₀,ℓ⟩/T} ≤ Z
  have hZpos : (0:ℝ) < ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) :=
    Finset.sum_pos
      (fun v _ => mul_pos (hρ₀ v) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hjensen : Real.exp ((∑ v, ρ₀ v * (-(ℓ v)/T)))
      ≤ ∑ v, ρ₀ v * Real.exp (-(ℓ v)/T) := by
    have hconv := convexOn_exp.map_sum_le
      (p := fun v => -(ℓ v)/T)
      (fun v _ => le_of_lt (hρ₀ v)) hρ₀1
      (fun v _ => Set.mem_univ v)
    simp only [smul_eq_mul] at hconv
    exact hconv
  -- log-монотонность: −⟨ρ₀,ℓ⟩/T ≤ log Z
  have hlogj : (∑ v, ρ₀ v * (-(ℓ v)/T))
      ≤ Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hjensen
    rw [Real.log_exp] at h1
    exact h1
  -- линейная сборка
  have hsplit : (∑ v, ρ₀ v * (-(ℓ v)/T))
      = -(∑ v, ρ₀ v * ℓ v)/T := by
    have hterm : ∀ v : V, ρ₀ v * (-(ℓ v)/T)
        = -(ρ₀ v * ℓ v)/T := by
      intro v
      ring
    rw [Finset.sum_congr rfl (fun v _ => hterm v),
      ← Finset.sum_neg_distrib, ← Finset.sum_div]
  rw [hsplit] at hlogj
  -- финал: ⟨γ,ℓ⟩ ≤ F(γ) = −T log Z ≤ ⟨ρ₀,ℓ⟩
  have hTKL : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀ ℓ T v
      * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) :=
    mul_nonneg (le_of_lt hT) hkl
  have h1 : (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      ≤ (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)) := by
    linarith
  have h2 : ((∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
        + T * (∑ v, mirrorStep ρ₀ ℓ T v
            * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v)))
      = -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T)) :=
    hatt
  rw [h2] at h1
  -- −T·logZ ≤ ⟨ρ₀,ℓ⟩ из hlogj (умножение на T > 0)
  have h3 : -T * Real.log (∑ v, ρ₀ v * Real.exp (-(ℓ v)/T))
      ≤ ∑ v, ρ₀ v * ℓ v := by
    have h4 := (mul_le_mul_of_nonneg_left hlogj (le_of_lt hT))
    -- T·(−⟨ρ₀,ℓ⟩/T) ≤ T·logZ ; T·(−X/T) = −X
    have h5 : T * (-(∑ v, ρ₀ v * ℓ v)/T)
        = -(∑ v, ρ₀ v * ℓ v) := by
      field_simp
    rw [h5] at h4
    linarith
  linarith [hkl, hT]

/-- МОНОТОННОСТЬ ЭНЕРГИИ ВДОЛЬ ТРАЕКТОРИИ: при фиксированных
потерях ℓ повторные зеркальные шаги монотонно не поднимают
ожидаемую энергию: ⟨w_n, ℓ⟩ ≤ ⟨ρ₀, ℓ⟩ для всех n —
итерированный hedge сходится по энергии (индукция из
mirror_energy_decrease). -/
theorem mirrorIterate_energy_monotone {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ (∑ v, ρ₀ v * ℓ v) := by
  induction n with
  | zero =>
      have h0 : mirrorIterate ρ₀ (fun _ => ℓ) T 0 = ρ₀ := rfl
      rw [h0]
  | succ m ih =>
      have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (m+1)
          = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T :=
        by simp only [mirrorIterate]
      rw [hdef]
      have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T m v :=
        mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ m
      have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T m v = 1 :=
        mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 m
      have hstep := mirror_energy_decrease
        (mirrorIterate ρ₀ (fun _ => ℓ) T m) ℓ T hT hpos h1
      linarith

/-- СХОДИМОСТЬ ЭНЕРГИИ ИТЕРАЦИЙ: при фиксированных потерях ℓ
с нижней границей C последовательность энергий
e_n = ⟨w_n, ℓ⟩ убывает шаг за шагом и ограничена снизу,
поэтому входит в ε-коридор над своим инфимумом L:
∀n≥N: L ≤ e_n ≤ L + ε — итерированный hedge сходится по
энергии (полнота ℝ + монотонность). -/
theorem mirrorIterate_energy_converges {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (C : ℝ) (hC : ∀ v, C ≤ ℓ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (sInf (Set.range (fun k =>
          ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v)))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (sInf (Set.range (fun k =>
            ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v))) + ε := by
  set e : ℕ → ℝ := fun k =>
    ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T k v * ℓ v with he
  -- соседняя монотонность: e_{n+1} ≤ e_n
  have hstep : ∀ n : ℕ, e (n+1) ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hdef : mirrorIterate ρ₀ (fun _ => ℓ) T (n+1)
        = mirrorStep (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T :=
      by simp only [mirrorIterate]
    have hdec := mirror_energy_decrease
      (mirrorIterate ρ₀ (fun _ => ℓ) T n) ℓ T hT hpos h1
    rw [he]
    show (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T (n+1) v * ℓ v)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
    rw [hdef]
    exact hdec
  -- цепная монотонность: m ≤ n → e_n ≤ e_m
  have hchain : ∀ n m : ℕ, m ≤ n → e n ≤ e m := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have h0 : m = 0 := Nat.le_zero.mp hm
        subst h0
        exact le_refl _
    | succ k ih =>
        intro m hm
        rcases Nat.lt_or_ge m (k+1) with hlt | hge
        · have hk : m ≤ k := Nat.lt_succ_iff.mp hlt
          have a := hstep k
          have b := ih m hk
          linarith
        · have h0 : m = k+1 := Nat.le_antisymm hm hge
          subst h0
          exact le_refl _
  -- ограниченность снизу: C ≤ e_n
  have hbdd : ∀ n : ℕ, C ≤ e n := by
    intro n
    have hpos : ∀ v, 0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
      mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀ n
    have h1 : ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
      mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n
    have hle : ∀ v : V, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hC v) (le_of_lt (hpos v))
    have hsplit : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C)
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) :=
      Finset.sum_le_sum fun v _ => hle v
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * C) = C := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) C),
        ← Finset.mul_sum, h1, mul_one]
    rw [he]
    linarith
  -- инфимум L и его свойства
  set L := sInf (Set.range e) with hL
  have hrng : (Set.range e).Nonempty := ⟨e 0, Set.mem_range_self 0⟩
  have hbddBelow : BddBelow (Set.range e) :=
    ⟨C, fun y hy => by
      obtain ⟨n, hn⟩ := Set.mem_range.mp hy
      rw [← hn]
      exact hbdd n⟩
  have hleL : ∀ n : ℕ, L ≤ e n :=
    fun n => csInf_le hbddBelow (Set.mem_range_self n)
  -- ∃ N: e N ≤ L + ε (иначе L+ε — меньшая нижняя граница)
  have hex : ∃ N : ℕ, e N ≤ L + ε := by
    by_contra hcon
    push_neg at hcon
    have hle' : L + ε ≤ L :=
      le_csInf hrng (fun y hy => by
        obtain ⟨n, hn⟩ := Set.mem_range.mp hy
        rw [← hn]
        exact le_of_lt (hcon n))
    linarith
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ⟨hleL n, ?_⟩⟩
  have h1 := hchain n N hn
  linarith

/-- NERNST-ПРЕДЕЛ ИТЕРАЦИЙ HEDGE: при фиксированных потерях ℓ
повторные зеркальные шаги сходятся по энергии к минимуму
потерь: ∀ε>0 ∃N ∀n≥N: ℓmin ≤ ⟨w_n, ℓ⟩ ≤ ℓmin + ε.
Механизм: w_n = mirrorStep ρ₀ (n·ℓ) T (кумулятивность),
свободная энергия F_n ≤ n·ℓmin − T·log(min ρ₀)
(Z_n ≥ min ρ₀ · e^{−nℓmin/T}), и KL-слагаемое ≥ 0 —
итерированный hedge находит минимум (термодинамический
предел T/n → 0). -/
theorem mirrorIterate_energy_infimum {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        ≤ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ∧ (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
        ≤ (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty)) + ε := by
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  set m := Finset.min' (Finset.univ.image ℓ) hneℓ with hm
  set r := Finset.min' (Finset.univ.image ρ₀) hneρ with hr
  -- минимумы достижимы и ограничивают
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hrw : r = ρ₀ wt := hwt.2.symm
  have hrpos : (0:ℝ) < r := by rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun w _ => le_of_lt (hρ₀ w)) (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- кумулятивность: w_n = mirrorStep ρ₀ (n·ℓ) T
  have hsum : ∀ (n : ℕ) (v : V),
      (∑ k ∈ Finset.range n, ℓ v) = (n : ℝ) * ℓ v := by
    intro n v
    simp
  have hwn : ∀ n : ℕ, mirrorIterate ρ₀ (fun _ => ℓ) T n
      = mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T := by
    intro n
    rw [mirrorIterate_cumulative ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1 n]
    congr 1
    funext v
    rw [hsum n v]
  -- нижняя граница энергии: e_n ≥ m
  have hposn : ∀ (n : ℕ) (v : V),
      0 < mirrorIterate ρ₀ (fun _ => ℓ) T n v :=
    mirrorIterate_pos ρ₀ (fun _ => ℓ) T hT hρ₀
  have h1n : ∀ n : ℕ,
      ∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v = 1 :=
    mirrorIterate_sum_one ρ₀ (fun _ => ℓ) T hT hρ₀ hρ₀1
  have hlower : ∀ n : ℕ, m ≤ (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v) := by
    intro n
    have hle : ∀ v : V,
        mirrorIterate ρ₀ (fun _ => ℓ) T n v * m
        ≤ mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v :=
      fun v => mul_le_mul_of_nonneg_left (hmle v)
        (le_of_lt (hposn n v))
    have hsplit := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hle v)
    have hsumC : (∑ v, mirrorIterate ρ₀ (fun _ => ℓ) T n v * m) = m := by
      rw [Finset.sum_congr rfl (fun v _ =>
        mul_comm (mirrorIterate ρ₀ (fun _ => ℓ) T n v) m),
        ← Finset.mul_sum, h1n n, mul_one]
    rw [hsumC] at hsplit
    exact hsplit
  -- верхняя граница: e_n ≤ m + (T/n)·(−log r)
  have hupper : ∀ n : ℕ, (0:ℕ) < n → (∑ v,
      mirrorIterate ρ₀ (fun _ => ℓ) T n v * ℓ v)
      ≤ m + T * (-(Real.log r)) / (n : ℝ) := by
    intro n hn
    -- KL(w_n ‖ ρ₀) ≥ 0 и attainment для n·ℓ
    have hγpos : ∀ v, 0 < mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v :=
      mirrorStep_pos ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hγ1 : ∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v = 1 :=
      mirrorStep_sum_one ρ₀ (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    have hkl : (0:ℝ) ≤ T * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v
        * Real.log (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v / ρ₀ v)) :=
      mul_nonneg (le_of_lt hT)
        (finite_kl_nonneg (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T)
          ρ₀ hγpos hγ1 hρ₀ hρ₀1)
    -- attainment: ⟨γ, nℓ⟩ + T·KL = −T·log Z_n
    have hatt := mirror_descent_attainment ρ₀
      (fun v => (n : ℝ) * ℓ v) T hT hρ₀
    -- нижняя оценка Z_n ≥ r · e^{−nm/T} через vt
    have hZge : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ ρ₀ vt * Real.exp (-((n : ℝ) * m)/T) := by
      have hterm := Finset.single_le_sum
        (f := fun w => ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        (fun w (_ : w ∈ Finset.univ) =>
          mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
        (Finset.mem_univ vt)
      rw [hvt.2] at hterm
      exact hterm
    have hrr : ρ₀ vt ≥ r := hrle vt
    have hZge2 : (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≥ r * Real.exp (-((n : ℝ) * m)/T) := by
      nlinarith [hZge, hrr, (Real.exp_pos
        (-((n : ℝ) * m)/T))]
    -- log-монотонность
    have hZpos : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T) := by
      have h0 : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
        mul_pos hrpos (Real.exp_pos _)
      linarith
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have hlog : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        ≤ Real.log (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)) :=
      Real.log_le_log hrpos' hZge2
    -- log(r·e^{−nm/T}) = log r − nm/T
    have hlogsplit : Real.log (r * Real.exp (-((n : ℝ) * m)/T))
        = Real.log r + (-((n : ℝ) * m)/T) := by
      rw [Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    rw [hlogsplit] at hlog
    -- собираем: e_n = ⟨γ, ℓ⟩ и ⟨γ, nℓ⟩ = n·e_n
    rw [hwn n]
    have hmul : (∑ v, mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
        * ((n : ℝ) * ℓ v))
        = (n : ℝ) * (∑ v, mirrorStep ρ₀
            (fun v => (n : ℝ) * ℓ v) T v * ℓ v) := by
      rw [Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) =>
        show mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
            * ((n : ℝ) * ℓ v)
          = (n : ℝ) * (mirrorStep ρ₀ (fun v => (n : ℝ) * ℓ v) T v
              * ℓ v) from by ring)]
      exact (Finset.mul_sum _ _ _).symm
    -- финальная арифметика
    have hnne : ((n : ℝ)) ≠ 0 := by
      have : (0:ℕ) < n := hn
      exact_mod_cast this.ne'
    rw [hmul] at hatt
    -- hlog, умноженный на T: T·log r − n·m ≤ T·logZ
    have hDTneg : T * (-(((n : ℝ) * m)/T))
        = -((n : ℝ) * m) := by
      have hDT : T * (((n : ℝ) * m)/T) = (n : ℝ) * m := by
        field_simp
      have hsplit : T * (-(((n : ℝ) * m)/T))
          = -(T * (((n : ℝ) * m)/T)) := by ring
      rw [hsplit, hDT]
    have hlog' : T * (Real.log r + -(((n : ℝ) * m)/T))
        ≤ T * Real.log (∑ w, ρ₀ w
          * Real.exp (-((n : ℝ) * ℓ w)/T)) := by
      have h := mul_le_mul_of_nonneg_left
        (show Real.log r + -((n : ℝ) * m)/T
            ≤ Real.log (∑ w, ρ₀ w
              * Real.exp (-((n : ℝ) * ℓ w)/T)) from hlog)
        (le_of_lt hT)
      have hnorm : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * (Real.log r + -((n : ℝ) * m)/T) := by
        congr 1
        congr 1
        field_simp
      rw [hnorm]
      exact h
    have hsplit : T * (Real.log r + -(((n : ℝ) * m)/T))
        = T * Real.log r - (n : ℝ) * m := by
      rw [mul_add, hDTneg]
      ring
    rw [hsplit] at hlog'
    -- hlog' : T·log r − n·m ≤ T·logZ
    -- n·e_n ≤ n·m − T·log r
    have hkey : ((n : ℝ)) * (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v)
        ≤ (n : ℝ) * m + T * (-(Real.log r)) := by
      linarith [hatt, hkl, hlog']
    -- деление на n > 0
    have hnposR : (0:ℝ) < (n : ℝ) := by
      have := hn; exact_mod_cast this
    have hkey' : ((n : ℝ)) * ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey]
    have hmuln : ((∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m) * (n : ℝ)
        ≤ T * (-(Real.log r)) := by
      nlinarith [hkey']
    have hdiv : (∑ v, mirrorStep ρ₀
        (fun v => (n : ℝ) * ℓ v) T v * ℓ v) - m
        ≤ T * (-(Real.log r)) / (n : ℝ) :=
      (le_div_iff₀ hnposR).mpr hmuln
    linarith
  -- выбор N: T·(−log r)/ε ≤ N
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      T * (-(Real.log r)) / ε ≤ N :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N + 1, fun n hn => ⟨hlower n, ?_⟩⟩
  have hnpos : (0:ℕ) < n := by omega
  have hbound := hupper n hnpos
  -- (T/n)(−log r) ≤ ε при n ≥ N+1 > N ≥ T(−log r)/ε
  have hnN : ((N : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hNge : T * (-(Real.log r)) ≤ (N : ℝ) * ε :=
    (div_le_iff₀ hε).mp hN
  have hnnz : ((n : ℝ)) ≠ 0 := by
    have : (0:ℕ) < n := hnpos
    exact_mod_cast this.ne'
  have hfin : T * (-(Real.log r)) / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ (show (0:ℝ) < (n : ℝ) by
      have := hnpos; exact_mod_cast this)]
    -- T(−log r) ≤ n·ε ⟸ N·ε ≤ n·ε и T(−log r) ≤ N·ε
    nlinarith [hNge, hnN, hε]
  linarith

/-- Пошаговая нормировка зеркального шага: Z(ρ₀,ℓ,T) =
Σ ρ₀·e^{−ℓ/T} — коэффициент перенормировки весов. -/
noncomputable def stepNorm {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) : ℝ :=
  ∑ w, ρ₀ w * Real.exp (-(ℓ w)/T)

/-- НОРМИРОВКИ ПЕРЕМНОЖАЮТСЯ: нормировка двух
последовательных шагов равна нормировке одного шага с
суммарными потерями: Z(γ₁,ℓ₂)·Z(ρ₀,ℓ₁) = Z(ρ₀,ℓ₁+ℓ₂) —
двойник полугруппового закона на уровне нормировок
(свидетельство: hedge-капитал телескопирует). -/
theorem stepNorm_compose {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ₁ ℓ₂ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) :
    stepNorm (mirrorStep ρ₀ ℓ₁ T) ℓ₂ T * stepNorm ρ₀ ℓ₁ T
      = stepNorm ρ₀ (fun v => ℓ₁ v + ℓ₂ v) T := by
  have hγpos : ∀ w, 0 < mirrorStep ρ₀ ℓ₁ T w :=
    mirrorStep_pos ρ₀ ℓ₁ T hT hρ₀
  have hZ₁ : (0:ℝ) < ∑ w, ρ₀ w * Real.exp (-(ℓ₁ w)/T) :=
    Finset.sum_pos
      (fun w _ => mul_pos (hρ₀ w) (Real.exp_pos _))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have he : ∀ w : V, Real.exp (-(ℓ₁ w)/T)
      * Real.exp (-(ℓ₂ w)/T)
      = Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    rw [← Real.exp_add]
    congr 1
    ring
  -- почленно: γ₁(w)·e^{−ℓ₂/T}·Z₁ = ρ₀(w)·e^{−(ℓ₁+ℓ₂)/T}
  have hterm : ∀ w : V, mirrorStep ρ₀ ℓ₁ T w
      * Real.exp (-(ℓ₂ w)/T)
      * (∑ u, ρ₀ u * Real.exp (-(ℓ₁ u)/T))
      = ρ₀ w * Real.exp (-(ℓ₁ w + ℓ₂ w)/T) := by
    intro w
    unfold mirrorStep
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hZ₁.ne',
      show ρ₀ w * Real.exp (-(ℓ₁ w)/T)
          * Real.exp (-(ℓ₂ w)/T)
        = ρ₀ w * (Real.exp (-(ℓ₁ w)/T)
            * Real.exp (-(ℓ₂ w)/T)) from by ring, he w]
  -- суммирование
  unfold stepNorm
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun w _ => hterm w)

/-- КАПИТАЛ HEDGE ТЕЛЕСКОПИРУЕТ: произведение пошаговых
нормировок траектории равно кумулятивной нормировке:
∏_{k<n} Z(w_k, ℓ_k, T) = Z(ρ₀, Σ_{k<n} ℓ_k, T) —
потенциал-функция MWU/Hedge в замкнутой форме. -/
theorem hedge_wealth_product {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ : V → ℝ) (ℓs : ℕ → V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1) (n : ℕ) :
    (∏ k ∈ Finset.range n,
        stepNorm (mirrorIterate ρ₀ ℓs T k) (ℓs k) T)
      = stepNorm ρ₀ (fun v => ∑ k ∈ Finset.range n, ℓs k v) T := by
  induction n with
  | zero =>
      show (1:ℝ) = stepNorm ρ₀
        (fun v => ∑ k ∈ Finset.range 0, ℓs k v) T
      simp only [Finset.range_zero, Finset.sum_empty, neg_zero,
        div_zero, Real.exp_zero, mul_one, stepNorm, zero_div]
      exact hρ₀1.symm
  | succ m ih =>
      -- кумулятивность: w_m = mirrorStep ρ₀ (Σ_{<m}) T
      have hcum : mirrorIterate ρ₀ ℓs T m
          = mirrorStep ρ₀ (fun v => ∑ k ∈ Finset.range m, ℓs k v) T :=
        mirrorIterate_cumulative ρ₀ ℓs T hT hρ₀ hρ₀1 m
      -- композиция нормировок на уровне ρ₀
      have hcomp := stepNorm_compose ρ₀
        (fun v => ∑ k ∈ Finset.range m, ℓs k v) (ℓs m) T hT hρ₀
      -- кумулятивная сумма range (m+1)
      have hsum : (fun v => ∑ k ∈ Finset.range (m+1), ℓs k v)
          = (fun v => (∑ k ∈ Finset.range m, ℓs k v) + ℓs m v) := by
        funext v
        rw [Finset.sum_range_succ]
      rw [Finset.prod_range_succ, hsum, ih, hcum, mul_comm,
        ← hcomp]

/-- НЕРНСТ-СЭНДВИЧ КАПИТАЛА HEDGE: логарифм капитала
(произведения пошаговых нормировок) зажат:
n·ℓmin − T·log|V| ≤ −T·log(∏ Z_k) ≤ n·ℓmin − T·log(min ρ₀).
Низ: каждый член ≤ e^{−nℓmin/T}, сумма ≤ |V|·e^{−nm/T};
верх: Z ≥ (min ρ₀)·e^{−nℓmin/T} — кумулятивная свободная
энергия итераций зажата энтропийным запасом и минимальным
априорным весом (термодинамический предел капитала). -/
theorem hedge_wealth_nernst {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (n : ℕ) :
    ((n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Fintype.card V : ℝ)
      ≤ -T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    ∧ (-T * Real.log (∏ k ∈ Finset.range n,
          stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
      ≤ (n : ℝ) * (Finset.min' (Finset.univ.image ℓ)
          (Finset.image_nonempty.2 Finset.univ_nonempty))
        - T * Real.log (Finset.min' (Finset.univ.image ρ₀)
          (Finset.image_nonempty.2 Finset.univ_nonempty))) := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hneℓ : (Finset.univ.image ℓ).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  have hneρ : (Finset.univ.image ρ₀).Nonempty :=
    Finset.image_nonempty.2 Finset.univ_nonempty
  obtain ⟨vt, hvt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneℓ)
  obtain ⟨wt, hwt⟩ := Finset.mem_image.mp (Finset.min'_mem _ hneρ)
  have hmle : ∀ v : V, m ≤ ℓ v := fun v =>
    Finset.min'_le (Finset.univ.image ℓ) (ℓ v)
      (Finset.mem_image_of_mem ℓ (Finset.mem_univ v))
  have hrle : ∀ v : V, r ≤ ρ₀ v := fun v =>
    Finset.min'_le (Finset.univ.image ρ₀) (ρ₀ v)
      (Finset.mem_image_of_mem ρ₀ (Finset.mem_univ v))
  have hrpos : (0:ℝ) < r := by
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  -- капитал = кумулятивная нормировка
  have hwealth := hedge_wealth_product ρ₀ (fun _ => ℓ) T hT hρ₀
    hρ₀1 n
  set Z : ℝ := stepNorm ρ₀
    (fun v => ∑ k ∈ Finset.range n, ℓ v) T with hZ
  have hZn : Z = ∑ w, ρ₀ w
      * Real.exp (-((n : ℝ) * ℓ w)/T) := by
    rw [hZ]
    refine Finset.sum_congr rfl fun w _ => ?_
    show ρ₀ w * Real.exp ((-∑ k ∈ Finset.range n, ℓ w)/T)
      = ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Z ≥ r·e^{−nm/T}
  have hZge : r * Real.exp (-((n : ℝ) * m)/T) ≤ Z := by
    rw [hZn]
    have hterm := Finset.single_le_sum
      (f := fun w => ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T))
      (fun w (_ : w ∈ Finset.univ) =>
        mul_nonneg (le_of_lt (hρ₀ w)) (Real.exp_nonneg _))
      (Finset.mem_univ vt)
    rw [hvt.2] at hterm
    nlinarith [hterm, hrle vt, Real.exp_pos
      (-((n : ℝ) * m)/T)]
  -- Z ≤ |V|·e^{−nm/T}
  have hZle : Z ≤ (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) := by
    rw [hZn]
    have hterm : ∀ w : V, ρ₀ w
        * Real.exp (-((n : ℝ) * ℓ w)/T)
        ≤ Real.exp (-((n : ℝ) * m)/T) := by
      intro w
      have h1 : ρ₀ w ≤ 1 := by
        have hs := Finset.single_le_sum
          (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
          (Finset.mem_univ w)
        rw [hρ₀1] at hs
        exact hs
      have h2 : Real.exp (-((n : ℝ) * ℓ w)/T)
          ≤ Real.exp (-((n : ℝ) * m)/T) := by
        refine Real.exp_le_exp.mpr ?_
        have hnle : ((n : ℝ)) * m ≤ (n : ℝ) * ℓ w :=
          mul_le_mul_of_nonneg_left (hmle w)
            (Nat.cast_nonneg n)
        have hnegr : -((n : ℝ) * ℓ w)
            ≤ -((n : ℝ) * m) := by
          have h1 : -((n : ℝ) * ℓ w) ≤ -((n : ℝ) * m) :=
            neg_le_neg hnle
          exact h1
        exact (div_le_div_iff_of_pos_right (show (0:ℝ) < T by
          exact hT)).mpr hnegr
      exact (mul_le_mul h1 h2 (Real.exp_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    calc (∑ w, ρ₀ w * Real.exp (-((n : ℝ) * ℓ w)/T))
        ≤ ∑ w : V, Real.exp (-((n : ℝ) * m)/T) :=
          Finset.sum_le_sum (fun w _ => hterm w)
      _ = (Fintype.card V : ℝ)
          * Real.exp (-((n : ℝ) * m)/T) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- позитивность Z
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  -- логарифмический сэндвич
  have hZpos : (0:ℝ) < Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    linarith [hZge, hrpos']
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcpos : (0:ℝ) < (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T) :=
    mul_pos hcardpos (Real.exp_pos _)
  -- card·e^{−nm/T} = e^{log card − nm/T}
  have hEqC : (Fintype.card V : ℝ)
      * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hcardpos,
      div_eq_mul_inv (Fintype.card V : ℝ)
        (Real.exp (((n : ℝ) * m)/T)), ← Real.exp_neg]
    congr 1
    ring
  -- log Z ≤ log card − nm/T
  have hlogZle : Real.log Z
      ≤ Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T := by
    have h1 := Real.log_le_log hZpos hZle
    rw [hEqC, Real.log_exp] at h1
    exact h1
  -- log r − nm/T ≤ log Z
  -- r·e^{−nm/T} = e^{log r − nm/T}
  have hEqR : r * Real.exp (-((n : ℝ) * m)/T)
      = Real.exp (Real.log r - ((n : ℝ) * m)/T) := by
    rw [Real.exp_sub, Real.exp_log hrpos,
      div_eq_mul_inv r (Real.exp (((n : ℝ) * m)/T)),
      ← Real.exp_neg]
    congr 1
    ring
  -- log r − nm/T ≤ log Z
  have hlogZge : Real.log r - ((n : ℝ) * m)/T ≤ Real.log Z := by
    have hrpos' : (0:ℝ) < r * Real.exp (-((n : ℝ) * m)/T) :=
      mul_pos hrpos (Real.exp_pos _)
    have h1 := Real.log_le_log hrpos' hZge
    rw [hEqR, Real.log_exp] at h1
    exact h1
  -- финальные умножения на −T < 0
  have hTnn : (0:ℝ) ≤ T := le_of_lt hT
  constructor
  · -- nm − T·log card ≤ −T·log Z
    rw [hwealth]
    have hmul := mul_le_mul_of_nonneg_left hlogZle hTnn
    have hsplit : T * (Real.log (Fintype.card V : ℝ)
        - ((n : ℝ) * m)/T)
        = T * Real.log (Fintype.card V : ℝ) - (n : ℝ) * m := by
      rw [mul_sub, mul_div_assoc',
        mul_div_cancel_left₀ _ (ne_of_gt hT)]
    rw [hsplit] at hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith
  · -- −T·log Z ≤ nm − T·log r
    rw [hwealth]
    have hlogZge' : Real.log r + (-(((n : ℝ) * m)/T))
        ≤ Real.log Z := by
      have := hlogZge
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogZge' hTnn
    have hkey : T * Real.log r - (n : ℝ) * m ≤ T * Real.log Z := by
      have hTdiv : T * (((n : ℝ) * m)/T) = (n : ℝ) * m :=
        mul_div_cancel₀ _ (ne_of_gt hT)
      have hexp : T * (Real.log r + -(((n : ℝ) * m)/T))
          = T * Real.log r - T * (((n : ℝ) * m)/T) := by ring
      rw [hexp, hTdiv] at hmul
      exact hmul
    have hneg : -T * Real.log Z = -(T * Real.log Z) := by ring
    rw [hneg]
    linarith

/-- СРЕДНИЙ ЛОГ-КАПИТАЛ СХОДИТСЯ К МИНИМУМУ: из
Нернст-сэндвича капитала: −T·log(∏Z_k)/n → ℓmin при
n → ∞ — средняя свободная энергия на шаг итерированного
hedge стремится к минимальным потерям (скорость —
T·log|V|/n сверху и T·log(min ρ₀)/n снизу). -/
theorem hedge_wealth_rate {V : Type*} [Fintype V] [Nonempty V]
    (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ₀1 : ∑ v, ρ₀ v = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      abs ((-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
        / (n : ℝ)
        - (Finset.min' (Finset.univ.image ℓ)
            (Finset.image_nonempty.2 Finset.univ_nonempty))) ≤ ε := by
  set m := Finset.min' (Finset.univ.image ℓ)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hm
  set r := Finset.min' (Finset.univ.image ρ₀)
    (Finset.image_nonempty.2 Finset.univ_nonempty) with hr
  have hsand : ∀ n : ℕ,
      ((n : ℝ) * m - T * Real.log (Fintype.card V : ℝ)
        ≤ -T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
      ∧ (-T * Real.log (∏ k ∈ Finset.range n,
            stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T)
        ≤ (n : ℝ) * m - T * Real.log r) :=
    fun n => hedge_wealth_nernst ρ₀ ℓ T hT hρ₀ hρ₀1 n
  -- границы смещения на шаг n
  set E := fun n : ℕ => (-T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T))
    / (n : ℝ) with hE
  -- |E n − m| ≤ max(T·log card, −T·log r)/n ≤ ε при больших n
  have hcardpos : (0:ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hrpos : (0:ℝ) < r := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]; exact hρ₀ wt
  have hrle1 : r ≤ 1 := by
    have hneρ : (Finset.univ.image ρ₀).Nonempty :=
      Finset.image_nonempty.2 Finset.univ_nonempty
    obtain ⟨wt, hwt⟩ :=
      Finset.mem_image.mp (Finset.min'_mem _ hneρ)
    have hrw : r = ρ₀ wt := hwt.2.symm
    rw [hrw]
    have h1 := Finset.single_le_sum
      (fun u (_ : u ∈ Finset.univ) => le_of_lt (hρ₀ u))
      (Finset.mem_univ wt)
    rw [hρ₀1] at h1
    exact h1
  have hlogr : Real.log r ≤ 0 :=
    (Real.log_le_log hrpos hrle1).trans_eq Real.log_one
  -- обе границы отклонения: T·log card / n и T·(−log r)/n
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ,
      T * Real.log (Fintype.card V : ℝ) / ε ≤ N1 :=
    exists_nat_ge (T * Real.log (Fintype.card V : ℝ) / ε)
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ,
      T * (-(Real.log r)) / ε ≤ N2 :=
    exists_nat_ge (T * (-(Real.log r)) / ε)
  refine ⟨N1 + N2 + 1, fun n hn => ?_⟩
  have hnpos : (0:ℕ) < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by
    have := hnpos; exact_mod_cast this
  obtain ⟨hlo_n, hhi_n⟩ := hsand n
  set W := -T * Real.log (∏ k ∈ Finset.range n,
      stepNorm (mirrorIterate ρ₀ (fun _ => ℓ) T k) ℓ T) with hWdef
  rw [hWdef] at hlo_n hhi_n
  -- пороги: A := T·log|V| ≥ 0, B := −T·log r ≥ 0
  have hcard1 : (1:ℝ) ≤ (Fintype.card V : ℝ) := by
    have := Fintype.card_pos (α := V)
    exact_mod_cast this
  have hA : (0:ℝ) ≤ T * Real.log (Fintype.card V : ℝ) :=
    mul_nonneg (le_of_lt hT) (Real.log_nonneg hcard1)
  have hB : (0:ℝ) ≤ T * (-(Real.log r)) :=
    mul_nonneg (le_of_lt hT) (neg_nonneg.mpr hlogr)
  -- W/n − m = (W − n·m)/n
  rw [div_sub' hnR.ne', abs_le]
  constructor
  · -- −ε ≤ (W − nm)/n ⟸ nm − A ≤ W и A ≤ n·ε
    rw [le_div_iff₀ hnR]
    -- цель: −ε·n ≤ W − n·m
    have hN1le : (N1 : ℝ) ≤ (n : ℝ) := by
      have : (N1 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN1e : T * Real.log (Fintype.card V : ℝ) ≤ (N1 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN1
    nlinarith [hN1e, hN1le, hε, hlo_n]
  · -- (W − nm)/n ≤ ε ⟸ W ≤ nm + B и B ≤ n·ε
    rw [div_le_iff₀ hnR]
    have hN2le : (N2 : ℝ) ≤ (n : ℝ) := by
      have : (N2 : ℕ) ≤ n := by omega
      exact_mod_cast this
    have hN2e : T * (-(Real.log r)) ≤ (N2 : ℝ) * ε :=
      (div_le_iff₀ hε).mp hN2
    nlinarith [hN2e, hN2le, hε, hhi_n]


/-! ### Источник №70 (arXiv 2609.15897): вариационный шаг как спуск
JKO-подобная схема: каждое экспоненциальное обновление —
минимизация свободной энергии F(q) = ⟨q,ℓ⟩ + T·KL(q‖ρ₀).
Отсюда НЕВОЗРАСТАНИЕ F вдоль итераций при том же ландшафте ℓ
(частный случай: конкурент q = ρ₀ с KL = 0). -/

/-- ВАРИАЦИОННЫЙ СПУСК ЗЕРКАЛЬНОГО ШАГА: γ = mirrorStep ρ₀ ℓ T
даёт F(γ) := ⟨γ,ℓ⟩ + T·KL(γ‖ρ₀) ≤ ⟨ρ₀,ℓ⟩ = F(ρ₀) — каждое
экспоненциальное обновление НЕ УВЕЛИЧИВАЕТ свободную энергию
(конкурент ρ₀ имеет нулевой KL-штраф; частный случай
вариационного принципа источника №70, arXiv 2609.15897). -/
theorem mirror_step_variational_descent {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1) :
    (∑ v, mirrorStep ρ₀ ℓ T v * ℓ v)
      + T * (∑ v, mirrorStep ρ₀ ℓ T v
          * Real.log (mirrorStep ρ₀ ℓ T v / ρ₀ v))
      ≤ ∑ v, ρ₀ v * ℓ v := by
  -- достижимость: F(γ) = −T·log Z ...
  have hatt := mirror_descent_attainment ρ₀ ℓ T hT hρ₀
  -- ... и пол с конкурентом ρ₀ (KL(ρ₀‖ρ₀) = 0):
  --   −T·log Z ≤ ⟨ρ₀,ℓ⟩ + T·KL(ρ₀‖ρ₀) = ⟨ρ₀,ℓ⟩
  have hself : (∑ v, ρ₀ v * Real.log (ρ₀ v / ρ₀ v)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v _
    rw [div_self (hρ₀ v).ne', Real.log_one, mul_zero]
  have hfloor := mirror_descent_floor ρ₀ ℓ T hT hρ₀ ρ₀ hρ₀ hρ1
  rw [hself, mul_zero] at hfloor
  linarith

/-- ИТЕРАЦИОННАЯ МОНОТОННОСТЬ (№70): при фиксированном
ландшафте ℓ частная свободная энергия шага не возрастает
вдоль траектории mirrorIterate: F_{k+1} ≤ F_k, где
F_k = ⟨ρ_k,ℓ⟩ (KL-штраф относительно ρ_k обнуляется на
следующем шаге). Кумулятивный аналог убывания свободной
энергии в JKO-схеме. -/
theorem mirrorIterate_partial_mono {V : Type*} [Fintype V]
    [Nonempty V] (ρ₀ ℓ : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hρ₀ : ∀ v, 0 < ρ₀ v) (hρ1 : ∑ v, ρ₀ v = 1)
    (ℓs : ℕ → V → ℝ) (k : ℕ) (hls : ℓs k = ℓ) :
    ∑ v, (mirrorIterate ρ₀ ℓs T (k+1)) v * ℓ v
      ≤ ∑ v, (mirrorIterate ρ₀ ℓs T k) v * ℓ v := by
  have hpos : ∀ v, 0 < mirrorIterate ρ₀ ℓs T k v :=
    mirrorIterate_pos ρ₀ ℓs T hT hρ₀ k
  have hsum : ∑ v, mirrorIterate ρ₀ ℓs T k v = 1 :=
    mirrorIterate_sum_one ρ₀ ℓs T hT hρ₀ hρ1 k
  have hstep : mirrorIterate ρ₀ ℓs T (k+1)
      = mirrorStep (mirrorIterate ρ₀ ℓs T k) (ℓs k) T := rfl
  rw [hls] at hstep
  rw [hstep]
  -- KL-штраф ≥ 0, поэтому вариационный спуск даёт ⟨γ,ℓ⟩ ≤ F(γ) ≤ ⟨ρ_k,ℓ⟩
  have hd := mirror_step_variational_descent
    (mirrorIterate ρ₀ ℓs T k) ℓ T hT hpos hsum
  have hKL0 : (0:ℝ) ≤ T * (∑ v, mirrorStep
      (mirrorIterate ρ₀ ℓs T k) ℓ T v
      * Real.log (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        / mirrorIterate ρ₀ ℓs T k v)) := by
    have hγpos : ∀ v, 0 < mirrorStep
        (mirrorIterate ρ₀ ℓs T k) ℓ T v :=
      mirrorStep_pos _ ℓ T hT hpos
    have hγ1 : ∑ v, mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T v
        = 1 := mirrorStep_sum_one _ ℓ T hT hpos
    have := finite_kl_nonneg (mirrorStep (mirrorIterate ρ₀ ℓs T k) ℓ T)
      (mirrorIterate ρ₀ ℓs T k) hγpos hγ1 hpos hsum
    exact mul_nonneg hT.le this
  linarith

end Hagi.Optimization
end C236_md

section C236_hedge
/-!
# Exponential-weights routing

The per-step potential bound for Hedge routing, the product
telelescope, and the router regret bound.
-/

open Real Finset Set

namespace Hagi.Autonomy

theorem exp_neg_le_quad (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  by_cases hy0 : y = 0
  · simp [hy0]
  set f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x) with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (x - 1 + Real.exp (-x)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      have h3 : HasDerivAt (fun x => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have h4 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * x / 2) x := h3.div_const (2 : ℝ)
      simpa using h4
    have hA : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - x) (x - 1) x :=
      HasDerivAt.sub h2 (hasDerivAt_id x)
    have hB : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 / 2 - x)) (0 + (x - 1)) x :=
      HasDerivAt.add (hasDerivAt_const x (1 : ℝ)) hA
    have hC : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 / 2 - x) - Real.exp (-x))
      ((0 + (x - 1)) - (-Real.exp (-x))) x := by
      have hE : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
        have hE0 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) x := (hasDerivAt_id x).neg
        have hE2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * -1) x :=
          HasDerivAt.comp x (hasDerivAt_exp (-x)) hE0
        exact hE2.congr_deriv (by ring)
      exact HasDerivAt.sub hB hE
    exact hC.congr_of_eventuallyEq (by filter_upwards with z; ring) |>.congr_deriv (by ring)
  -- MVT on [0, y]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hcont : ContinuousOn f (Set.Icc 0 y) :=
    (show Continuous f from by continuity).continuousOn
  obtain ⟨ξ, hξm, hξ2⟩ := exists_hasDerivAt_eq_slope f
    (fun x => x - 1 + Real.exp (-x)) hypos hcont
    (fun x hx => hderiv x)
  -- f y - f 0 = f'(ξ) * (y - 0), and f' ξ ≥ 0
  have hposξ : 0 ≤ ξ - 1 + Real.exp (-ξ) := by
    have := add_one_le_exp (-ξ)
    linarith
  have hval : (ξ - 1 + Real.exp (-ξ)) = (f y - f 0) / (y - 0) := hξ2
  have h0 : f 0 = 0 := by simp [hf]
  rw [h0, sub_zero] at hval
  have hmul : (ξ - 1 + Real.exp (-ξ)) * y = f y := by
    rw [hval]
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith : (y:ℝ) - 0 ≠ 0)]
    ring
  -- f y = y · f' ξ ≥ 0
  have hnn : 0 ≤ (ξ - 1 + Real.exp (-ξ)) * y := by positivity
  rw [hmul] at hnn
  simp only [hf] at hnn
  linarith

open Finset

/-- For losses `l i ∈ [0, 1]`, weights `p` with `p i ≥ 0` and
`Σ p = 1`, and `η ∈ [0, 1]`:
`Σ p i * exp (-η * l i) ≤ 1 - η * Σ p i * l i + η ^ 2 / 2`. -/
theorem hedge_step {ι : Type} [Fintype ι] (p l : ι → ℝ) (eta : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hl : ∀ i, 0 ≤ l i ∧ l i ≤ 1) (heta : 0 ≤ eta ∧ eta ≤ 1) :
    ∑ i, p i * Real.exp (-eta * l i) ≤ 1 - eta * ∑ i, p i * l i + eta ^ 2 / 2 := by
  have hquad : ∀ i, Real.exp (-eta * l i) ≤ 1 - eta * l i + (eta * l i) ^ 2 / 2 := by
    intro i
    have h := exp_neg_le_quad (eta * l i) (mul_nonneg heta.1 (hl i).1)
    convert h using 1 <;> ring
  have hmul : ∀ i, p i * Real.exp (-eta * l i)
      ≤ p i * (1 - eta * l i + (eta * l i) ^ 2 / 2) :=
    fun i => mul_le_mul_of_nonneg_left (hquad i) (hp i)
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (f := fun i => p i * Real.exp (-eta * l i))
    (g := fun i => p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)) (fun i _ => hmul i)
  have hsplit : ∑ i, p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)
      = (∑ i, p i) - eta * (∑ i, p i * l i)
        + ∑ i, p i * ((eta * l i) ^ 2 / 2) := by
    have e1 : ∑ i : ι, p i * (1 - eta * l i + (eta * l i) ^ 2 / 2)
        = ∑ i : ι, (p i - eta * (p i * l i) + p i * ((eta * l i) ^ 2 / 2)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1]
    have e2 : ∑ i : ι, (p i - eta * (p i * l i) + p i * ((eta * l i) ^ 2 / 2))
        = (∑ i : ι, (p i - eta * (p i * l i))) + ∑ i : ι, p i * ((eta * l i) ^ 2 / 2) :=
      sum_add_distrib
    have e3 : ∑ i : ι, (p i - eta * (p i * l i))
        = (∑ i : ι, p i) - eta * (∑ i : ι, p i * l i) := by
      rw [sum_sub_distrib]
      rw [Finset.mul_sum (s := Finset.univ) (f := fun i => p i * l i) (a := eta)]
    rw [e2, e3]
  -- last term ≤ η²/2 · Σp = η²/2 (since l ≤ 1)
  have hsq : ∀ i, p i * ((eta * l i) ^ 2 / 2) ≤ p i * (eta ^ 2 / 2) := by
    intro i
    have h1 : (eta * l i) ^ 2 ≤ eta ^ 2 := by
      have := hl i
      nlinarith [sq_nonneg (eta * l i - eta)]
    calc p i * ((eta * l i) ^ 2 / 2) ≤ p i * (eta ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (hp i)
      _ = p i * (eta ^ 2 / 2) := rfl
  have hlast : ∑ i, p i * ((eta * l i) ^ 2 / 2) ≤ eta ^ 2 / 2 := by
    calc ∑ i, p i * ((eta * l i) ^ 2 / 2)
        ≤ ∑ i, p i * (eta ^ 2 / 2) :=
          Finset.sum_le_sum (s := Finset.univ) (f := fun i => p i * ((eta * l i) ^ 2 / 2))
            (g := fun i => p i * (eta ^ 2 / 2)) (fun i _ => hsq i)
      _ = (∑ i, p i) * (eta ^ 2 / 2) :=
          (Finset.sum_mul (s := Finset.univ) (f := fun i => p i)
            (a := eta ^ 2 / 2)).symm
      _ = eta ^ 2 / 2 := by rw [hsum, one_mul]
  calc ∑ i, p i * Real.exp (-eta * l i)
      ≤ (∑ i, p i) - eta * (∑ i, p i * l i)
        + ∑ i, p i * ((eta * l i) ^ 2 / 2) := hsplit ▸ hsumle
    _ ≤ (∑ i, p i) - eta * (∑ i, p i * l i) + eta ^ 2 / 2 := by
          have hadd : ∑ i, p i * ((eta * l i) ^ 2 / 2) ≤ eta ^ 2 / 2 := hlast
          linarith
    _ = 1 - eta * (∑ i, p i * l i) + eta ^ 2 / 2 := by
          rw [hsum]

theorem hedge_telescope (u : ℕ → ℝ) (hnn : ∀ t, (0:ℝ) ≤ 1 + u t) (T : ℕ) :
    ∏ t ∈ Finset.range T, (1 + u t) ≤ Real.exp (∑ t ∈ Finset.range T, u t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := ih
      have h2 : (1:ℝ) + u T ≤ Real.exp (u T) := by
        have := add_one_le_exp (u T)
        linarith
      calc ∏ t ∈ Finset.range (T+1), (1 + u t)
          = (∏ t ∈ Finset.range T, (1 + u t)) * (1 + u T) :=
            Finset.prod_range_succ (fun t => 1 + u t) T
      _ ≤ Real.exp (∑ t ∈ Finset.range T, u t) * Real.exp (u T) :=
          mul_le_mul h1 h2 (hnn T) (le_of_lt (Real.exp_pos (∑ t ∈ Finset.range T, u t)))
      _ = Real.exp (∑ t ∈ Finset.range T, u t + u T) := by rw [Real.exp_add]
      _ = Real.exp (∑ t ∈ Finset.range (T+1), u t) := by
          rw [Finset.sum_range_succ]

/-- Assuming the survivor bound `(1/K) * exp (-η * Lstar) ≤
exp (-η * A + T * η ^ 2 / 2)` with `η > 0` and `K > 0`, the
cumulative-loss gap satisfies `A - Lstar ≤ log K / η + η * T / 2`.
At `η = √(ln K / T)` this is `2√(T * ln K)`. -/
theorem router_regret_bound (K T : ℕ) (eta A Lstar : ℝ)
    (hK : 0 < K) (heta : 0 < eta)
    (hsurv : (1:ℝ) / K * Real.exp (-eta * Lstar)
      ≤ Real.exp (-eta * A + T * eta ^ 2 / 2)) :
    A - Lstar ≤ Real.log K / eta + eta * T / 2 := by
  have hlogle : Real.log ((1:ℝ) / K * Real.exp (-eta * Lstar))
      ≤ -eta * A + T * eta ^ 2 / 2 := by
    have h1 := Real.log_le_log (x := (1:ℝ) / K * Real.exp (-eta * Lstar))
      (y := Real.exp (-eta * A + T * eta ^ 2 / 2)) (by positivity) hsurv
    rw [Real.log_exp] at h1
    exact h1
  rw [Real.log_mul (by positivity) (by positivity)] at hlogle
  rw [Real.log_exp] at hlogle
  -- log(1/K) = -log K
  have hlog1 : Real.log ((1:ℝ) / K) = -Real.log K := by
    rw [Real.log_div (by norm_num) (by positivity)]
    norm_num
  rw [hlog1] at hlogle
  -- now: -log K - eta*Lstar <= -eta*A + T*eta^2/2; divide by eta and finish
  field_simp
  linarith

end Hagi.Autonomy
end C236_hedge

section C236_hsurv
/-!
# HedgeSurvivor — склейка (a) аудита v5

Вывод посылки выживания `hsurv` из САМИХ hedge_step +
hedge_telescope: строится экспоненциально-взвешенный процесс
(веса w, потенциал W, нормированные p), шаг связывается с
hedge_step, произведение — с монотонностью exp, и получается
`(1/K)·exp(-η·L*) ≤ exp(-η·A + T·η²/2)`.
-/

namespace Hagi.Autonomy

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Веса экспоненциальных весов: w 0 = 1, мультипликативное
обновление. -/
noncomputable def ewWeight (l : ℕ → ι → ℝ) (eta : ℝ) :
    ℕ → ι → ℝ
  | 0, _ => 1
  | t + 1, i => ewWeight l eta t i * Real.exp (-eta * l t i)

/-- Потенциал (суммарная масса весов). -/
noncomputable def ewPot (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) : ℝ :=
  ∑ i, ewWeight l eta t i

/-- Нормированные веса (распределение алгоритма). -/
noncomputable def ewNorm (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) : ℝ :=
  ewWeight l eta t i / ewPot l eta t

theorem ewWeight_nonneg (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 ≤ ewWeight l eta t i := by
  induction t with
  | zero => simp [ewWeight]
  | succ t ih =>
      simp only [ewWeight]
      exact mul_nonneg ih (Real.exp_pos _).le

/-- Явная форма веса: w T i = exp (-η · Σ_{t<T} l t i). -/
theorem ewWeight_exp (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι) :
    ewWeight l eta T i
      = Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) := by
  induction T with
  | zero => simp [ewWeight]
  | succ T ih =>
      rw [Finset.sum_range_succ, ewWeight, ih, ← Real.exp_add]
      congr 1
      ring

theorem ewWeight_pos (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 < ewWeight l eta t i := by
  rw [ewWeight_exp]
  positivity

theorem ewPot_pos (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    0 < ewPot l eta t := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  unfold ewPot
  exact Finset.sum_pos' (fun i _ => ewWeight_nonneg l eta t i)
    ⟨j, Finset.mem_univ _, ewWeight_pos l eta t j⟩

theorem ewNorm_nonneg (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    0 ≤ ewNorm l eta t i :=
  div_nonneg (ewWeight_nonneg l eta t i) (ewPot_pos l eta t).le

theorem ewNorm_sum (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    ∑ i, ewNorm l eta t i = 1 := by
  have h : (∑ i ∈ Finset.univ, ewWeight l eta t i)
      / ewPot l eta t
      = ∑ i ∈ Finset.univ, ewWeight l eta t i / ewPot l eta t :=
    Finset.sum_div Finset.univ (fun i => ewWeight l eta t i)
      (ewPot l eta t)
  unfold ewNorm at h ⊢
  rw [← h]
  exact div_self (ne_of_gt (ewPot_pos l eta t))

/-- Потенциальный шаг: W(t+1) = W t · Σ p t i exp(-η l t i). -/
theorem ewPot_step (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) :
    ewPot l eta (t + 1)
      = ewPot l eta t
        * ∑ i, ewNorm l eta t i * Real.exp (-eta * l t i) := by
  unfold ewPot ewNorm
  simp only [ewWeight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hW : ewPot l eta t = ∑ i, ewWeight l eta t i := rfl
  rw [hW]
  have hsum_ne : (∑ i, ewWeight l eta t i) ≠ 0 := by
    have := ewPot_pos l eta t
    rw [hW] at this
    exact ne_of_gt this
  field_simp


/-- ВЕРХНИЙ ТЕЛЕСКОП: W T ≤ card ι · exp (-η·A + T·η²/2),
где A = Σ_t a_t, a_t = Σ_i p t i · l t i — потери алгоритма.
Шаг — hedge_step, переход 1+u ≤ exp u, связка — индукция. -/
theorem ewPot_upper (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1)
    (heta : 0 ≤ eta ∧ eta ≤ 1) :
    ewPot l eta T ≤ (Fintype.card ι : ℝ)
      * Real.exp (-eta * (∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i) + T * eta ^ 2 / 2) := by
  have hbase : ewPot l eta 0 = (Fintype.card ι : ℝ) := by
    simp [ewPot, ewWeight]
  induction T with
  | zero => rw [hbase]; simp
  | succ T ih =>
      have hlT : ∀ i, 0 ≤ l T i ∧ l T i ≤ 1 := hl T (by omega)
      have hstep : ewPot l eta (T + 1)
          ≤ ewPot l eta T * (1 - eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
        rw [ewPot_step l eta T]
        exact mul_le_mul_of_nonneg_left
          (hedge_step (ewNorm l eta T) (l T) eta
            (ewNorm_nonneg l eta T) (ewNorm_sum l eta T) hlT heta)
          (ewPot_pos l eta T).le
      -- шаг через hedge_step и 1+u ≤ exp u
      have hexp : (1:ℝ) + (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2) ≤ Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2) := by
        have := Real.add_one_le_exp (-eta * (∑ i, ewNorm l eta T i * l T i)
          + eta ^ 2 / 2)
        linarith
      have hW := ih (fun t ht => hl t (by omega))
      calc ewPot l eta (T + 1)
          ≤ ewPot l eta T * (1 - eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
              rw [ewPot_step l eta T]
              exact mul_le_mul_of_nonneg_left
                (hedge_step (ewNorm l eta T) (l T) eta
                  (ewNorm_nonneg l eta T) (ewNorm_sum l eta T) hlT heta)
                (ewPot_pos l eta T).le
        _ ≤ ewPot l eta T * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
            + eta ^ 2 / 2) := by
              have hnn : (0:ℝ) ≤ ewPot l eta T := (ewPot_pos l eta T).le
              have hnn1 : (0:ℝ) ≤ Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2) := Real.exp_nonneg _
              have h1 : (1:ℝ) - eta * (∑ i, ewNorm l eta T i * l T i)
                  + eta ^ 2 / 2
                  = 1 + (-eta * (∑ i, ewNorm l eta T i * l T i)
                    + eta ^ 2 / 2) := by ring
              rw [h1]
              exact mul_le_mul_of_nonneg_left hexp hnn
        _ ≤ ((Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2))
            * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
              + eta ^ 2 / 2) := by
              apply mul_le_mul_of_nonneg_right hW
              exact Real.exp_nonneg _
        _ = (Fintype.card ι : ℝ)
            * (Real.exp (-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2)
              * Real.exp (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2)) := by ring
        _ = (Fintype.card ι : ℝ)
            * Real.exp ((-eta * (∑ t ∈ Finset.range T,
              ∑ i, ewNorm l eta t i * l t i) + (T:ℝ) * eta ^ 2 / 2)
              + (-eta * (∑ i, ewNorm l eta T i * l T i)
                + eta ^ 2 / 2)) := by rw [← Real.exp_add]
        _ = (Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range (T + 1),
              ∑ i, ewNorm l eta t i * l t i)
              + ((T:ℝ) + 1) * eta ^ 2 / 2) := by
              congr 2
              rw [Finset.sum_range_succ]
              ring
        _ = (Fintype.card ι : ℝ)
            * Real.exp (-eta * (∑ t ∈ Finset.range (T + 1),
              ∑ i, ewNorm l eta t i * l t i)
              + ((T + 1 : ℕ) : ℝ) * eta ^ 2 / 2) := by
              congr 2
              push_cast
              ring


/-- НИЖНЯЯ ГРАНИЦА: потенциал доминирует любую экспорту —
W T ≥ exp (-η·L i*). -/
theorem ewPot_lower (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι) :
    Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) ≤ ewPot l eta T := by
  have hterm : Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ ewWeight l eta T i :=
    (ewWeight_exp l eta T i).symm ▸ le_refl _
  have hsum : ewWeight l eta T i ≤ ∑ j, ewWeight l eta T j :=
    Finset.single_le_sum (f := fun j => ewWeight l eta T j)
      (fun j _ => ewWeight_nonneg l eta T j) (Finset.mem_univ i)
  exact hterm.trans hsum

/-- СКЛЕЙКА (a) — ПОСЫЛКА ВЫЖИВАНИЯ ВЫВЕДЕНА: для EW-процесса
hsurv из router_regret_bound выполняется С АЛГОРИТМИЧЕСКИМИ
потерями A = Σ_t Σ_i p t i l t i. Больше не гипотеза. -/
theorem hsurv_derived (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (hl : ∀ t < T, ∀ i, 0 ≤ l t i ∧ l t i ≤ 1)
    (heta : 0 ≤ eta ∧ eta ≤ 1) :
    (1:ℝ) / (Fintype.card ι : ℕ)
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ Real.exp (-eta * (∑ t ∈ Finset.range T,
        ∑ i, ewNorm l eta t i * l t i) + ((T:ℝ)) * eta ^ 2 / 2) := by
  have hlow := ewPot_lower l eta T i
  have hhigh := ewPot_upper l eta T hl heta
  -- exp(-η L i) ≤ W T ≤ card · exp(-η A + Tη²/2)
  have hkey : Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (Fintype.card ι : ℝ)
        * Real.exp (-eta * (∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i) + T * eta ^ 2 / 2) :=
    hlow.trans hhigh
  have hcardpos : (0:ℝ) < (Fintype.card ι : ℕ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_mul_eq_mul_div, one_mul]
  refine (div_le_iff₀ hcardpos).mpr ?_
  calc Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (Fintype.card ι : ℝ)
        * Real.exp (-eta * ∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i + (T:ℝ) * eta ^ 2 / 2) := hkey
    _ = Real.exp (-eta * ∑ t ∈ Finset.range T,
          ∑ i, ewNorm l eta t i * l t i + (T:ℝ) * eta ^ 2 / 2)
        * (Fintype.card ι : ℝ) := by ring


/-- АНТИ-ЛОК-ИН: при неотрицательных потерях и η ≥ 0
нормированный вес ЛЮБОГО ключа после T шагов удовлетворяет
экспоненциальной нижней оценке выживания
`ewNorm ≥ (1/K)·exp(−η·Σ_{t<T} ℓ t i)`. Вес может убывать не
быстрее, чем экспоненциально по собственной накопленной потере —
он никогда не ноль: роутер не может навсегда shut out ключ с
ограниченными потерями. (Обёртка над `ewWeight_exp`; посылки
слабее, чем у `hsurv_derived` — только ℓ ≥ 0, регрет-сторона при
этом НЕ утверждается.) -/
theorem ewNorm_survivor_lower (l : ℕ → ι → ℝ) (eta : ℝ) (T : ℕ) (i : ι)
    (heta : 0 ≤ eta) (hl : ∀ t, ∀ j, 0 ≤ l t j) :
    (1 / (Fintype.card ι : ℝ))
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ ewNorm l eta T i := by
  have hwle1 : ∀ j, ewWeight l eta T j ≤ 1 := by
    intro j
    rw [ewWeight_exp]
    have hL : 0 ≤ ∑ t ∈ Finset.range T, l t j :=
      Finset.sum_nonneg fun t _ => hl t j
    calc Real.exp (-eta * ∑ t ∈ Finset.range T, l t j)
        ≤ Real.exp (0:ℝ) := (Real.exp_le_exp).2 (by nlinarith [mul_nonneg heta hL])
      _ = 1 := Real.exp_zero
  have hWpos : 0 < ewPot l eta T := ewPot_pos l eta T
  have hcardpos : (0:ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hEpos : 0 < Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) :=
    Real.exp_pos _
  have hW : ewPot l eta T ≤ (Fintype.card ι : ℝ) := by
    calc ewPot l eta T = ∑ j, ewWeight l eta T j := rfl
      _ ≤ ∑ j : ι, (1:ℝ) := Finset.sum_le_sum fun j _ => hwle1 j
      _ = (Fintype.card ι : ℝ) := by simp
  have hone : (1:ℝ) / (Fintype.card ι : ℝ) ≤ 1 / ewPot l eta T := by
    rw [le_div_iff₀ hWpos, div_mul_eq_mul_div, div_le_one]
    · rw [one_mul]; exact hW
    · exact_mod_cast Fintype.card_pos
  calc (1 / (Fintype.card ι : ℝ))
      * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i)
      ≤ (1 / ewPot l eta T)
        * Real.exp (-eta * ∑ t ∈ Finset.range T, l t i) :=
        mul_le_mul_of_nonneg_right hone hEpos.le
    _ = ewNorm l eta T i := by
        unfold ewNorm
        rw [ewWeight_exp, div_mul_eq_mul_div, one_mul]

open Hagi.Optimization

variable {ι : Type} [Fintype ι] [Nonempty ι]

theorem ewNorm_as_mirror (l : ℕ → ι → ℝ) (eta : ℝ) (t : ℕ) (i : ι) :
    ewNorm l eta t i
      = mirrorStep (fun _ => (1:ℝ))
          (fun j => ∑ s ∈ Finset.range t, l s j) (1 / eta) i := by
  unfold ewNorm mirrorStep
  have hw : ∀ j, ewWeight l eta t j
      = (1:ℝ) * Real.exp (-((∑ s ∈ Finset.range t, l s j)) / (1/eta)) := by
    intro j
    rw [ewWeight_exp]
    field_simp
  have hWpot : ewPot l eta t
      = ∑ x, (1:ℝ) * Real.exp (-((∑ s ∈ Finset.range t, l s x)) / (1/eta)) :=
    Finset.sum_congr rfl (fun x _ => hw x)
  rw [hw i, hWpot]

end Hagi.Autonomy
end C236_hsurv
