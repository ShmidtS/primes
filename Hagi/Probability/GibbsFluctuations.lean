/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.GibbsCooling
import Hagi.Probability.MomentBounds
set_option linter.style.header false

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
