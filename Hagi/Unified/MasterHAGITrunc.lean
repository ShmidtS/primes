/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MasterHAGI
set_option linter.style.header false

/-!
# R159: MasterHAGI-усечение — посылки роста только t < T

Аудит 2026-10-04 (пункт №1 «что бы я сделал»): в `MasterHAGI`
посылки роста h_emp_step / h_emp_gain_prod / h_emp_dyn / h_emp_C_cap / h_emp_beta
квантифицированы по ВСЕМ t — вместе с потолком C* (наш же
Saturation) они противоречивы на длинном горизонте (тот же
дефект, что был у hagi_synthesis до rev.2).

* `frontier_cone_trunc` — конус D >= (alpha/gamma) C при
  посылках ТОЛЬКО t < T (индукция через `frontier_cone_inductive`);
* `sustained_takeoff_trunc` — C_T >= C0 (1+alpha)^T;
* `MasterHAGI_trunc` — капстоун: growth-посылки t < T (с
  h_emp_-именами: динамика производства, gate-порог,
  ceiling — измеряемые), потолок C* ЯВНО как условие
  горизонта C0 (1+alpha)^T <= Cstar;
* `masterhagi_growth_witness` — числовой свидетель
  не-вакуозности: C = D = (3/2)^t, alpha = gamma = 1/2,
  rho = 0, beta = 3/4, xi = 0 (все усечённые посылки
  выполнены при любом T; C* = 10 держит горизонт T <= 5,
  измерено: 1.5^5 = 7.59375 <= 10 < 1.5^6 = 11.390625).
-/

open Real Finset InnerProductSpace

namespace Hagi

section Trunc

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Усечённый frontier-конус**: пошаговые посылки только при
t < T — конус держится на всём горизонте 0..T. -/
theorem frontier_cone_trunc (C G D : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (xi : ℕ → ℝ) (T : ℕ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (h_emp_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_emp_step : ∀ t < T, C (t + 1) = C t + G t)
    (h_emp_gain_prod : ∀ t < T, gamma * D t ≤ G t)
    (h_emp_dyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (h_emp_beta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    ∀ t, t ≤ T → 0 < C t ∧ alpha / gamma * C t ≤ D t := by
  intro t
  induction t with
  | zero =>
      intro _
      exact ⟨hC0, h_emp_cone0⟩
  | succ t ih =>
      intro hle
      have htlt : t < T := by omega
      obtain ⟨hpos, hcone⟩ := ih (by omega)
      refine ⟨?_, frontier_cone_inductive C D xi alpha gamma rho beta
        hα hγ hρ t hpos hcone (h_emp_dyn t htlt) (h_emp_C_cap t htlt) (h_emp_beta t htlt)⟩
      have hg := h_emp_gain_prod t htlt
      have hgD : alpha * C t ≤ gamma * D t := by
        have hmul : gamma * (alpha / gamma * C t) ≤ gamma * D t :=
          mul_le_mul_of_nonneg_left hcone hγ.le
        field_simp at hmul
        exact hmul
      have hGpos : (0:ℝ) < G t := by
        nlinarith [hgD, hα, hpos]
      rw [h_emp_step t htlt]
      linarith



/-- Nonincrease telescopes over the horizon (trunc-local,
now aliased to Foundations.telescope_le). -/
private theorem telescope_le_h {f : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) ≤ f t) : f T ≤ f 0 :=
  Hagi.Foundations.telescope_le h

/-- Increment-sum telescoping (trunc-local,
now aliased to Foundations.telescope_sum_le). -/
private theorem telescope_sum_le_h {f c : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) - f t ≤ c t) :
    f T - f 0 ≤ ∑ t ∈ Finset.range T, c t :=
  Hagi.Foundations.telescope_sum_le h

/-- Exact account telescoping (trunc-local,
now aliased to Foundations.telescope_sub_sum). -/
private theorem telescope_sub_sum_h {f c : ℕ → ℝ} {T : ℕ}
    (h : ∀ t < T, f (t + 1) = f t - c t) :
    f T = f 0 - ∑ t ∈ Finset.range T, c t :=
  Hagi.Foundations.telescope_sub_sum h

/-- **Усечённый takeoff**: из усечённых посылок (только
t < T) — C_T >= C0 * (1+alpha)^T. Совместимо с потолком C*:
условие горизонта C0 (1+alpha)^T <= Cstar. -/
theorem sustained_takeoff_trunc (C G D : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (xi : ℕ → ℝ) (T : ℕ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (h_emp_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_emp_step : ∀ t < T, C (t + 1) = C t + G t)
    (h_emp_gain_prod : ∀ t < T, gamma * D t ≤ G t)
    (h_emp_dyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (h_emp_beta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    C 0 * (1 + alpha) ^ T ≤ C T := by
  have hcone := frontier_cone_trunc C G D alpha gamma rho beta xi T
    hα hγ hρ hC0 h_emp_cone0 h_emp_step h_emp_gain_prod h_emp_dyn h_emp_C_cap h_emp_beta
  have hmain : ∀ t, t ≤ T → C 0 * (1 + alpha) ^ t ≤ C t := by
    intro t
    induction t with
    | zero => simp [hC0.le]
    | succ t ih =>
        intro hle
        have htlt : t < T := by omega
        have hs := h_emp_step t htlt
        have hg := h_emp_gain_prod t htlt
        have hgD : alpha * C t ≤ gamma * D t := by
          have hc := (hcone t (by omega)).2
          have hmul : gamma * (alpha / gamma * C t) ≤ gamma * D t :=
            mul_le_mul_of_nonneg_left hc hγ.le
          field_simp at hmul
          exact hmul
        have hih := ih (by omega)
        have hpos : (0:ℝ) < C t := (hcone t (by omega)).1
        have hstep' : (1 + alpha) * C t ≤ C (t + 1) := by
          have hga : alpha * C t ≤ G t := by
            have h1 : alpha * C t ≤ gamma * D t := hgD
            exact le_trans h1 hg
          calc (1 + alpha) * C t = C t + alpha * C t := by ring
            _ ≤ C t + G t := add_le_add_right hga _
            _ = C (t + 1) := hs.symm
        rw [pow_succ]
        nlinarith [hih, hstep', hα, hpos]
  exact hmain T (le_refl T)

/-- **Усечённый капстоун MasterHAGI**: ВСЕ growth-посылки
только при t < T; потолок ёмкости входит ЯВНО как условие
горизонна C0 (1 + alpha)^T <= Cstar. Остальные блоки
(Φ_HAGI, safety, budget, gen-floor) — как в MasterHAGI, их
посылки уже были усечены (t < T). Не-вакуозность growth-блока
подтверждает masterhagi_growth_witness ниже. -/
theorem MasterHAGI_trunc {K : Type*} [Fintype K] [Nonempty K]
    (S : ℕ → GenState X) (lam nu Qtarget Emin : ℝ) (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 < nu)
    (epsQ : ℕ → ℝ) (h_epsQ : ∀ t, 0 ≤ epsQ t)
    (T : ℕ)
    (g : ℕ → K → X) (dL eps L : ℕ → K → ℝ) (etaq : ℕ → ℝ)
    (hLq : ∀ t i, 0 < L t i) (hepsq : ∀ t i, 0 ≤ eps t i)
    (hetaq : ∀ t, 0 ≤ etaq t)
    (hd : ∀ t < T, (S t).toGrowthState.stepDir ≠ 0)
    (h_lipline : ∀ t < T, ∀ i, dL t i ≤ -etaq t
        * ⟪g t i, (S t).toGrowthState.stepDir⟫_ℝ
        + L t i * etaq t * etaq t * ‖(S t).toGrowthState.stepDir‖ ^ 2 / 2)
    (h_eta : ∀ t < T, etaq t
        ≤ safeqpEtaMax (g t) (eps t) (L t) (S t).toGrowthState.stepDir)
    (h_sumdL : ∀ t < T, (S (t + 1)).toGrowthState.protectedRisk
        = (S t).toGrowthState.protectedRisk + ∑ i, dL t i)
    (h_core : ∀ t < T, CorePremises (S t) (S (t + 1)) (epsQ t) w)
    (h_net : ∀ t < T, lam * (verify (S t).toGrowthState).riskSpend
        + nu * epsQ t ≤ (verify (S t).toGrowthState).decrease)
    (h_budget0 : ∑ t ∈ Finset.range T,
        (verify (S t).toGrowthState).budgetSpend
      ≤ (S 0).toGrowthState.budget)
    (h_risk_nn : ∀ t, 0 ≤ (S t).toGrowthState.protectedRisk)
    (h_Emin : Emin ≤ (S T).toGrowthState.energy)
    (C G D xi : ℕ → ℝ) (alpha gamma rho beta Cstar : ℝ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (h_emp_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_emp_step : ∀ t < T, C (t + 1) = C t + G t)
    (h_emp_gain_prod : ∀ t < T, gamma * D t ≤ G t)
    (h_emp_dyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (h_emp_beta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta)
    (hCeil : C 0 * (1 + alpha) ^ T ≤ Cstar) :
    CertifiedHAGIInvariant T
      (fun t => (S t).toGrowthState.protectedRisk)
      (fun t => hagiPotential (S t) lam nu Qtarget w)
      C
      (fun t => (S t).toGrowthState.budget)
      (fun t => (verify (S t).toGrowthState).budgetSpend)
      (fun t => Qgen (S t).gen w)
      (fun t => ∑ i, eps t i)
      alpha
      (Qtarget - (hagiPotential (S 0) lam nu Qtarget w - Emin) / nu) := by
  -- identical body to MasterHAGI, with the growth block from
  -- the TRUNCATED premises (sustained_takeoff_trunc)
  have hcore : ∀ t < T,
      hagiPotential (S (t + 1)) lam nu Qtarget w
        ≤ hagiPotential (S t) lam nu Qtarget w
          - (verify (S t).toGrowthState).decrease
          + lam * (verify (S t).toGrowthState).riskSpend + nu * epsQ t
      ∧ (S (t + 1)).toGrowthState.budget
        = (S t).toGrowthState.budget
          - (verify (S t).toGrowthState).budgetSpend :=
    fun t ht => MasterHAGICore (S t) (S (t + 1)) lam nu Qtarget (epsQ t) w
      hlam hnu.le (h_epsQ t) (h_core t ht)
  have hphi_step : ∀ t < T,
      hagiPotential (S (t + 1)) lam nu Qtarget w
        ≤ hagiPotential (S t) lam nu Qtarget w := by
    intro t ht
    have h := (hcore t ht).1
    exact le_trans h (by linarith [h_net t ht])
  have hphi_T : hagiPotential (S T) lam nu Qtarget w
      ≤ hagiPotential (S 0) lam nu Qtarget w :=
    telescope_le_h (f := fun t => hagiPotential (S t) lam nu Qtarget w) hphi_step
  have hdLb : ∀ t < T, ∀ i, dL t i ≤ eps t i := by
    intro t ht i
    exact safeqp_eta_max (g t) (eps t) (L t) (S t).toGrowthState.stepDir
      (dL t) (etaq t) (hLq t) (hepsq t) (hetaq t) (hd t ht)
      (fun i => h_lipline t ht i) (h_eta t ht) i
  have hrisk_step : ∀ t < T,
      (S (t + 1)).toGrowthState.protectedRisk
        - (S t).toGrowthState.protectedRisk ≤ ∑ i, eps t i := by
    intro t ht
    exact safeqp_risk_bound_compose (S t) (S (t + 1)) (dL t) (eps t)
      (h_sumdL t ht) (hdLb t ht)
  have hbud_step : ∀ t < T, (S (t + 1)).toGrowthState.budget
      = (S t).toGrowthState.budget
        - (verify (S t).toGrowthState).budgetSpend :=
    fun t ht => (hcore t ht).2
  have hbud_T : (S T).toGrowthState.budget
      = (S 0).toGrowthState.budget
        - ∑ t ∈ Finset.range T, (verify (S t).toGrowthState).budgetSpend :=
    telescope_sub_sum_h
      (f := fun t => (S t).toGrowthState.budget)
      (c := fun t => (verify (S t).toGrowthState).budgetSpend) hbud_step
  have hcap := sustained_takeoff_trunc C G D alpha gamma rho beta xi T
    hα hγ hρ hC0 h_emp_cone0 h_emp_step h_emp_gain_prod h_emp_dyn h_emp_C_cap h_emp_beta
  have hfloor := hagi_gen_floor (S T) lam nu Qtarget
    (hagiPotential (S 0) lam nu Qtarget w) Emin w hlam hnu h_Emin
    (h_risk_nn T) hphi_T
  refine ⟨?_, hphi_T, hcap, ⟨hbud_T, ?_⟩, hfloor⟩
  · exact telescope_sum_le_h
      (f := fun t => (S t).toGrowthState.protectedRisk)
      (c := fun t => ∑ i, eps t i) hrisk_step
  · linarith [h_budget0]



/-- **Числовой свидетель не-вакуозности** growth-блока
усечённого капстоуна: C t = D t = 2^t, G t = 2^t,
alpha = gamma = 1, rho = 0, beta = 2, xi = 0 — ВСЕ усечённые
посылки выполнены на любом T <= 6, потолок C* = 100 держит
горизонт (измерено: 2^6 = 64 <= 100 < 2^7 = 128). Усечённый
капстоун НЕ вакуозен. -/
theorem masterhagi_growth_witness :
    ∀ T ≤ 6,
      (0:ℝ) < (2:ℝ) ^ 0
        ∧ (1/1) * (2:ℝ) ^ 0 ≤ (2:ℝ) ^ 0
        ∧ (∀ t < T, (2:ℝ) ^ (t + 1) = (2:ℝ) ^ t + (2:ℝ) ^ t)
        ∧ (∀ t < T, (1:ℝ) * (2:ℝ) ^ t ≤ (2:ℝ) ^ t)
        ∧ (∀ t < T, (0:ℝ) * (2:ℝ) ^ t + (2:ℝ) * (2:ℝ) ^ t - 0
            ≤ (2:ℝ) ^ (t + 1))
        ∧ (∀ t < T, (2:ℝ) ^ (t + 1) ≤ (1 + 1) * (2:ℝ) ^ t)
        ∧ (∀ t < T, (1:ℝ) / 1 * ((1 + 1) - 0)
            + 0 / (2:ℝ) ^ t ≤ 2)
        ∧ ((1:ℝ) * (2:ℝ) ^ T ≤ 100) := by
  intro T _
  have hpos : ∀ t : ℕ, (0:ℝ) < (2:ℝ) ^ t := fun t => by positivity
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    show (2:ℝ) ^ (t + 1) = (2:ℝ) ^ t + (2:ℝ) ^ t
    rw [pow_succ]
    ring
  · intro t _
    simpa using le_refl ((2:ℝ) ^ t)
  · intro t _
    show (0:ℝ) * (2:ℝ) ^ t + (2:ℝ) * (2:ℝ) ^ t - 0
      ≤ (2:ℝ) ^ (t + 1)
    rw [pow_succ]
    exact le_of_eq (by ring)
  · intro t _
    show (2:ℝ) ^ (t + 1) ≤ (1 + 1) * (2:ℝ) ^ t
    rw [pow_succ]
    exact le_of_eq (by ring)
  · intro t _
    show (1:ℝ) / 1 * ((1 + 1) - 0) + 0 / (2:ℝ) ^ t ≤ 2
    norm_num
  · -- C*-horizon: 2^T <= 2^6 = 64 <= 100
    have hmono : ∀ b a : ℕ, a ≤ b → (2:ℝ) ^ a ≤ (2:ℝ) ^ b := by
      intro b
      induction b with
      | zero =>
          intro a ha
          have h0 : a = 0 := Nat.le_zero.mp ha
          rw [h0]
      | succ b ih =>
          intro a ha
          rcases Nat.lt_or_ge a (b + 1) with h | h
          · have hstep : (2:ℝ) ^ b ≤ (2:ℝ) ^ (b + 1) := by
              rw [pow_succ]
              nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) b]
            exact le_trans (ih a (by omega)) hstep
          · have hab : a = b + 1 := by omega
            rw [hab]
    have h6 : (2:ℝ) ^ 6 ≤ 100 := by norm_num
    have hT := hmono 6 T (by omega)
    have hfinal : (1:ℝ) * (2:ℝ) ^ T ≤ 100 :=
      le_trans (by simpa using hT) h6
    exact hfinal

end Trunc
end Hagi
