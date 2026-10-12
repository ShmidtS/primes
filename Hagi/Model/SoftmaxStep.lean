/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
import Hagi.Foundations.StageCalculus
set_option linter.style.header false

/-!
# SoftmaxStep — learning-step мини-модели

Модель: одно-параметрическая softmax-голова на одном примере
(2 класса), `logitCE w = log (1 + exp (-w))`, градиентный шаг
`w' = w + η / (1 + e^w)`.

* `logitCE_deriv` — `logitCE' w = -1 / (1 + e^w)`.
* `logitGrad_deriv` — производная градиента равна
  `e^w / (1 + e^w)²`.
* `sigmoid_sq_le_quarter` — `e^w / (1 + e^w)² ≤ 1/4`.
* `grad_lipschitz` — градиент 1/4-липшицев.
* `logitCE_descent_lemma` — одномерная descent lemma.
* `descent_step` — при `0 < η ≤ 2` шаг гарантирует
  `logitCE w' ≤ logitCE w - (η/2) * (1/(1+e^w))²`.
* `descent_example` — числовой пример `w = 0`, `η = 2`.

Модель одномерная (один пример, один параметр);
мультипараметрический/стохастический случай не покрывается.
-/

open Real Set

namespace Hagi.Model

/-- CE одно-параметрической softmax-головы (margin w). -/
noncomputable def logitCE (w : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-w))

/-- Градиент логит-головы (функция шага). -/
noncomputable def logitGrad (w : ℝ) : ℝ :=
  -1 / (1 + Real.exp w)

/-- Производная logitCE: −1/(1+e^w) (chain rule). -/
theorem logitCE_deriv (w : ℝ) :
    HasDerivAt logitCE (-1 / (1 + Real.exp w)) w := by
  have hpos : (0:ℝ) < 1 + Real.exp (-w) := by positivity
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) w := by
    have h0 := (hasDerivAt_id w).neg
    rw [show (-id : ℝ → ℝ) = fun t => -t from rfl] at h0
    exact h0
  have he : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-w)) w := by
    have hc := (Real.hasDerivAt_exp (-w)).comp w hneg
    rw [show (Real.exp ∘ (fun t : ℝ => -t))
        = fun t => Real.exp (-t) from rfl] at hc
    rw [show Real.exp (-w) * (-1) = -Real.exp (-w) from by ring] at hc
    exact hc
  have h1 : HasDerivAt (fun t => 1 + Real.exp (-t)) (-Real.exp (-w)) w := by
    have h := (hasDerivAt_const w (1:ℝ)).add he
    rw [show ((fun _ : ℝ => (1:ℝ)) + (fun t => Real.exp (-t)))
        = fun t => 1 + Real.exp (-t) from rfl] at h
    rw [show (0:ℝ) + (-Real.exp (-w)) = -Real.exp (-w) from by ring] at h
    exact h
  have h2 : HasDerivAt (fun t => Real.log (1 + Real.exp (-t)))
      ((1 + Real.exp (-w))⁻¹ * (-Real.exp (-w))) w := by
    have hc := (Real.hasDerivAt_log
      (ne_of_gt hpos : (1 + Real.exp (-w)) ≠ 0)).comp w h1
    rw [show (Real.log ∘ (fun t => 1 + Real.exp (-t)))
        = fun t => Real.log (1 + Real.exp (-t)) from rfl] at hc
    exact hc
  have key : (1 + Real.exp (-w))⁻¹ * (-Real.exp (-w))
      = -1 / (1 + Real.exp w) := by
    have hE : Real.exp (-w) * Real.exp w = 1 := by
      rw [← Real.exp_add]
      simp
    field_simp
    linarith
  unfold logitCE at h2 ⊢
  rw [key] at h2
  exact h2

/-- Производная градиента: e^w/(1+e^w)² (кривизна CE). -/
theorem logitGrad_deriv (w : ℝ) :
    HasDerivAt logitGrad (Real.exp w / (1 + Real.exp w)^2) w := by
  have hpos : (0:ℝ) < 1 + Real.exp w := by positivity
  have hne : (1 + Real.exp w) ≠ 0 := ne_of_gt hpos
  have hexp : HasDerivAt (fun t => Real.exp t) (Real.exp w) w :=
    Real.hasDerivAt_exp w
  have h1 : HasDerivAt (fun t => 1 + Real.exp t) (Real.exp w) w := by
    have h := (hasDerivAt_const w (1:ℝ)).add hexp
    rw [show ((fun _ : ℝ => (1:ℝ)) + (fun t => Real.exp t))
        = fun t => 1 + Real.exp t from rfl] at h
    rw [show (0:ℝ) + Real.exp w = Real.exp w from by ring] at h
    exact h
  have hinv : HasDerivAt (fun t => (1 + Real.exp t)⁻¹)
      (-Real.exp w / (1 + Real.exp w)^2) w := by
    have hc := (hasDerivAt_inv hne).comp w h1
    rw [show (fun x => x⁻¹) ∘ (fun t => 1 + Real.exp t)
        = fun t => (1 + Real.exp t)⁻¹ from rfl] at hc
    rw [show -((1 + Real.exp w)^2)⁻¹ * Real.exp w
        = -Real.exp w / (1 + Real.exp w)^2 from by
        field_simp] at hc
    exact hc
  have hfin := hinv.neg
  rw [show -(fun t => (1 + Real.exp t)⁻¹)
      = fun t => -((1 + Real.exp t)⁻¹) from rfl] at hfin
  rw [show -(-Real.exp w / (1 + Real.exp w)^2)
      = Real.exp w / (1 + Real.exp w)^2 from by
      field_simp] at hfin
  rw [show (fun t => -((1 + Real.exp t)⁻¹)) = logitGrad from by
      funext t
      unfold logitGrad
      field_simp] at hfin
  exact hfin

/-- Кривизна CE ограничена 1/4 (ядро: 0 <= (1-e^w)^2). -/
theorem sigmoid_sq_le_quarter (w : ℝ) :
    Real.exp w / (1 + Real.exp w)^2 ≤ 1/4 := by
  have hkey : 4 * Real.exp w ≤ (1 + Real.exp w)^2 := by
    nlinarith [sq_nonneg (1 - Real.exp w)]
  field_simp
  linarith

/-- **Градиент логит-головы 1/4-липшицев** (MVT на градиенте,
кривизна ≤ 1/4): одномерная константа гладкости L = 1/4. -/
theorem grad_lipschitz (a b : ℝ) :
    |logitGrad b - logitGrad a| ≤ (1/4) * |b - a| := by
  rcases lt_trichotomy a b with h | h | h
  · have hcont : ContinuousOn logitGrad (Icc a b) :=
      fun x _ => (logitGrad_deriv x).continuousAt.continuousWithinAt
    obtain ⟨c, _, hslope⟩ :=
      exists_hasDerivAt_eq_slope logitGrad
        (fun w => Real.exp w / (1 + Real.exp w)^2)
        h hcont (fun x _ => logitGrad_deriv x)
    have hq := sigmoid_sq_le_quarter c
    have hd : (0:ℝ) < b - a := by linarith
    have hs : logitGrad b - logitGrad a
        = (Real.exp c / (1 + Real.exp c)^2) * (b - a) := by
      have := (eq_div_iff hd.ne').mp hslope
      linarith
    have hq0 : (0:ℝ) < Real.exp c / (1 + Real.exp c)^2 := by
      positivity
    have hcpos : (0:ℝ) ≤ logitGrad b - logitGrad a :=
      by nlinarith [hs, hq0, hd]
    rw [abs_of_nonneg hcpos, abs_of_pos hd, hs]
    nlinarith [hq, Real.exp_pos c]
  · rw [h]
    simp
  · rw [abs_sub_comm (logitGrad b) (logitGrad a)]
    have hcont : ContinuousOn logitGrad (Icc b a) :=
      fun x _ => (logitGrad_deriv x).continuousAt.continuousWithinAt
    obtain ⟨c, _, hslope⟩ :=
      exists_hasDerivAt_eq_slope logitGrad
        (fun w => Real.exp w / (1 + Real.exp w)^2)
        h hcont (fun x _ => logitGrad_deriv x)
    have hq := sigmoid_sq_le_quarter c
    have hd : (0:ℝ) < a - b := by linarith
    have hs : logitGrad a - logitGrad b
        = (Real.exp c / (1 + Real.exp c)^2) * (a - b) := by
      have := (eq_div_iff hd.ne').mp hslope
      linarith
    have hq0 : (0:ℝ) < Real.exp c / (1 + Real.exp c)^2 := by
      positivity
    have hcpos : (0:ℝ) ≤ logitGrad a - logitGrad b :=
      by nlinarith [hs, hq0, hd]
    rw [abs_of_nonneg hcpos, abs_sub_comm b a, abs_of_pos hd, hs]
    nlinarith [hq, Real.exp_pos c]

/-- Одномерная descent lemma: для любых `x y`,
`logitCE y ≤ logitCE x + logitGrad x * (y - x) +
(1/4) * (y - x) ^ 2` (MVT + `grad_lipschitz`). -/
theorem logitCE_descent_lemma (x y : ℝ) :
    logitCE y ≤ logitCE x + logitGrad x * (y - x)
      + (1/4) * (y - x)^2 := by
  rcases lt_trichotomy x y with h | h | h
  · have hcont : ContinuousOn logitCE (Icc x y) :=
      fun w _ => (logitCE_deriv w).continuousAt.continuousWithinAt
    obtain ⟨c, hcmem, hslope⟩ :=
      exists_hasDerivAt_eq_slope logitCE logitGrad
        h hcont (fun w _ => logitCE_deriv w)
    have hd : (0:ℝ) < y - x := by linarith
    have hcx : (0:ℝ) ≤ c - x := by
      have := hcmem.1
      linarith
    have hcy : c - x ≤ y - x := by
      have := hcmem.2
      linarith
    have hlip := grad_lipschitz c x
    rw [abs_sub_comm (logitGrad x) (logitGrad c),
      abs_sub_comm x c, abs_of_nonneg hcx] at hlip
    have hgc : logitGrad c ≤ logitGrad x + (1/4) * (y - x) := by
      have h2 : logitGrad c - logitGrad x ≤ (1/4) * (y - x) :=
        le_trans (abs_le.mp hlip).2 (by linarith [hcy])
      linarith
    have hs : logitCE y - logitCE x
        = logitGrad c * (y - x) := by
      have := (eq_div_iff hd.ne').mp hslope
      linarith
    calc logitCE y ≤ logitCE x
          + (logitGrad x + (1/4) * (y - x)) * (y - x) := by
            nlinarith [hs, hgc, hd]
      _ = logitCE x + logitGrad x * (y - x)
          + (1/4) * (y - x)^2 := by ring
  · rw [h]
    nlinarith [sq_nonneg (logitGrad x)]
  · -- y < x: симметричный MVT на [y, x]
    have hcont : ContinuousOn logitCE (Icc y x) :=
      fun w _ => (logitCE_deriv w).continuousAt.continuousWithinAt
    obtain ⟨c, hcmem, hslope⟩ :=
      exists_hasDerivAt_eq_slope logitCE logitGrad
        h hcont (fun w _ => logitCE_deriv w)
    have hd : (0:ℝ) < x - y := by linarith
    have hyx : (0:ℝ) ≤ x - c := by
      have := hcmem.2
      linarith
    have hle : x - c ≤ x - y := by
      have := hcmem.1
      linarith
    have hlip := grad_lipschitz c x
    rw [abs_sub_comm (logitGrad x) (logitGrad c),
      abs_of_nonneg (by nlinarith : (0:ℝ) ≤ x - c)] at hlip
    have hgc : logitGrad x - (1/4) * (x - y) ≤ logitGrad c := by
      have h2 : -(logitGrad c - logitGrad x) ≤ (1/4) * (x - y) := by
        have hA := (abs_le.mp hlip).1
        have hB := (abs_le.mp hlip).2
        linarith
      linarith
    have hs : logitCE y - logitCE x
        = logitGrad c * (y - x) := by
      have hkey : logitGrad c * (x - y) = logitCE x - logitCE y := by
        rw [hslope]
        field_simp
      have hconv : logitGrad c * (y - x)
          = -(logitGrad c * (x - y)) := by ring
      rw [hconv]
      linarith [hkey]
    have hyx2 : (y - x) * (y - x) = (x - y) * (x - y) := by ring
    calc logitCE y ≤ logitCE x
          + (logitGrad x - (1/4) * (x - y)) * (y - x) := by
            nlinarith [hs, hgc, hd]
      _ = logitCE x + logitGrad x * (y - x)
          + (1/4) * (y - x)^2 := by ring

/-- Гарантированный спуск: при `0 < eta ≤ 2` шаг
`w' = w + eta / (1 + e^w)` даёт
`logitCE w' ≤ logitCE w - (eta/2) * (1 / (1 + e^w)) ^ 2`. -/
theorem descent_step (w eta : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 2) :
    logitCE (w + eta / (1 + Real.exp w))
      ≤ logitCE w - (eta/2) * (1 / (1 + Real.exp w))^2 := by
  have hgval : logitGrad w = -1 / (1 + Real.exp w) := rfl
  have hstep : (w + eta / (1 + Real.exp w)) - w
      = eta / (1 + Real.exp w) := by ring
  have hlem := logitCE_descent_lemma w (w + eta / (1 + Real.exp w))
  rw [hgval] at hlem
  -- подстановка шага в лемму
  have hq : (0:ℝ) < 1 + Real.exp w := by positivity
  have hq2 : (0:ℝ) < (1/(1 + Real.exp w))^2 := by positivity
  -- hlem: CE y <= CE w + (-1/(1+e^w))*(eta/(1+e^w)) + (1/4)*(eta/(1+e^w))^2
  rw [hstep] at hlem
  -- арифметика: -eta*q^2 + (1/4)eta^2*q^2 <= -(eta/2)q^2 при eta <= 2
  have hsq : (eta / (1 + Real.exp w))^2
      = eta^2 * (1/(1 + Real.exp w))^2 := by
    rw [div_pow]
    field_simp
  have hcross : (-1/(1 + Real.exp w)) * (eta / (1 + Real.exp w))
      = -eta * (1/(1 + Real.exp w))^2 := by
    field_simp
  rw [hcross, hsq] at hlem
  have hprod : (0:ℝ)
      ≤ eta^2 * (1/(1 + Real.exp w))^2 := by positivity
  nlinarith [hlem, heta, heta2, hq2, hprod, sq_nonneg eta]

/-- Числовой пример: при `w = 0`, `eta = 2`,
`logitCE (0 + 2 / (1 + e^0)) ≤ logitCE 0 - 1/4`. -/
theorem descent_example :
    logitCE (0 + 2 / (1 + Real.exp 0))
      ≤ logitCE 0 - (2/2) * (1 / (1 + Real.exp 0))^2 :=
  descent_step 0 2 (by norm_num) (by norm_num)

/-! ## Bridge: explicit model -> certified joint stage (R350)

The `h_emp_smooth` premise of `Foundations.joint_stage` is
DERIVED (not assumed) for the explicit logit-CE model:
`logitCE_descent_lemma` is exactly the L-smoothness form
with `L = 1/2` (coefficient 1/4 = L/2). Instantiating
`joint_stage` with this derived smoothness yields the
certified descent stage for the real model — the first
closed bridge from an explicit model to the stage
calculus. -/

set_option maxHeartbeats 1000000 in
/-- Certified joint stage for the explicit logit-CE model
(R350). Here `d` is a descent DIRECTION (along `-grad`), so
the certified-descent premise reads `d^2 ≤ (-logitGrad w)*d`
(automatic for `d = t·q` with `0 ≤ t ≤ 1`, `q = -grad ≥ 0`).
The smoothness premise of `joint_stage` is DERIVED from
`logitCE_descent_lemma` (which is exactly L-smoothness with
`L = 1/2`), giving `logitCE (w + eta*d) ≤ logitCE w -
eta*d^2/2` — the first h_emp_smooth premise closed by an
explicit model. -/
theorem joint_stage_logitCE (w eta d : ℝ)
    (heta : 0 < eta) (heta2 : eta ≤ 2)
    (hdescent : d ^ 2 ≤ (-logitGrad w) * d) :
    logitCE (w + eta * d) ≤ logitCE w - eta * d ^ 2 / 2 := by
  have hsmooth : logitCE (w + eta * d) ≤ logitCE w
      - eta * ((-logitGrad w) * d) + (1/2) * eta ^ 2 * d ^ 2 / 2 := by
    have hlem := logitCE_descent_lemma w (w + eta * d)
    rw [show (w + eta * d) - w = eta * d from by ring] at hlem
    have hterm : (1/4) * (eta * d) ^ 2 = (1/2) * eta ^ 2 * d ^ 2 / 2 := by
      field_simp
      ring
    rw [hterm] at hlem
    have hsign : logitGrad w * (eta * d)
        = eta * (logitGrad w * d) := by ring
    rw [hsign] at hlem
    linarith
  have heta' : eta ≤ 1 / (1/2) := by
    norm_num
    linarith
  exact Hagi.Foundations.joint_stage (1/2) eta d
    ((-logitGrad w) * d) (logitCE (w + eta * d)) (logitCE w)
    (by norm_num) heta' heta.le hdescent hsmooth

/-!
## Trajectory bound for the explicit model (R354)

Iterating the derived certified stage (`joint_stage_logitCE`)
telescopes over the whole training trajectory: after T
certified steps the logit-CE is at most its initial value
minus the summed per-step certified decreases. Every premise
here is either a definition of the trajectory or the
DERIVED-per-step stage condition — no `h_emp_*` premises.
-/

/-- Telescoped certified-descent bound for the explicit
logit-CE model: if each step `w t → w t + eta t * d t`
satisfies `0 < eta t ≤ 2` and the certified-descent
direction condition `d t ^ 2 ≤ (-logitGrad (w t)) * d t`,
then

  logitCE (w T) ≤ logitCE (w 0) − ∑ t < T, eta t * d t ^ 2 / 2.

This is the concrete-model instance of the loop-level
telescope (`stage_certificate_telescope`) with the
smoothness premise DERIVED (`joint_stage_logitCE`) instead
of assumed. -/
theorem logitCE_trajectory_bound (T : ℕ) (w eta d : ℕ → ℝ)
    (hstep : ∀ t < T, w (t + 1) = w t + eta t * d t)
    (heta : ∀ t < T, 0 < eta t ∧ eta t ≤ 2)
    (hdir : ∀ t < T, d t ^ 2 ≤ (-logitGrad (w t)) * d t) :
    logitCE (w T) ≤ logitCE (w 0)
      - ∑ t ∈ Finset.range T, eta t * d t ^ 2 / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hstepT : ∀ t < T, w (t + 1) = w t + eta t * d t :=
        fun t ht => hstep t (Nat.lt_succ_of_lt ht)
      have hetaT : ∀ t < T, 0 < eta t ∧ eta t ≤ 2 :=
        fun t ht => heta t (Nat.lt_succ_of_lt ht)
      have hdirT : ∀ t < T, d t ^ 2 ≤ (-logitGrad (w t)) * d t :=
        fun t ht => hdir t (Nat.lt_succ_of_lt ht)
      have hih := ih hstepT hetaT hdirT
      have hsucc := joint_stage_logitCE (w T) (eta T) (d T)
        (heta T (Nat.le_refl _)).1 (heta T (Nat.le_refl _)).2
        (hdir T (Nat.le_refl _))
      rw [hstep T (Nat.le_refl _)]
      have hsum : ∑ t ∈ Finset.range (T + 1), eta t * d t ^ 2 / 2
          = ∑ t ∈ Finset.range T, eta t * d t ^ 2 / 2
            + eta T * d T ^ 2 / 2 := by
        rw [Finset.sum_range_succ]
      rw [hsum]
      linarith

/-- The explicit-model CE is nonnegative: log(1+e^{-w}) ≥ 0
(the argument is ≥ 1, so the log is ≥ log 1 = 0). -/
theorem logitCE_nonneg (w : ℝ) : 0 ≤ logitCE w := by
  have h1 : (1:ℝ) ≤ 1 + Real.exp (-w) := by
    have := Real.exp_nonneg (-w)
    linarith
  have hpos : (0:ℝ) < 1 + Real.exp (-w) := by linarith
  have hlog : Real.log 1 ≤ Real.log (1 + Real.exp (-w)) :=
    Real.log_le_log (by norm_num) h1
  simp only [logitCE]
  simpa using hlog

/-- Bounded total certified descent (R355): the summed
per-step certified decreases along ANY certified trajectory
never exceed the initial CE — since CE stays nonnegative,
the model cannot descend forever. The explicit-model
instance of the loop-level termination bound. -/
theorem logitCE_total_descent_bounded (T : ℕ) (w eta d : ℕ → ℝ)
    (hstep : ∀ t < T, w (t + 1) = w t + eta t * d t)
    (heta : ∀ t < T, 0 < eta t ∧ eta t ≤ 2)
    (hdir : ∀ t < T, d t ^ 2 ≤ (-logitGrad (w t)) * d t) :
    ∑ t ∈ Finset.range T, eta t * d t ^ 2 / 2 ≤ logitCE (w 0) := by
  have htr := logitCE_trajectory_bound T w eta d hstep heta hdir
  have hnn := logitCE_nonneg (w T)
  linarith

end Hagi.Model

namespace Hagi
export Hagi.Model (logitCE logitGrad logitCE_deriv logitGrad_deriv sigmoid_sq_le_quarter grad_lipschitz logitCE_descent_lemma descent_step descent_example joint_stage_logitCE logitCE_trajectory_bound logitCE_nonneg logitCE_total_descent_bounded)
end Hagi
