import Hagi.Unified.LoopInstances

/-!
# Сквозной свидетель CertifiedLoop на горизонтах

Полушаговая траектория квадратичной машины: каждый шаг —
середина к цели, энергия геометрически убывает, каждый шаг
продуктивен. Капстоун `certified_loop_strict` применяется к
реальной многошаговой траектории: строгий спуск на любом
горизонте, специализации для малых горизонтов.
-/

namespace Hagi.Examples

open Hagi.Unified.CertifiedLoop Hagi.Unified.LinkedQVec
open Hagi.Unified.HonestTransition Hagi.Unified.DescentCoreQuad
open Hagi.Unified.LoopInstances

variable {k : Type*} [Fintype k]

/-- Траектория полушагов: каждый шаг — середина между
текущей точкой и целью. -/
noncomputable def qhalf (a x : k → ℝ) : ℕ → (k → ℝ) :=
  fun t => Nat.rec x (fun _ w i => (w i + a i) / 2) t

theorem qhalf_succ (a x : k → ℝ) (t : ℕ) :
    qhalf a x (t + 1) = fun i => (qhalf a x t i + a i) / 2 := rfl

/-- Энергия после полушага — четверть энергии до него. -/
theorem quadE_half (a w : k → ℝ) :
    quadE a (fun i => (w i + a i) / 2) = (1 : ℝ) / 4 * quadE a w := by
  have hexp : ∀ i, (((w i + a i) / 2) - a i)^2
      = (1 : ℝ) / 4 * (w i - a i)^2 := by
    intro i
    field_simp
    ring
  unfold quadE
  rw [Finset.sum_congr rfl (fun i _ => hexp i), ← Finset.mul_sum]
  linarith

/-- Энергия вдоль полушаговой траектории убывает
геометрически. -/
theorem quadE_qhalf (a x : k → ℝ) (t : ℕ) :
    quadE a (qhalf a x t) = (1 : ℝ) / 4 ^ t * quadE a x := by
  induction t with
  | zero => rw [show qhalf a x 0 = x from rfl]; norm_num
  | succ t ih =>
    rw [qhalf_succ, quadE_half, ih]
    field_simp
    ring

theorem quadE_pos_of_grad (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    0 < quadE a x := by
  by_contra h0
  push_neg at h0
  apply hx
  funext i
  have hnn : (0:ℝ) ≤ ∑ j, (x j - a j)^2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : (x i - a i)^2 ≤ ∑ j, (x j - a j)^2 :=
    Finset.single_le_sum (f := fun j => (x j - a j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  unfold quadE at h0
  have hz : ∑ j, (x j - a j)^2 = 0 := by
    have hd : ((∑ j, (x j - a j)^2) : ℝ) / 2 ≤ 0 := h0
    have hdub : (∑ j, (x j - a j)^2) = 2 * ((∑ j, (x j - a j)^2) / 2) := by
      ring
    have hs : (0:ℝ) < 2 := by norm_num
    nlinarith
  have hsq : (0:ℝ) ≤ (x i - a i)^2 := sq_nonneg _
  have hi : (x i - a i)^2 = 0 := by linarith
  have hxi : x i - a i = 0 := by
    exact pow_eq_zero_iff (by norm_num) |>.mp hi
  unfold quadGrad
  simpa using hxi

/-- Градиент вдоль полушаговой траектории не зануляется,
если не нулевой в старте. -/
theorem qhalf_grad_ne (a x : k → ℝ) (hx : quadGrad a x ≠ 0)
    (t : ℕ) : quadGrad a (qhalf a x t) ≠ 0 := by
  intro h0
  apply hx
  have hE : quadE a (qhalf a x t) = 0 := by
    unfold quadE
    have hfun : ∀ i, (qhalf a x t i - a i)^2 = 0 := by
      intro i
      have hi := congrFun h0 i
      unfold quadGrad at hi
      have : qhalf a x t i - a i = 0 := by simpa using hi
      rw [this]; norm_num
    rw [Finset.sum_congr rfl (fun i _ => hfun i)]
    norm_num
  have hpos := quadE_pos_of_grad a x hx
  rw [quadE_qhalf] at hE
  have hq : (0:ℝ) < (1:ℝ) / 4 ^ t := by positivity
  nlinarith

/-- Монотонность энергии вдоль полушаговой траектории. -/
theorem quadE_qhalf_le (a x : k → ℝ) (t : ℕ) :
    quadE a (qhalf a x t) ≤ quadE a x := by
  have hnn : (0:ℝ) ≤ quadE a x := quadE_nonneg a x
  induction t with
  | zero => rw [show qhalf a x 0 = x from rfl]
  | succ t ih =>
    rw [qhalf_succ, quadE_half]
    have ht := quadE_nonneg a (qhalf a x t)
    nlinarith

/-- Сертификат продуктивного полушага: честный спуск на
три четверти текущей энергии. -/
noncomputable def halfStepCert (a x : k → ℝ) (hx : quadGrad a x ≠ 0)
    (t : ℕ) :
    StepCert (fun w => quadE a w) (quadMeasured a) (quadFloor a x) 0
      (qhalf a x t) (qhalf a x (t + 1)) 0 0 where
  riskSpend := 0
  budgetSpend := 0
  trans := ⟨(3 : ℝ) / 4 * quadE a (qhalf a x t),
    mul_pos (by norm_num)
      (quadE_pos_of_grad a (qhalf a x t) (qhalf_grad_ne a x hx t)),
    by
      rw [qhalf_succ]
      have hstep : quadE a (fun i => (qhalf a x t i + a i) / 2)
          = (1 : ℝ) / 4 * quadE a (qhalf a x t) :=
        quadE_half a (qhalf a x t)
      rw [hstep]
      ring_nf
      linarith,
    le_refl 0, le_refl 0⟩
  hriskSpend_nn := le_refl 0
  hbudgetSpend_nn := le_refl 0
  hdec := by norm_num
  quality := by
    intro i
    have hE : quadE a (qhalf a x (t + 1))
        = (1 : ℝ) / 4 * quadE a (qhalf a x t) := by
      rw [qhalf_succ, quadE_half]
    have hpos := quadE_pos_of_grad a x hx
    have hnn : (0:ℝ) ≤ quadE a (qhalf a x t) := by
      rw [quadE_qhalf]
      exact mul_nonneg (by positivity) (le_of_lt hpos)
    simp only [quadMeasured]
    show 1 / (2 * (1 + quadE a x))
      ≤ 1 / (1 + quadE a (qhalf a x (t + 1)))
    have h1 : (0:ℝ) < 1 + quadE a x := by linarith
    have h2 : (0:ℝ) < 2 * (1 + quadE a x) := by linarith
    have h3 : (0:ℝ) < 1 + quadE a (qhalf a x (t + 1)) := by
      rw [hE]; linarith
    rw [div_le_div_iff₀ h2 h3]
    have hle := quadE_qhalf_le a x (t + 1)
    linarith

/-- Свидетель: сертифицированная полушаговая траектория
строго убывает на любом положительном горизонте. -/
theorem quad_loop_horizon (a x : k → ℝ) (hx : quadGrad a x ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    quadE a (qhalf a x n) < quadE a (qhalf a x 0) := by
  have h₀ : FloorKept (quadMeasured a) (qhalf a x 0)
      (quadFloor a x) := by
    intro i
    have hpos := quadE_pos_of_grad a x hx
    simp only [quadMeasured, quadFloor]
    show 1 / (2 * (1 + quadE a x)) ≤ 1 / (1 + quadE a x)
    have h1 : (0:ℝ) < 1 + quadE a x := by linarith
    have h2 : (0:ℝ) < 2 * (1 + quadE a x) := by linarith
    rw [div_le_div_iff₀ h2 h1]
    linarith
  have main := certified_loop_strict
    (fun w => quadE a w) (quadMeasured a) (quadFloor a x) 0
    (qhalf a x) (fun _ => 0)
    (fun t => (3 : ℝ) / 4 * quadE a (qhalf a x t)) n
    h₀ (le_refl 0)
    (fun t => halfStepCert a x hx t.val)
    (fun t => rfl)
    hn
  exact main.1

/-- Специализация свидетеля на малом горизонте. -/
theorem quad_witness_T3 (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    quadE a (qhalf a x 3) < quadE a (qhalf a x 0) :=
  quad_loop_horizon a x hx 3 (by norm_num)

/-- Специализация свидетеля на длинном горизонте. -/
theorem quad_witness_T10 (a x : k → ℝ) (hx : quadGrad a x ≠ 0) :
    quadE a (qhalf a x 10) < quadE a (qhalf a x 0) :=
  quad_loop_horizon a x hx 10 (by norm_num)

end Hagi.Examples
