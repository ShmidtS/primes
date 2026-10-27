/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.System.GrowthState
import Hagi.Step.ProjectionDescent
import Hagi.Unified.AnytimeMartingale
import Mathlib.Tactic
import Hagi.Foundations.StageCalculus
/-!
# the quantization-to-energy bridge (audit bridge #4)

The round-67 audit found the missing edge: MacroCycle's
compress stage assumed an abstract dnorm ≤ 1/2 without
grounding in the real ternary pipeline. This module chains:

  pointwise ternary residue (tern_distortion_round, s/2)
  → Euclidean residual norm (quant_residual_norm: √n·s/2)
  → energy cost (quant_energy_bridge: ΔE ≤ κ·√n·s/2 under
    the h_emp_ Lipschitz constant of the energy in the
    weight norm)

MacroCycle's compress hypothesis is now architecture-level.
-/

open Finset Real

namespace Hagi.Energy

/-- **The ternary residual norm bound** (audit bridge #4,
step 1): if every weight's ternary rounding residue is at
most s/2 in absolute value (tern_distortion_round scaled to
the grid step s), the Euclidean residual norm over n weights
is at most sqrt(n)·s/2. -/
theorem quant_residual_norm {n : ℕ} (w q : Fin n → ℝ) (s : ℝ)
    (hres : ∀ i, |w i - q i| ≤ s / 2) :
    (∑ i, (w i - q i) ^ 2) ≤ n * (s / 2) ^ 2 := by
  have hsq : ∀ i : Fin n, (w i - q i) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    have hle := hres i
    rw [abs_le] at hle
    have h1 : (w i - q i) ^ 2 ≤ (s / 2) ^ 2 := by
      nlinarith [hle.1, hle.2]
    exact h1
  calc (∑ i, (w i - q i) ^ 2) ≤ ∑ i : Fin n, (s / 2) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hsq i)
    _ = n * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp

/-- **The quantization→energy bridge** (audit bridge #4,
step 2 — the missing edge of MacroCycle's compress stage):
with the energy κ-Lipschitz in the weight Euclidean norm
(h_emp_lip — measured curvature), the ternary compression of
n weights at grid step s costs at most
ΔE ≤ κ·√n·s/2 — the concrete, architecture-level compression
cost, chaining pointwise rounding (tern_distortion_round) →
residual norm → energy. MacroCycle's abstract Hagi.Foundations.compress_stage
hypothesis is now grounded in the real ternary pipeline. -/
theorem quant_energy_bridge {n : ℕ} (w q : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2)
    (hkappa : 0 ≤ kappa)
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2)) :
    dE ≤ kappa * Real.sqrt (n : ℝ) * s / 2 := by
  have hnorm := quant_residual_norm w q s hres
  have hsq : Real.sqrt (∑ i, (w i - q i) ^ 2) ≤ Real.sqrt ((n : ℝ) * (s / 2) ^ 2) :=
    Real.sqrt_le_sqrt hnorm
  have hsqrt : Real.sqrt ((n : ℝ) * (s / 2) ^ 2) = Real.sqrt (n : ℝ) * |s / 2| := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
    rw [Real.sqrt_sq_eq_abs]
  rw [hsqrt, abs_of_nonneg (by linarith : (0:ℝ) ≤ s / 2)] at hsq
  calc dE ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)) := by
          calc dE ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2) := h_emp_lip
            _ ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)) :=
                mul_le_mul_of_nonneg_left hsq hkappa
    _ = kappa * Real.sqrt (n : ℝ) * s / 2 := by ring


/-- **The quantization→layer-output perturbation** (unified plan
§6.2, step 2): if every weight of an m×n layer is rounded
with componentwise error at most D (e.g. D = Δ/2 for the grid
step Δ), then the output perturbation obeys the
dimension-correct bound

  ‖(Ŵ − W) x‖₂ ≤ D · √(m·n) · ‖x‖₂,

with BOTH d_in and d_out under the root (the plan's audit
correction: the √d_in-only form holds for the componentwise
max-norm of the output, not for the Euclidean norm of the
whole vector). -/
theorem quant_matrix_perturb {m n : ℕ} (W Wq : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hres : ∀ i j, |Wq i j - W i j| ≤ D) :
    ∑ i, ((Wq - W).mulVec x i) ^ 2 ≤ (m * n) * D ^ 2 * (∑ j, x j ^ 2) := by
  set E : Matrix (Fin m) (Fin n) ℝ := Wq - W with hE
  have hmul : ∀ i, (E.mulVec x i) = ∑ j, E i j * x j := by
    intro i
    rfl
  have hsq : ∀ i, (E.mulVec x i) ^ 2 ≤ n * D ^ 2 * (∑ j, x j ^ 2) := by
    intro i
    rw [hmul i]
    have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => E i j) x
    have hEin : (∑ j, E i j ^ 2) ≤ n * D ^ 2 := by
      have hle : ∀ j : Fin n, E i j ^ 2 ≤ D ^ 2 := by
        intro j
        have hr := hres i j
        rw [abs_le] at hr
        have hEij : E i j = Wq i j - W i j := by rw [hE]; rfl
        rw [hEij]
        nlinarith [hr.1, hr.2]
      calc (∑ j, E i j ^ 2) ≤ ∑ j : Fin n, D ^ 2 :=
            Finset.sum_le_sum (fun j _ => hle j)
        _ = n * D ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            simp
    calc (∑ j, E i j * x j) ^ 2 ≤ (∑ j, E i j ^ 2) * (∑ j, x j ^ 2) := hcs
      _ ≤ (n * D ^ 2) * (∑ j, x j ^ 2) := by
          exact mul_le_mul_of_nonneg_right hEin (by positivity)
  calc ∑ i, (E.mulVec x i) ^ 2 ≤ ∑ i, n * D ^ 2 * (∑ j, x j ^ 2) :=
        Finset.sum_le_sum (fun i _ => hsq i)
    _ = m * (n * D ^ 2 * (∑ j, x j ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
    _ = (m * n) * D ^ 2 * (∑ j, x j ^ 2) := by ring

/-- Корневая (нормовая) форма: ‖(Ŵ−W)x‖₂ ≤ D·√(m·n)·‖x‖₂. -/
theorem quant_matrix_perturb_norm {m n : ℕ} (W Wq : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hres : ∀ i j, |Wq i j - W i j| ≤ D) :
    Real.sqrt (∑ i, ((Wq - W).mulVec x i) ^ 2)
      ≤ D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2) := by
  have key := quant_matrix_perturb W Wq x D hD hres
  have hpos : (0:ℝ) ≤ D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2) := by
    positivity
  have hR : (m * n) * D ^ 2 * (∑ j, x j ^ 2)
      = (D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ m * n),
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ ∑ j, x j ^ 2)]
    ring
  rw [hR] at key
  calc Real.sqrt (∑ i, ((Wq - W).mulVec x i) ^ 2)
      ≤ Real.sqrt ((D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2) := Real.sqrt_sq hpos

/-- **The layer-output→loss bridge** (unified plan §6.2, step 3):
if the loss ℓ is κ-Lipschitz in the layer output (Euclidean
norm on Fin m), then quantizing an m×n layer with
componentwise error ≤ D changes the loss by at most

  |ℓ(Ŵ x) − ℓ(W x)| ≤ κ · D · √(m·n) · ‖x‖₂

— the direct composition of the dimension-correct output
perturbation (quant_matrix_perturb_norm) with the measured
Lipschitz constant of the loss (h_emp_lip-style premise). -/
theorem quant_loss_bridge {m n : ℕ} (W Wq : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (ell : (Fin m → ℝ) → ℝ) (kappa D : ℝ)
    (hD : 0 ≤ D) (hk : 0 ≤ kappa)
    (hres : ∀ i j, |Wq i j - W i j| ≤ D)
    (hlip : ∀ y z, |ell y - ell z|
      ≤ kappa * Real.sqrt (∑ i, (y i - z i) ^ 2)) :
    |ell (Wq.mulVec x) - ell (W.mulVec x)|
      ≤ kappa * D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2) := by
  have hpert := quant_matrix_perturb_norm W Wq x D hD hres
  -- ‖Wq x − W x‖₂ = ‖(Wq − W) x‖₂
  have hlip2 := hlip (Wq.mulVec x) (W.mulVec x)
  have hsum : (∑ i, (Wq.mulVec x i - W.mulVec x i) ^ 2)
      = ∑ i, ((Wq - W).mulVec x i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [Matrix.sub_mulVec]; rfl
  rw [hsum] at hlip2
  calc |ell (Wq.mulVec x) - ell (W.mulVec x)|
      ≤ kappa * Real.sqrt (∑ i, ((Wq - W).mulVec x i) ^ 2) := hlip2
    _ ≤ kappa * (D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2)) :=
        mul_le_mul_of_nonneg_left hpert hk
    _ = kappa * D * Real.sqrt (m * n) * Real.sqrt (∑ j, x j ^ 2) := by ring

set_option maxHeartbeats 8000000 in
/-- **Frobenius-уровень цены квантования**
(единый план §6.2/§6.3):
при покомпонентной ошибке ≤ D
и κ_F-липшицевости потери ℓ по
норме Фробениуса (явная sqrt-форма):

  |ℓ(W) − ℓ(Ŵ)| ≤ κ_F · D · √(m·n)

— весовой аналог mdl_rank_ce (для
rank-k усечения √(∑σ²) вместо D·√(mn)). -/
theorem quant_frob_loss {m n : ℕ} (W Wq : Matrix (Fin m) (Fin n) ℝ)
    (ell : Matrix (Fin m) (Fin n) ℝ → ℝ) (kappaF D : ℝ)
    (hkF : 0 ≤ kappaF) (hD : 0 ≤ D)
    (hres : ∀ i j, |Wq i j - W i j| ≤ D)
    (hlip : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
      |ell X - ell Y|
        ≤ kappaF * Real.sqrt (∑ i, ∑ j, (X i j - Y i j) ^ 2)) :
    |ell W - ell Wq| ≤ kappaF * D * Real.sqrt (m * n) := by
  have hrow : ∀ i : Fin m,
      (∑ j, (Wq i j - W i j) ^ 2) ≤ n * D ^ 2 := by
    intro i
    have hle : ∀ j : Fin n, (Wq i j - W i j) ^ 2 ≤ D ^ 2 := by
      intro j
      have hr := hres i j
      rw [abs_le] at hr
      nlinarith [hr.1, hr.2]
    calc (∑ j, (Wq i j - W i j) ^ 2) ≤ ∑ j : Fin n, D ^ 2 :=
          Finset.sum_le_sum (fun j _ => hle j)
      _ = n * D ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp
  have hsum : (∑ i, ∑ j, (Wq i j - W i j) ^ 2) ≤ m * n * D ^ 2 := by
    calc (∑ i, ∑ j, (Wq i j - W i j) ^ 2)
        ≤ ∑ i, n * D ^ 2 :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = m * n * D ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp
          ring
  have h2 : Real.sqrt (∑ i, ∑ j, (Wq i j - W i j) ^ 2)
      ≤ D * Real.sqrt (m * n) := by
    have h1 := Real.sqrt_le_sqrt hsum
    rwa [Real.sqrt_mul (by positivity : (0:ℝ) ≤ m * n),
      Real.sqrt_sq hD, mul_comm] at h1
  have h := hlip Wq W
  rw [abs_sub_comm] at h
  calc |ell W - ell Wq|
      ≤ kappaF * Real.sqrt (∑ i, ∑ j, (Wq i j - W i j) ^ 2) := h
    _ ≤ kappaF * (D * Real.sqrt (m * n)) :=
        mul_le_mul_of_nonneg_left h2 hkF
    _ = kappaF * D * Real.sqrt (m * n) := by ring



/-- **Minkowski для двойных сумм** (вспомогательная):
‖X+Y‖_F ≤ ‖X‖_F + ‖Y‖_F на Fin×Fin. -/
theorem frob_minkowski {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Real.sqrt (∑ i, ∑ j, (X i j + Y i j) ^ 2)
      ≤ Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2) := by
  have hA : (0:ℝ) ≤ ∑ i, ∑ j, (X i j) ^ 2 := by positivity
  have hB : (0:ℝ) ≤ ∑ i, ∑ j, (Y i j) ^ 2 := by positivity
  -- строчный КШ
  have hrow : ∀ i : Fin m, ∑ j, X i j * Y i j
      ≤ Real.sqrt (∑ j, (X i j) ^ 2) * Real.sqrt (∑ j, (Y i j) ^ 2) := by
    intro i
    have hpx : (0:ℝ) ≤ ∑ j, (X i j) ^ 2 := by positivity
    have hpy : (0:ℝ) ≤ ∑ j, (Y i j) ^ 2 := by positivity
    have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ (X i) (Y i)
    calc ∑ j, X i j * Y i j ≤ |∑ j, X i j * Y i j| := le_abs_self _
      _ = Real.sqrt ((∑ j, X i j * Y i j) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ j, (X i j) ^ 2) * ∑ j, (Y i j) ^ 2) :=
          Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∑ j, (X i j) ^ 2) * Real.sqrt (∑ j, (Y i j) ^ 2) :=
          Real.sqrt_mul hpx (∑ j, (Y i j) ^ 2)
  -- сумма по строкам + КШ по i
  have hcross : ∑ i, ∑ j, X i j * Y i j
      ≤ Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        * Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2) := by
    have hcs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i => Real.sqrt (∑ j, (X i j) ^ 2))
      (fun i => Real.sqrt (∑ j, (Y i j) ^ 2))
    have hax : ∑ i, (Real.sqrt (∑ j, (X i j) ^ 2)) ^ 2
        = ∑ i, ∑ j, (X i j) ^ 2 := by
      exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (by positivity)
    have hbx : ∑ i, (Real.sqrt (∑ j, (Y i j) ^ 2)) ^ 2
        = ∑ i, ∑ j, (Y i j) ^ 2 := by
      exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (by positivity)
    calc ∑ i, ∑ j, X i j * Y i j
        ≤ ∑ i, (Real.sqrt (∑ j, (X i j) ^ 2)
            * Real.sqrt (∑ j, (Y i j) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ ≤ |∑ i, (Real.sqrt (∑ j, (X i j) ^ 2)
            * Real.sqrt (∑ j, (Y i j) ^ 2))| := le_abs_self _
      _ = Real.sqrt ((∑ i, (Real.sqrt (∑ j, (X i j) ^ 2)
            * Real.sqrt (∑ j, (Y i j) ^ 2))) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ i, (Real.sqrt (∑ j, (X i j) ^ 2)) ^ 2)
          * (∑ i, (Real.sqrt (∑ j, (Y i j) ^ 2)) ^ 2)) :=
          Real.sqrt_le_sqrt hcs
      _ = Real.sqrt ((∑ i, ∑ j, (X i j) ^ 2)
          * ∑ i, ∑ j, (Y i j) ^ 2) := by
          rw [hax, hbx]
      _ = Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
          * Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2) :=
          Real.sqrt_mul hA (∑ i, ∑ j, (Y i j) ^ 2)
  -- разложение квадрата
  have hexp : ∑ i, ∑ j, (X i j + Y i j) ^ 2
      = (∑ i, ∑ j, (X i j) ^ 2) + 2 * (∑ i, ∑ j, X i j * Y i j)
        + (∑ i, ∑ j, (Y i j) ^ 2) := by
    have hterm : ∀ i : Fin m, ∑ j, (X i j + Y i j) ^ 2
        = (∑ j, (X i j) ^ 2) + 2 * (∑ j, X i j * Y i j)
          + (∑ j, (Y i j) ^ 2) := by
      intro i
      calc (∑ j, (X i j + Y i j) ^ 2)
          = ∑ j, ((X i j) ^ 2 + (2 * (X i j * Y i j) + (Y i j) ^ 2)) :=
            Finset.sum_congr rfl (fun j _ => by ring)
        _ = (∑ j, (X i j) ^ 2)
            + ∑ j, (2 * (X i j * Y i j) + (Y i j) ^ 2) :=
            Finset.sum_add_distrib
        _ = (∑ j, (X i j) ^ 2)
            + ((∑ j, 2 * (X i j * Y i j)) + ∑ j, (Y i j) ^ 2) := by
            rw [Finset.sum_add_distrib]
        _ = (∑ j, (X i j) ^ 2) + 2 * (∑ j, X i j * Y i j)
            + (∑ j, (Y i j) ^ 2) := by
            rw [Finset.mul_sum]
            ring
    calc (∑ i, ∑ j, (X i j + Y i j) ^ 2)
        = ∑ i, ((∑ j, (X i j) ^ 2)
            + (2 * (∑ j, X i j * Y i j) + ∑ j, (Y i j) ^ 2)) :=
          Finset.sum_congr rfl (fun i _ => by rw [hterm i]; ring)
      _ = (∑ i, ∑ j, (X i j) ^ 2)
          + ∑ i, (2 * (∑ j, X i j * Y i j) + ∑ j, (Y i j) ^ 2) :=
          Finset.sum_add_distrib
      _ = (∑ i, ∑ j, (X i j) ^ 2)
          + ((∑ i, 2 * (∑ j, X i j * Y i j))
              + ∑ i, ∑ j, (Y i j) ^ 2) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ i, ∑ j, (X i j) ^ 2) + 2 * (∑ i, ∑ j, X i j * Y i j)
          + (∑ i, ∑ j, (Y i j) ^ 2) := by
          rw [Finset.mul_sum]
          ring
  have hsqAB : (Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
      + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2)) ^ 2
      = (∑ i, ∑ j, (X i j) ^ 2) + 2 * (Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        * Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2))
      + (∑ i, ∑ j, (Y i j) ^ 2) := by
    have e : (Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2)) ^ 2
        = (Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)) ^ 2
          + 2 * (Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
            * Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2))
          + (Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2)) ^ 2 := by ring
    rw [e, Real.sq_sqrt hA, Real.sq_sqrt hB]
  calc Real.sqrt (∑ i, ∑ j, (X i j + Y i j) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
          + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hexp, hsqAB]
          linarith
    _ = Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- ДЕЛЕГИРОВАНИЕ Mathlib (аудит v5 п.6): Минковский для
Фробениуса — неравенство треугольника L2 (norm_add_le в
EuclideanSpace); ручное доказательство из TopLevel.frob_minkowski
заменено одной ссылкой. -/
theorem frob_minkowski' {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℝ) :
    Real.sqrt (∑ i, ∑ j, (X i j + Y i j) ^ 2)
      ≤ Real.sqrt (∑ i, ∑ j, (X i j) ^ 2)
        + Real.sqrt (∑ i, ∑ j, (Y i j) ^ 2) := by
  have hnorm : ∀ (Z : Matrix (Fin m) (Fin n) ℝ),
      (‖(WithLp.toLp 2 (fun p => Z p.1 p.2) :
        EuclideanSpace ℝ (Fin m × Fin n))‖)
        = Real.sqrt (∑ i, ∑ j, (Z i j) ^ 2) := by
    intro Z
    simp only [EuclideanSpace.norm_eq]
    congr 1
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => by simp))
  have hadd : (WithLp.toLp 2 (fun p => X p.1 p.2)
      + WithLp.toLp 2 (fun p => Y p.1 p.2) :
      EuclideanSpace ℝ (Fin m × Fin n))
      = WithLp.toLp 2 (fun p => X p.1 p.2 + Y p.1 p.2) := rfl
  have key := norm_add_le
    (WithLp.toLp 2 (fun p => X p.1 p.2) :
      EuclideanSpace ℝ (Fin m × Fin n))
    (WithLp.toLp 2 (fun p => Y p.1 p.2) :
      EuclideanSpace ℝ (Fin m × Fin n))
  rw [hadd] at key
  have hXY : ∑ i, ∑ j, (X i j + Y i j) ^ 2
      = ∑ i, ∑ j, ((X + Y) i j) ^ 2 := by
    simp [Matrix.add_apply]
  rw [hXY, ← hnorm (X + Y), ← hnorm X, ← hnorm Y]
  exact key

/-- **Полная цена двухстадийного сжатия**
(единый план §6.2, замыкание цепочки):
если первая стадия сжатия (напр.
rank-k усечение) удаляет веса
на δ₁ (Фробениус), вторая (квантование)
— ещё на δ₂, то при κ_F-липшицевости
потери полная цена аддитивна:

  |ℓ(W) − ℓ(W'')| ≤ κ_F · (δ₁ + δ₂). -/
theorem compress_chain_cost {m n : ℕ} (W W1 W2 : Matrix (Fin m) (Fin n) ℝ)
    (ell : Matrix (Fin m) (Fin n) ℝ → ℝ) (kappaF d1 d2 : ℝ)
    (hkF : 0 ≤ kappaF)
    (h1 : Real.sqrt (∑ i, ∑ j, (W1 i j - W i j) ^ 2) ≤ d1)
    (h2 : Real.sqrt (∑ i, ∑ j, (W2 i j - W1 i j) ^ 2) ≤ d2)
    (hlip : ∀ X Y : Matrix (Fin m) (Fin n) ℝ,
      |ell X - ell Y|
        ≤ kappaF * Real.sqrt (∑ i, ∑ j, (X i j - Y i j) ^ 2)) :
    |ell W - ell W2| ≤ kappaF * (d1 + d2) := by
  have h := hlip W2 W
  rw [abs_sub_comm] at h
  have hM := frob_minkowski
    (fun i j => W1 i j - W i j) (fun i j => W2 i j - W1 i j)
  have hsum_eq : ∑ i, ∑ j, ((W1 i j - W i j) + (W2 i j - W1 i j)) ^ 2
      = ∑ i, ∑ j, (W2 i j - W i j) ^ 2 :=
    Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [hsum_eq] at hM
  have h12 : Real.sqrt (∑ i, ∑ j, (W1 i j - W i j) ^ 2)
      + Real.sqrt (∑ i, ∑ j, (W2 i j - W1 i j) ^ 2) ≤ d1 + d2 :=
    add_le_add h1 h2
  calc |ell W - ell W2|
      ≤ kappaF * Real.sqrt (∑ i, ∑ j, (W2 i j - W i j) ^ 2) := h
    _ ≤ kappaF * (d1 + d2) := by
        refine mul_le_mul_of_nonneg_left ?_ hkF
        exact le_trans hM h12

end Hagi.Energy


namespace Hagi
export Hagi.Energy (quant_residual_norm quant_energy_bridge quant_matrix_perturb
  quant_matrix_perturb_norm quant_loss_bridge quant_frob_loss
  frob_minkowski compress_chain_cost)
end Hagi
/-!
# SafeQPRobust — устойчивая к возмущениям допустимость

* `robust_feasibility`: при `eps + m ≤ g*d` и
  `|g*d − gdhat| ≤ m` — `eps ≤ gdhat` (запас eps + m
  поглощает шум батча);
* `stochastic_safeqp_feasible`: построчная версия для всех
  доменов i;
* `stochastic_safeqp_descent`: при `dnorm² ≤ inner_true`,
  `|inner_est − inner_true| ≤ m0`, `0 < L`, `eta ≤ 1/L` и
  гладкости — `E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`
  (чистый спуск при `m0 < dnorm²`).

Полная проекционно-возмущенческая оценка `‖d̂*−d*‖` — не
доказана (матричная теория возмущений).
-/

open Finset

namespace Hagi.Step

/-- При `eps + m ≤ g*d` и `|g*d − gdhat| ≤ m`:
`eps ≤ gdhat`. -/
theorem robust_feasibility (g d gdhat : ℝ) (eps m : ℝ)
    (htrue : eps + m ≤ g * d) (hpert : |g * d - gdhat| ≤ m) :
    eps ≤ gdhat := by
  nlinarith [abs_le.mp hpert]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Если для всех i выполнено `eps i + m i ≤ g i * d i` и
`|g i * d i − gdhat i| ≤ m i`, то `eps i ≤ gdhat i` для
всех i. -/
theorem stochastic_safeqp_feasible {K : Type} [Fintype K]
    (g d gdhat : K → ℝ) (eps m : K → ℝ)
    (htrue : ∀ i, eps i + m i ≤ g i * d i)
    (h_emp_conc : ∀ i, |g i * d i - gdhat i| ≤ m i) :
    ∀ i, eps i ≤ gdhat i :=
  fun i => robust_feasibility (g i) (d i) (gdhat i) (eps i) (m i)
    (htrue i) (h_emp_conc i)

/-- При `dnorm² ≤ inner_true`, `|inner_est − inner_true| ≤ m0`,
`0 < L`, `0 ≤ eta ≤ 1/L` и гладкости
`E₂ ≤ E₁ − eta·inner_est + L·eta²·dnorm²/2` —
`E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`. -/
theorem stochastic_safeqp_descent (inner_true inner_est dnorm m0 eta L E1 E2 : ℝ)
    (hdescent : dnorm ^ 2 ≤ inner_true)
    (h_emp_conc : |inner_est - inner_true| ≤ m0)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * inner_est + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 + eta * m0 := by
  have heff : dnorm ^ 2 - m0 ≤ inner_est := by
    rw [abs_le] at h_emp_conc
    have h1 : -(m0) ≤ inner_est - inner_true := h_emp_conc.1
    have h2 : inner_est - inner_true ≤ m0 := h_emp_conc.2
    have h3 : inner_true - m0 ≤ inner_est := by linarith
    linarith
  have hsecond : L * eta ^ 2 * dnorm ^ 2 / 2 ≤ eta * dnorm ^ 2 / 2 := by
    have hLe : L * eta ≤ 1 := by
      have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
      have hdiv : L * (1 / L) = 1 := by field_simp
      linarith
    by_cases hd : dnorm ^ 2 = 0
    · rw [hd]
      norm_num
    · have hd2 : 0 < dnorm ^ 2 := by
        have hnn : 0 ≤ dnorm ^ 2 := sq_nonneg dnorm
        by_contra hc
        push Not at hc
        apply hd
        linarith
      have hsplit : L * eta ^ 2 * dnorm ^ 2 = (L * eta) * (eta * dnorm ^ 2) := by ring
      rw [hsplit]
      have hmono : (L * eta) * (eta * dnorm ^ 2) ≤ 1 * (eta * dnorm ^ 2) :=
        mul_le_mul_of_nonneg_right hLe (by nlinarith)
      calc L * eta * (eta * dnorm ^ 2) / 2
          = (L * eta) * (eta * dnorm ^ 2) / 2 := by ring
        _ ≤ 1 * (eta * dnorm ^ 2) / 2 := by
            have hd2' : 2 * ((L * eta) * (eta * dnorm ^ 2) / 2)
                = (L * eta) * (eta * dnorm ^ 2) := by ring
            have hd3' : 2 * (1 * (eta * dnorm ^ 2) / 2) = eta * dnorm ^ 2 := by ring
            nlinarith [hmono, hd2', hd3']
        _ = eta * dnorm ^ 2 / 2 := by ring
  nlinarith [h_emp_smooth, heff, hsecond, heta0]

end Hagi.Step

namespace Hagi
export Hagi.Step (robust_feasibility stochastic_safeqp_feasible stochastic_safeqp_descent)
end Hagi
set_option linter.style.header false

/-!
# The top-level cycle bound on pipeline variables

`top_level_cycle_bound`: one macro generation on real
quantities (token-weighted CE's, the SafeQP projection
output `ds`, ternary compression) satisfies
`E4 ≤ Emean − (G + eta * ‖ds‖² / 2 − kappa * √n * s / 2)`.
The empirical inputs are the smoothness and Lipschitz
premises; the descent direction and the √n factor are
derived (`safeQP_descent`, `quant_energy_bridge`).
`top_level_termination` / `horizon_termination` give the
horizon bound; `noisy_cycle_step` adds minibatch noise
`m₀`; `merge_stage_concat_adapter` realizes the merge
hypothesis from the token-level Concat law.
-/

open Real InnerProductSpace Finset

namespace Hagi.Unified

/-- Under the stated premises (SafeQP minimality, smoothness
h_emp_, per-entry distortion ≤ s/2, Lipschitz h_emp_), one
macro generation satisfies
`E4 ≤ Emean − (G + eta * ‖ds‖² / 2 − kappa * √n * s / 2)`,
with the descent quantity derived from `safeQP_descent` and
the √n factor from `quant_energy_bridge`. -/
theorem top_level_cycle_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta Emean E2 E3 E4 G kappa s : ℝ) {n : ℕ}
    {w q : Fin n → ℝ}
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hE2 : E2 ≤ Emean - G) (_hG : 0 ≤ G)
    (h_emp_smooth : E3 ≤ E2 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2)
    (hs0 : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2) (hkappa : 0 ≤ kappa)
    (h_emp_lip : E4 - E3 ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2)) :
    E4 ≤ Emean - (G + eta * ‖ds‖ ^ 2 / 2 - kappa * Real.sqrt (n : ℝ) * s / 2) := by
  -- the joint stage with REAL descent quantities (derived from safeQP_descent)
  have hjoint := Hagi.joint_stage_linked C hconv h0 g0 ds hs hmin L eta E2 E3
    hL heta heta0 h_emp_smooth
  -- the quant stage DERIVED through the R70 bridge (dependency made real —
  -- the R75 honesty fix: not an assumed final bound)
  have hquant := Hagi.quant_energy_bridge w q s kappa (E4 - E3) hs0 hres hkappa h_emp_lip
  -- assemble the three real stages: merge law, joint descent, quant cost
  linarith

/-- **Терминация из телескопа с риск-бюджетом (R529)**:
композиция `stage_certificate_telescope` + лиапуновской терминации.
Каждое поколение сертифицировано: после ≤ before − decrease + riskSpend
(soundность телескопа), decrease ≥ ε > 0 в каждом поколении, а
суммарный risk-спенд ограничен R (риск-бюджет). Тогда потенциал на
выходе T поколений остаётся ≥ Emin − R, и горизонт ограничен:
T ≤ (Φ₀ − Emin + R) / ε. Риск-бюджет входит в числитель горизонта —
менеджмент риска линеен по времени жизни процесса. -/
theorem risk_budget_termination (cs : ℕ → Hagi.StageCertificate)
    (Φ₀ Emin eps R : ℝ) (T : ℕ)
    (hT : 0 < T)
    (heps : 0 < eps)
    (h0 : (cs 0).before = Φ₀)
    (hcontig : ∀ t, t + 1 < T → (cs (t + 1)).before = (cs t).after)
    (hsound : ∀ t, t < T →
      (cs t).after ≤ (cs t).before - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend)
    (hdec : ∀ t, t < T → eps ≤ ((cs t).cert).decrease)
    (hsum : ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend ≤ R)
    (hR0 : 0 ≤ R)
    (hfloor : Emin ≤ (cs (T - 1)).after) :
    (T : ℝ) ≤ (Φ₀ - Emin + R) / eps := by
  have htel := Hagi.stage_certificate_telescope cs hT hcontig hsound
  rw [h0] at htel
  -- sum of decreases ≥ T * eps
  have hsumdec : ∑ t ∈ Finset.range T, ((cs t).cert).decrease ≥ eps * (T:ℝ) := by
    calc eps * (T:ℝ) = ∑ t ∈ Finset.range T, eps := by
          rw [Finset.sum_const]; simp; ring
      _ ≤ ∑ t ∈ Finset.range T, ((cs t).cert).decrease :=
          Finset.sum_le_sum fun t ht => hdec t (Finset.mem_range.mp ht)
  -- after_{T-1} ≤ Φ₀ − Tε + R
  have hbound : (cs (T - 1)).after ≤ Φ₀ - eps * (T:ℝ) + R := by
    calc (cs (T - 1)).after
        ≤ Φ₀ - ∑ t ∈ Finset.range T, ((cs t).cert).decrease
          + ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend := htel
      _ ≤ Φ₀ - eps * (T:ℝ) + R := by linarith
  -- close: Emin − R ≤ after ≤ Φ₀ − Tε + R
  have hcomm : eps * (T:ℝ) = (T:ℝ) * eps := mul_comm _ _
  rw [le_div_iff₀ heps]
  linarith

/-- If `Emin ≤ E t` for `t ≤ k` and each step decreases by
at least `eps > 0`, then `k ≤ (E 0 − Emin) / eps`. -/
theorem top_level_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hstep : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  Hagi.lyapunov_termination_fin Emin eps k hE hstep heps

/-- Deterministic one-cycle bound under minibatch noise: with
concentration `|inner_est − inner_true| ≤ m0` (h_emp_),
smoothness in `inner_est`, `E3 = E2`, and the residual-norm
compression premise, `E4 ≤ Emean − (G + eta * dnorm² / 2 −
eta * m0 − kappa * √n * s / 2)`. No probability space is
involved. -/
theorem noisy_cycle_step {n : ℕ} {w q : Fin n → ℝ}
    (inner_true inner_est dnorm m0 eta L Emean E1 E2 E3 E4 G kappa s : ℝ)
    (hdescent : dnorm ^ 2 ≤ inner_true)
    (h_emp_conc : |inner_est - inner_true| ≤ m0)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * inner_est + L * eta ^ 2 * dnorm ^ 2 / 2)
    (hE1 : E1 ≤ Emean - G)
    (hs0 : 0 ≤ s) (hres : ∀ i, |w i - q i| ≤ s / 2) (hkappa : 0 ≤ kappa)
    (hquant : E4 - E3 ≤ kappa * Real.sqrt (∑ i, (w i - q i) ^ 2))
    (hE3 : E3 = E2) :
    E4 ≤ Emean - (G + eta * dnorm ^ 2 / 2 - eta * m0
      - kappa * Real.sqrt (n : ℝ) * s / 2) := by
  have hstoch := Hagi.stochastic_safeqp_descent inner_true inner_est dnorm m0 eta L E1 E2
    hdescent h_emp_conc hL heta heta0 h_emp_smooth
  have hq := Hagi.quant_energy_bridge w q s kappa (E4 - E3) hs0 hres hkappa hquant
  rw [hE3] at hq
  linarith

/-- Restatement of `top_level_termination`: per-step decrease
≥ eps and lower bound `Emin` give
`k ≤ (E 0 − Emin) / eps`. -/
theorem horizon_termination {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t) (hstep : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  top_level_termination Emin eps k hE hstep heps

/-- For nonnegative weights `w` and per-token Concat law
`cmerged t ≤ cmean t`: the token-weighted merge identity
`∑ w t * cmerged t = ∑ w t * cmean t − ∑ w t * (cmean t − cmerged t)`
holds, and the gap `∑ w t * (cmean t − cmerged t)` is
nonnegative. -/
theorem merge_stage_concat_adapter {Tok : Type} [Fintype Tok]
    (w cmean cmerged : Tok → ℝ)
    (hw : ∀ t, 0 ≤ w t)
    (hcat : ∀ t, cmerged t ≤ cmean t) :
    (∑ t, w t * cmerged t = (∑ t, w t * cmean t)
        - ∑ t, w t * (cmean t - cmerged t))
    ∧ 0 ≤ ∑ t, w t * (cmean t - cmerged t) := by
  constructor
  · -- the definitional identity: per-term w·cmean − w·(diff) = w·cmerged
    have hterm : ∀ t : Tok, w t * cmean t - w t * (cmean t - cmerged t)
        = w t * cmerged t := by
      intro t
      ring
    have hsplit : ∑ t : Tok, w t * cmerged t
        = (∑ t : Tok, w t * cmean t) - ∑ t : Tok, w t * (cmean t - cmerged t) := by
      have e1 : ∑ t : Tok, (w t * cmean t - w t * (cmean t - cmerged t))
          = (∑ t : Tok, w t * cmean t) - ∑ t : Tok, w t * (cmean t - cmerged t) :=
        sum_sub_distrib (fun t : Tok => w t * cmean t)
          (fun t : Tok => w t * (cmean t - cmerged t))
      rw [← e1]
      exact Finset.sum_congr rfl (fun t _ => (hterm t).symm)
    exact hsplit
  · -- G >= 0: a sum of nonneg terms (w >= 0, mean - merged >= 0 by Concat)
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (hw t) (by
      have := hcat t
      linarith)

end Hagi.Unified

namespace Hagi
export Hagi.Unified (top_level_cycle_bound top_level_termination noisy_cycle_step horizon_termination merge_stage_concat_adapter risk_budget_termination)
end Hagi
