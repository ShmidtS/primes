/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Foundations.StageCalculus
set_option linter.style.header false

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
