import Mathlib.Tactic
import Hagi.StatMech.Hopfield.Model
import Hagi.Learning.TernaryPert

set_option linter.style.header false

/-!
# Concentration — оценка партициона Хопфилда (цикл 28)

Мост StatMech ↔ Learning: Frobenius-оценка (переиспользована
из TernaryPert.frob_submul, цикл 11) даёт равномерную границу
энергии по всем спиновым конфигурациям:
  E(σ; J) = ‖J·σ‖²/(2N) ≤ ‖J‖²_F/2
(через eunorm(spins σ) = √N), откуда верхняя оценка
партицион-функции:
  Z = Σ_σ exp(β·E(σ)) ≤ 2^N · exp(β·‖J‖²_F/2),
и свободная энергия на спин:
  (1/N)·log Z ≤ log 2 + β·‖J‖²_F/(2N).

Ёмкость памяти вычисляется из нормы паттернов — выводится, а
не подбирается.
-/

open Finset Hagi.Core

namespace Hagi.StatMech.Hopfield.Concentration

open Hagi.StatMech.Hopfield Hagi.Learning.TernaryPert

/-! ### Равномерная энергетическая граница -/

/-- Норма спиновой конфигурации: Σ spin² = N (каждый спин ±1). -/
theorem eunorm_spins {N : ℕ} (σ : Fin N → Bool) :
    eunorm (spins σ) = Real.sqrt N := by
  have hsum : ∑ i : Fin N, (spins σ i) ^ 2
      = ((Fintype.card (Fin N) : ℕ) : ℝ) := by
    have hterm : ∀ i : Fin N, (spins σ i) ^ 2 = 1 := by
      intro i
      unfold spins spinOf
      rcases σ i with _ | _
      · simp
      · simp
    have h1 : ∑ i : Fin N, (spins σ i) ^ 2
        = ∑ i : Fin N, (1:ℝ) :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  unfold eunorm
  rw [hsum, Fintype.card_fin]

theorem frobSq_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    (0:ℝ) ≤ frobSq M := by
  unfold frobSq
  exact Finset.sum_nonneg (fun i _ => by positivity)

/-- Энергия любой конфигурации ≤ ‖J‖²_F/2:
E(σ) = outNorm(Jσ)²/(2N) ≤ (‖J‖_F·√N)²/(2N) = ‖J‖²_F/2. -/
theorem energy_le_frob {N K : ℕ} [NeZero N]
    (J : Matrix (Fin K) (Fin N) ℝ)
    (σ : Fin N → Bool) :
    energy N K J σ ≤ frobSq J / 2 := by
  have hf := frob_submul (E := J) (x := spins σ)
  have honn : (0:ℝ) ≤ outNorm (fun i => dotProduct (rowVec J i)
      (spins σ)) := by
    unfold outNorm
    exact Real.sqrt_nonneg _
  have hnn : (0:ℝ) ≤ Real.sqrt (frobSq J) * eunorm (spins σ) :=
    mul_nonneg (Real.sqrt_nonneg _) (by
      rw [eunorm_spins]; exact Real.sqrt_nonneg _)
  have hsq : outNorm (fun i => dotProduct (rowVec J i) (spins σ)) ^ 2
      ≤ (Real.sqrt (frobSq J) * eunorm (spins σ)) ^ 2 :=
    by nlinarith [honn, hnn, hf,
      sq_nonneg (outNorm (fun i => dotProduct (rowVec J i) (spins σ)))]
  rw [eunorm_spins] at hsq
  -- (√frobSq·√N)² = frobSq·N
  have hprod : (Real.sqrt (frobSq J) * Real.sqrt N) ^ 2
      = frobSq J * N := by
    rw [show Real.sqrt (frobSq J) * Real.sqrt N
        = Real.sqrt (frobSq J * N) from by
      rw [Real.sqrt_mul (frobSq_nonneg J) (N:ℝ)]]
    rw [Real.sq_sqrt (mul_nonneg (frobSq_nonneg J)
      (Nat.cast_nonneg _))]
  rw [hprod] at hsq
  -- energy = outNorm²/(2N) ≤ frobSq·N/(2N) = frobSq/2
  have houtnorm : (∑ k, (J.mulVec (spins σ) k) ^ 2)
      = outNorm (fun i => dotProduct (rowVec J i) (spins σ)) ^ 2 := by
    unfold outNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun k _ => by positivity))]
    congr 1
  calc energy N K J σ
      = ∑ k, (J.mulVec (spins σ) k) ^ 2 / (2 * N : ℝ) := rfl
    _ ≤ frobSq J * N / (2 * N : ℝ) := by
        rw [← Finset.sum_div, houtnorm]
        have hN : (0:ℝ) < N := by
          have : (0:ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
          exact_mod_cast this
        have h2Npos : (0:ℝ) < 2 * N := by nlinarith
        have := mul_le_mul_of_nonneg_right hsq h2Npos.le
        rwa [← div_le_div_iff₀ h2Npos] at this
    _ = frobSq J / 2 := by
        have hNpos : (0:ℝ) < N := by
          have : (0:ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
          exact_mod_cast this
        have hhalf : (N:ℝ) / (2 * N) = 1 / 2 := by
          field_simp
        rw [mul_div_assoc, hhalf, mul_one_div]

/-! ### Партицион -/

/-- ВЕРХНЯЯ ОЦЕНКА ПАРТИЦИОНА: Z ≤ 2^N · exp(β·‖J‖²_F/2)
при β ≥ 0. Ёмкость памяти вычисляется из нормы паттернов. -/
theorem partition_le {N K : ℕ} [NeZero N] (beta : ℝ) (hβ : 0 ≤ beta)
    (J : Matrix (Fin K) (Fin N) ℝ) :
    partition N K beta J
      ≤ 2 ^ N * Real.exp (beta * frobSq J / 2) := by
  unfold partition
  have hper : ∀ σ : Fin N → Bool,
      Real.exp (beta * energy N K J σ)
        ≤ Real.exp (beta * frobSq J / 2) := by
    intro σ
    have h := mul_le_mul_of_nonneg_left (energy_le_frob J σ) hβ
    have h2 : beta * frobSq J / 2 = beta * (frobSq J / 2) := by ring
    rw [h2]
    exact Real.exp_le_exp.mpr h
  calc ∑ σ : Fin N → Bool, Real.exp (beta * energy N K J σ)
      ≤ ∑ σ : Fin N → Bool, Real.exp (beta * frobSq J / 2) :=
        Finset.sum_le_sum (fun σ _ => hper σ)
    _ = 2 ^ N * Real.exp (beta * frobSq J / 2) := by
        simp [Fintype.card_fun]

/-- Свободная энергия на спин: (1/N)·log Z ≤ log 2 +
β·‖J‖²_F/(2N) — ёмкостная граница: норма паттернов задаёт
свободную энергию, память НЕ растёт быстрее нормы. -/
theorem freeEnergy_le {N K : ℕ} [NeZero N] (beta : ℝ) (hβ : 0 ≤ beta)
    (J : Matrix (Fin K) (Fin N) ℝ) :
    freeEnergyDensity N K beta J
      ≤ Real.log 2 + beta * frobSq J / (2 * ((N:ℕ):ℝ)) := by
  have hZpos : 0 < partition N K beta J := partition_pos N K beta J
  have hZle := partition_le beta hβ J
  have h2N : ((2 * N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
  have hN0 : ((N:ℕ):ℝ) ≠ 0 := by
    have : (0:ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this.ne'
  have hNpos : (0:ℝ) < ((N:ℕ):ℝ) := by
    have : (0:ℕ) < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hexp : Real.log (2 ^ N * Real.exp (beta * frobSq J / 2))
      = N * Real.log 2 + beta * frobSq J / 2 := by
    have h1 : (0:ℝ) < 2 ^ N := by positivity
    rw [Real.log_mul h1.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_pow]
  unfold freeEnergyDensity
  have hstep : Real.log (partition N K beta J) / N
      ≤ Real.log (2 ^ N * Real.exp (beta * frobSq J / 2)) / N := by
    have hle := Real.log_le_log hZpos hZle
    have hmul := mul_le_mul_of_nonneg_right hle hNpos.le
    rwa [← div_le_div_iff₀ hNpos] at hmul
  refine le_trans hstep ?_
  rw [hexp, add_div, mul_div_assoc]
  field_simp
  exact le_refl _

end Hagi.StatMech.Hopfield.Concentration
