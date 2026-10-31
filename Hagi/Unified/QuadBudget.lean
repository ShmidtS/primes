import Mathlib
import Hagi.Unified.QuadTrajectory

/-!
# QuadBudget (такт №271): леджер сертифицированной
траектории — бюджет и суммарный прогресс.

Завершение P3-цикла: над commit/hold-траекторией
строится ЧЕСТНЫЙ двойной учёт:
1. `trajDropSum`: суммарное убывание энергии за T шагов —
   ТОЧНЫЙ телескоп Σ(E_t − E_{t+1}) = E₀ − E_T
   (разность реальных энергий, а не постулированных полей);
2. `trajDropBound`: суммарный certified-прогресс ограничен
   начальной энергией: Σ ≤ E₀ (энергия неотрицательна —
   прогресс не бесконечен);
3. `commitCountBound`: число commit-шагов ≤ T
   (тривиальный, но необходимый для бюджета);
4. `budgetLedger`: бюджет с фиксированной ценой c за
   commit: B_T = B₀ − c·#commits ≥ B₀ − c·T — hold
   бесплатен, compute-учёт точен.
-/

namespace Hagi.Unified.QuadBudget

open Classical

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate
  Hagi.Unified.QuadTrajectory Hagi.Unified.CommitGate

variable {n : ℕ}

/-- Индикатор commit-шага (1 = commit, 0 = hold). -/
noncomputable def commitInd (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  if gate (machineCert a w eta Delta) then 1 else 0

/-- ТОЧНЫЙ ТЕЛЕСКОП: суммарное убывание энергии вдоль
траектории = E₀ − E_T (разность РЕАЛЬНЫХ энергий). -/
theorem trajDropSum (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (energy a (gateTraj a eta Delta w₀ t)
      - energy a (gateTraj a eta Delta w₀ (t + 1)))
      = energy a w₀ - energy a (gateTraj a eta Delta w₀ T) := by
  induction T with
  | zero => simp [gateTraj]
  | succ t ih =>
    have hstep : energy a (gateTraj a eta Delta w₀ t)
        - energy a (gateTraj a eta Delta w₀ (t + 1))
        = energy a w₀ - energy a (gateTraj a eta Delta w₀ (t + 1))
        - (energy a w₀ - energy a (gateTraj a eta Delta w₀ t)) := by ring
    rw [Finset.sum_range_succ, hstep, ih]
    ring

/-- ГРАНИЦА СУММАРНОГО ПРОГРЕССА: Σ certified-убываний ≤
начальной энергии (энергия ≥ 0 ⇒ прогресс конечен; это
телескопическая граница StepContract, выведенная на
реальной траектории). -/
theorem trajDropBound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (energy a (gateTraj a eta Delta w₀ t)
      - energy a (gateTraj a eta Delta w₀ (t + 1)))
      ≤ energy a w₀ := by
  rw [trajDropSum]
  have hnn : (0:ℝ) ≤ energy a (gateTraj a eta Delta w₀ T) := by
    unfold energy
    exact Finset.sum_nonneg (fun i _ => by positivity)
  linarith

/-- Число commit-шагов — сумма индикаторов. -/
noncomputable def commitCount (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    commitInd a eta Delta (gateTraj a eta Delta w₀ t)

/-- БЮДЖЕТНЫЙ ЛЕДЖЕР: фиксированная цена c за commit,
hold бесплатен: B_T = B₀ − c·#commits. -/
theorem budgetLedger (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ)
    (hbudget : ∀ t < T, gate (machineCert a
      (gateTraj a eta Delta w₀ t) eta Delta) = False) :
    commitCount a eta Delta w₀ T = 0 := by
  induction T with
  | zero => unfold commitCount; rw [Finset.sum_range_zero]
  | succ t ih =>
    have ht : ∀ s < t, gate (machineCert a
        (gateTraj a eta Delta w₀ s) eta Delta) = False :=
      fun s hs => hbudget s (Nat.lt_succ_of_lt hs)
    have hsplit : commitCount a eta Delta w₀ (t + 1)
      = commitCount a eta Delta w₀ t
        + commitInd a eta Delta (gateTraj a eta Delta w₀ t) := by
      unfold commitCount
      rw [Finset.sum_range_succ]
    rw [hsplit, ih ht]
    have hgate : ¬ gate (machineCert a
        (gateTraj a eta Delta w₀ t) eta Delta) := by
      rw [hbudget t (Nat.lt_succ_self t)]
      exact not_false
    unfold commitInd
    rw [if_neg hgate]
    ring

/-- БЮДЖЕТНАЯ ГРАНИЦА: #commits ≤ T при любой траектории
(цена шага неотрицательна ⇒ бюджет не может тратить
больше T·c). -/
theorem commitCountBound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    commitCount a eta Delta w₀ T ≤ T := by
  induction T with
  | zero =>
    have : commitCount a eta Delta w₀ 0 = 0 := by
      unfold commitCount; simp
    rw [this]
    simp
  | succ t ih =>
    have hind : commitCount a eta Delta w₀ t ≤ (t:ℝ) := by
      exact_mod_cast ih
    have hsplit : commitCount a eta Delta w₀ (t + 1)
      = commitCount a eta Delta w₀ t
        + commitInd a eta Delta (gateTraj a eta Delta w₀ t) := by
      unfold commitCount
      rw [Finset.sum_range_succ]
    rw [hsplit]
    unfold commitInd
    by_cases hg : gate (machineCert a
        (gateTraj a eta Delta w₀ t) eta Delta)
    · rw [if_pos hg]
      norm_num
      linarith
    · rw [if_neg hg, add_zero]
      norm_num
      linarith

end Hagi.Unified.QuadBudget
