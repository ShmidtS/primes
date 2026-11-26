/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# LrRestart — перезапуск lr на границе домена усиливает забывание старого

Zheng et al. 2026 (arXiv 2610.31551): расписание lr определяет, как
возмущения данных распространяются через последующие задачи; перезапуск
затухания на границах задач меняет это распространение. В HAGI `train_optimal`
строит оптимизатор на домен — warmup/cosine перезапускаются.

* `damp lam eta T = ∏_{t<T} (1 − λ·η_t)` — множитель старого возмущения в
  квадратичной модели с кривизной `λ`;
* `damp_le_of_eta_le` — если перезапущенные шаги не меньше продолженных
  (`ec ≤ er`) и `0 ≤ λ·η ≤ 1`, старое возмущение затухает сильнее:
  перезапуск = быстрее учить новое, быстрее забывать старое;
* `sum_eta_le` — суммарная чувствительность к данным нового домена не меньше.

Балансируется повтором (`ReplaySchedule`): код измерил +0.40 → +0.04
забывания при `REPLAY_FRAC 0.30 → 1.0`.
-/

open Finset
namespace Hagi.Step.LrRestart

/-- Квадратичная модель с кривизной `λ`: возмущение `δ₀` стартового состояния
после `T` шагов SGD с шагами `η` умножается на `∏ (1 − η_t·λ)`. -/
noncomputable def damp (lam : ℝ) (eta : ℕ → ℝ) (T : ℕ) : ℝ := ∏ t ∈ range T, (1 - eta t * lam)
/-- Перезапуск lr (крупные шаги в начале нового домена) затягивает старое
возмущение сильнее: `η_restart ≥ η_cont` поточечно ⇒ `damp restart ≤ damp cont`. -/
theorem damp_le_of_eta_le (lam : ℝ) (hlam : 0 ≤ lam) (er ec : ℕ → ℝ)
    (h0 : ∀ t, 0 ≤ ec t * lam) (her : ∀ t, er t * lam ≤ 1) (hec : ∀ t, ec t * lam ≤ 1)
    (h : ∀ t, ec t ≤ er t)
    (T : ℕ) : damp lam er T ≤ damp lam ec T := by
  unfold damp
  induction T with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hn : 0 ≤ ∏ t ∈ range k, (1 - ec t * lam) :=
      Finset.prod_nonneg (fun t _ => by nlinarith [h0 t, hec t])
    have hk : 0 ≤ ∏ t ∈ range k, (1 - er t * lam) :=
      Finset.prod_nonneg (fun t _ => by nlinarith [h0 t, h t, her t])
    exact mul_le_mul ih (by nlinarith [h k]) (by nlinarith [h0 k, her k]) hn
/-- Суммарная чувствительность к данным нового домена `∑ η_t` при перезапуске
не меньше. -/
theorem sum_eta_le (er ec : ℕ → ℝ) (h : ∀ t, ec t ≤ er t) (T : ℕ) :
    ∑ t ∈ range T, ec t ≤ ∑ t ∈ range T, er t :=
  Finset.sum_le_sum fun t _ => h t

end Hagi.Step.LrRestart
