/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Math.Foundations.Telescope
import Hagi.Cert.Core
import Hagi.Cert.StepGen
import Hagi.Training.StepProvider
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Unified.TelescopeInstances — первая партия миграций на generic-телескопы

Каждая теорема ниже — однострочная (одношаговая) маршрутизация
доменного телескопа через generic-ядро `Hagi.Foundations.Telescope`
(`telescope_le_sub`, `telescope_sum_floor_le`, `telescope_sum_le`,
`lyapunov_gain_noise`). Формулировки СТРОГО сильнее замороженных
оригиналов: гипотезы шага ограничены горизонтом (`∀ t < T` вместо
`∀ t`) либо цепь сертификатов задаётся только до горизонта со
скалярным ledger-ом. Полный учёт 40 доменных телескопов —
миграционный ledger `.tmp/C346/ledger.md` (C346, A14 QW6).
-/

open Finset Real Hagi.Foundations

namespace Hagi.Unified.TelescopeInstances

/-! ## Growth.Ceilings -/

/-- Миграция `Hagi.Growth.potential_telescope`: гипотеза шага
ограничена горизонтом, `hVnn` не нужен (не используется и в
оригинальном доказательстве по существу). -/
theorem potential_telescope' (V eps b : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, V (t + 1) ≤ V t - eps t + b t) :
    V T + ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t :=
  by have h := lyapunov_gain_noise (V := V) (gain := eps) (noise := b) hstep
     linarith

/-- Миграция `Hagi.Growth.edge_total_bound` (горизонтная гипотеза,
floor-член `V T ≥ 0` остаётся честной посылкой). -/
theorem edge_total_bound' (V eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ V t)
    (hstep : ∀ t < T, V (t + 1) ≤ V t - eps t + b t) :
    ∑ t ∈ Finset.range T, eps t
      ≤ V 0 + ∑ t ∈ Finset.range T, b t := by
  have h := potential_telescope' V eps b T hstep
  linarith [hVnn T]

/-! ## Growth.LinearCone -/

/-- Миграция `Hagi.Growth.telescope_band` (форма `t < T` вместо
членства в `Finset.range T`; прямое применение `telescope_sum_le`). -/
theorem telescope_band' (C G b : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, C (t + 1) = C t + G t)
    (hband : ∀ t < T, G t ≤ b t) :
    C T - C 0 ≤ ∑ t ∈ Finset.range T, b t :=
  telescope_sum_le (f := C) (c := fun t => b t)
    (fun t ht => by rw [hstep t ht, add_sub_cancel_left]; exact hband t ht)

/-- Миграция `Hagi.Growth.band_telescope` (горизонтная гипотеза;
прямое применение `telescope_sum_le`). -/
theorem band_telescope' (C G : ℕ → ℝ) (b σ : ℝ) (N : ℕ)
    (hstep : ∀ t < N, C (t + 1) = C t + G t)
    (hband : ∀ t < N, G t ≤ b * (1 - σ) ^ t) :
    C N ≤ C 0 + ∑ t ∈ Finset.range N, b * (1 - σ) ^ t := by
  have h := telescope_sum_le (f := C) (c := fun t => b * (1 - σ) ^ t)
    (fun t ht => by rw [hstep t ht, add_sub_cancel_left]; exact hband t ht)
  linarith

/-! ## Cert.Core (скаляризация цепей сертификатов) -/

variable {S : Type*} {TaskId : Type*}
variable {M : Hagi.Cert.SystemMetrics S TaskId}
variable {obl : Hagi.Cert.StepObligations TaskId}

/-- Миграция `Hagi.Cert.trajectory_telescope`: цепь сертификатов
только до горизонта `n`, drops — явный скалярный ledger;
сводится к `telescope_le_sub` на `fun k => M.objective (t k)`. -/
theorem trajectory_telescope' (n : ℕ) (t : ℕ → S) (drop : ℕ → ℝ)
    (steps : ∀ j, j < n → Hagi.Cert.CertStep M obl (t j) (t (j + 1)))
    (hdrop : ∀ j, ∀ h : j < n, drop j = (steps j h).drop) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, drop j :=
  telescope_le_sub
    (f := fun k => M.objective (t k)) (c := drop)
    (fun j hj => by rw [hdrop j hj]; exact (steps j hj).descent)

/-- Миграция `Hagi.Cert.delta_telescope` (остаточная форма):
сводится к `telescope_sum_floor_le` с полом `0`. -/
theorem delta_telescope' (n : ℕ) (t : ℕ → S) (deltaLevel : S → ℝ)
    (dl : ℕ → ℝ)
    (hTn : 0 ≤ deltaLevel (t n))
    (steps : ∀ j, j < n → Hagi.Cert.CertStepDelta M obl deltaLevel
      (t j) (t (j + 1)))
    (hdrop : ∀ j, ∀ h : j < n, dl j = (steps j h).delta) :
    ∑ j ∈ Finset.range n, dl j ≤ deltaLevel (t 0) := by
  simpa using telescope_sum_floor_le 0
    (f := fun k => deltaLevel (t k)) (c := dl)
    (fun j hj => by rw [hdrop j hj]; exact (steps j hj).delta_next.le)
    hTn

/-! ## Cert.StepGen -/

/-- Миграция `Hagi.Cert.trajectory_telescope_gen_bounded`
(bounded-цепь до горизонта + скалярный ledger; `telescope_le_sub`). -/
theorem trajectory_telescope_gen_bounded' (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S) (drop : ℕ → ℝ)
    (steps : ∀ j, j < n → Hagi.Cert.CertStepGenBounded M obl deltaLevel
      (t j) (t (j + 1)))
    (hdrop : ∀ j, ∀ h : j < n, drop j = (steps j h).drop) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, drop j :=
  telescope_le_sub
    (f := fun k => M.objective (t k)) (c := drop)
    (fun j hj => by rw [hdrop j hj]; exact (steps j hj).descent)

/-- Миграция `Hagi.Cert.delta_telescope_gen` (остаточная форма;
`telescope_sum_floor_le`). -/
theorem delta_telescope_gen' (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S) (dl : ℕ → ℝ)
    (hTn : 0 ≤ deltaLevel (t n))
    (steps : ∀ j, j < n → Hagi.Cert.CertStepGen M obl deltaLevel
      (t j) (t (j + 1)))
    (hdrop : ∀ j, ∀ h : j < n, dl j = (steps j h).delta) :
    ∑ j ∈ Finset.range n, dl j ≤ deltaLevel (t 0) := by
  simpa using telescope_sum_floor_le 0
    (f := fun k => deltaLevel (t k)) (c := dl)
    (fun j hj => by rw [hdrop j hj]; exact (steps j hj).delta_next.le)
    hTn

/-! ## Unified.StepProvider -/

/-- Миграция `Hagi.Unified.StepProvider.telescope`: окно оракула
ограничено горизонтом `n`, drops — явный ledger; сводится к
`telescope_le_sub`. -/
theorem provider_telescope'
    {deltaLevel : S → ℝ}
    (P : Hagi.Unified.StepProvider.StepProvider M obl deltaLevel)
    (n : ℕ) (t : ℕ → S) (drop : ℕ → ℝ)
    (steps : ∀ j, j < n + 1 →
      Hagi.Unified.StepProvider.StepProposal M obl deltaLevel (t j))
    (_hsome : ∀ j (hj : j < n), P.step (t j)
      = some (steps j (Nat.lt_succ_of_lt hj)))
    (hnext : ∀ j (hj : j < n),
      (steps j (Nat.lt_succ_of_lt hj)).next = t (j + 1))
    (hdrop : ∀ j (hj : j < n), drop j
      = (steps j (Nat.lt_succ_of_lt hj)).cert.drop) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, drop j := by
  refine telescope_le_sub
    (f := fun k => M.objective (t k)) (c := drop)
    (fun j hj => ?_)
  have hcert := (steps j (Nat.lt_succ_of_lt hj)).cert.descent
  have hnext' : M.objective
      ((steps j (Nat.lt_succ_of_lt hj)).next)
      = M.objective (t (j + 1)) :=
    congrArg M.objective (hnext j hj)
  rw [hnext'] at hcert
  rw [hdrop j hj]
  exact hcert

end Hagi.Unified.TelescopeInstances
