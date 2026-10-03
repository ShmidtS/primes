/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.SelfDevelopment
set_option linter.style.header false

/-!
# P1: DirectionalParetoController — направленный Pareto-контроллер

Аудит R120 (SWE-2 Extended, anishlk.com/swe-2-extended): выбор
действия по `max gain/cost` неявно фиксирует одну точку зрения —
«максимизировать прирост на единицу ресурса». Нужен контроллер,
который выбирает НАПРАВЛЕНИЕ движения по Pareto frontier:
α=1 — прирост capability при сохранении cost, α=0 — снижение
cost при сохранении performance, промежуточные — баланс.

**Формализация** (векторная, n координат; SWE-2 — случай n=2):

* `u a i` — нормированный прирост i-й координаты действием a
  (capability-гейн, минус wall-clock, минус risk, ...).
* `omega i > 0` — желаемое направление (Σω = 1 не существенно).
* `dirTau u omega a` — максимальный сбалансированный уровень
  τ: `∀ i, u(a,i) ≥ ω_i·τ` (sup'-форма `−sup'_i(−u a i/ω i)`).

**Теоремы (§7 аудита):**

1. `dirTau_le`, `le_dirTau`, `dirTau_char` — эквивалентность
   min-формы и системы неравенств.
2. `pareto_validity` — τ(a) > 0 ⇒ a строго улучшает каждую
   координату (направленный Pareto-шаг).
3. `dir_controller_find` — completeness: ∃ a₀ с τ(a₀) ≥ g ⇒
   argmax-τ контроллер выбирает a* с τ(a*) ≥ g (направленный
   аналог `self_development_find` R118).
4. `noisy_pareto_select` — при поэлементной ε_i-концентрации
   измерений (R114): argmax по измеренным даёт истинный
   τ(a*) ≥ τ(a₀) − 2·max_i(ε i/ω i).

**Честные границы**: (1) оценка локального наклона frontier —
отдельная сертифицируемая задача (audit §14); (2) hard-
констрейнты (ΔQ_j ≥ −ε_j, ΔR ≤ ε_R, B ≥ 0) — safe-фильтр ДО
контроллера (компонуется с `safeCandidates` R118).
-/

open Finset

namespace Hagi

variable {A : Type} [Fintype A] [Nonempty A]

section Directional

variable {n : ℕ} [Nonempty (Fin n)]

/-- Направленный сбалансированный уровень действия a:
максимальное τ с `∀ i, u(a,i) ≥ ω_i·τ` (sup'-форма). -/
noncomputable def dirTau (u : A → Fin n → ℝ) (omega : Fin n → ℝ)
    (a : A) : ℝ :=
  -(Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty
    (fun i => -(u a i / omega i))

/-- Координатная оценка: dirTau ≤ u a j / ω j. -/
theorem dirTau_le (u : A → Fin n → ℝ) (omega : Fin n → ℝ) (a : A)
    (j : Fin n) :
    dirTau u omega a ≤ u a j / omega j := by
  have h := Finset.le_sup' (fun i => -(u a i / omega i))
    (Finset.mem_univ j)
  unfold dirTau
  linarith

/-- Верхняя характеризация: (∀ i, τ ≤ u a i / ω i) ⇒ τ ≤ dirTau. -/
theorem le_dirTau (u : A → Fin n → ℝ) (omega : Fin n → ℝ) (a : A)
    (tau : ℝ) (h : ∀ i, tau ≤ u a i / omega i) :
    tau ≤ dirTau u omega a := by
  have hsup : (Finset.univ : Finset (Fin n)).sup'
      Finset.univ_nonempty (fun i => -(u a i / omega i)) ≤ -tau :=
    Finset.sup'_le Finset.univ_nonempty (fun i => -(u a i / omega i))
      (fun i _ => by
        have := h i
        linarith)
  unfold dirTau
  linarith

/-- Эквивалентность min-формы и системы неравенств (audit §7,
теорема 1): τ ≤ dirTau a ↔ (∀ i, τ·ω i ≤ u a i) при ω > 0. -/
theorem dirTau_char (u : A → Fin n → ℝ) (omega : Fin n → ℝ)
    (hw : ∀ i, 0 < omega i) (a : A) (tau : ℝ) :
    tau ≤ dirTau u omega a ↔ ∀ i, tau * omega i ≤ u a i := by
  constructor
  · intro h i
    have hle := dirTau_le u omega a i
    rw [le_div_iff₀ (hw i)] at hle
    exact le_trans (mul_le_mul_of_nonneg_right h (hw i).le) hle
  · intro h
    exact le_dirTau u omega a tau (fun i => by
      rw [le_div_iff₀ (hw i)]
      exact h i)

/-- **Pareto validity** (audit §7, теорема 2): если
направленный уровень положителен, действие строго улучшает
каждую координату. -/
theorem pareto_validity (u : A → Fin n → ℝ) (omega : Fin n → ℝ)
    (hw : ∀ i, 0 < omega i) (a : A)
    (hpos : 0 < dirTau u omega a) (i : Fin n) :
    0 < u a i := by
  have h1 := dirTau_le u omega a i
  rw [le_div_iff₀ (hw i)] at h1
  have h2 : 0 < omega i * dirTau u omega a := mul_pos (hw i) hpos
  linarith

/-- **Controller completeness** (audit §7, теорема 3):
направленный аналог `self_development_find` — если существует
действие с направленным уровнем ≥ g, argmax-τ контроллер
выбирает действие с уровнем ≥ g. -/
theorem dir_controller_find (u : A → Fin n → ℝ) (omega : Fin n → ℝ)
    (a₀ : A) (g : ℝ)
    (hg : g ≤ dirTau u omega a₀) :
    ∃ a', g ≤ dirTau u omega a' ∧
      ∀ a, dirTau u omega a ≤ dirTau u omega a' := by
  obtain ⟨a', _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun a => dirTau u omega a)
      Finset.univ_nonempty
  exact ⟨a', le_trans hg (hmax a₀ (Finset.mem_univ a₀)),
    fun a => hmax a (Finset.mem_univ a)⟩

/-- Устойчивость sup'-формы: если f i ≤ g i + E поэлементно,
то sup' f ≤ sup' g + E. -/
private theorem sup_stab {m : ℕ} [Nonempty (Fin m)] (f g : Fin m → ℝ)
    (E : ℝ) (h : ∀ i, f i ≤ g i + E) :
    (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty f
      ≤ (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty g + E := by
  have h1 : ∀ i, g i ≤ (Finset.univ : Finset (Fin m)).sup'
      Finset.univ_nonempty g :=
    fun i => Finset.le_sup' g (Finset.mem_univ i)
  have hkey : ∀ i, f i ≤ (Finset.univ : Finset (Fin m)).sup'
      Finset.univ_nonempty g + E := by
    intro i
    linarith [h i, h1 i]
  exact Finset.sup'_le Finset.univ_nonempty f (fun i _ => hkey i)

/-- **Noisy Pareto selection** (audit §7, теорема 4): при
поэлементной ε_i-концентрации измеренных приростов û
(|û a i − u a i| ≤ ε i, сертифицируемо R114) argmax по
ИЗМЕРЕННОМУ dirTau даёт истинный уровень
≥ dirTau(a₀) − 2·max_i(ε i/ω i). -/
theorem noisy_pareto_select (u uhat : A → Fin n → ℝ)
    (omega : Fin n → ℝ) (hw : ∀ i, 0 < omega i)
    (eps : Fin n → ℝ)
    (hconc : ∀ a i, |uhat a i - u a i| ≤ eps i)
    (a₀ : A) :
    ∃ a',
      dirTau u omega a₀ - 2 * (Finset.univ : Finset (Fin n)).sup'
          Finset.univ_nonempty (fun i => eps i / omega i)
        ≤ dirTau u omega a' := by
  classical
  set E : ℝ := (Finset.univ : Finset (Fin n)).sup'
    Finset.univ_nonempty (fun i => eps i / omega i) with hE
  have hEle : ∀ i, eps i / omega i ≤ E :=
    fun i => Finset.le_sup' (fun i => eps i / omega i)
      (Finset.mem_univ i)
  have hstabGE : ∀ a, dirTau u omega a ≤ dirTau uhat omega a + E := by
    intro a
    -- −sup_u ≤ −sup_û + E  ⇐  sup_û ≤ sup_u + E
    have h := sup_stab (fun i => -(uhat a i / omega i))
      (fun i => -(u a i / omega i)) E
      (fun i => by
        have hsub : (u a i - uhat a i) / omega i ≤ E := by
          have h1 : (u a i - uhat a i) / omega i ≤ eps i / omega i :=
            (div_le_div_iff₀ (hw i) (hw i)).mpr
              (mul_le_mul_of_nonneg_right
                (by linarith [abs_le.mp (hconc a i) |>.1]) (hw i).le)
          linarith [h1, hEle i]
        have heq : -(uhat a i / omega i) + u a i / omega i
            = (u a i - uhat a i) / omega i := by
          field_simp
          ring
        linarith [heq, hsub])
    unfold dirTau
    linarith
  have hstabLE : ∀ a, dirTau uhat omega a ≤ dirTau u omega a + E := by
    intro a
    -- −sup_û ≤ −sup_u + E  ⇐  sup_u ≤ sup_û + E
    have h := sup_stab (fun i => -(u a i / omega i))
      (fun i => -(uhat a i / omega i)) E
      (fun i => by
        have hsub : (uhat a i - u a i) / omega i ≤ E := by
          have h1 : (uhat a i - u a i) / omega i ≤ eps i / omega i :=
            (div_le_div_iff₀ (hw i) (hw i)).mpr
              (mul_le_mul_of_nonneg_right
                (by linarith [abs_le.mp (hconc a i) |>.2]) (hw i).le)
          linarith [h1, hEle i]
        have heq : -(u a i / omega i) + uhat a i / omega i
            = (uhat a i - u a i) / omega i := by
          field_simp
          ring
        linarith [heq, hsub])
    unfold dirTau
    linarith
  obtain ⟨a', _, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun a => dirTau uhat omega a)
      Finset.univ_nonempty
  have hsel : dirTau uhat omega a₀ ≤ dirTau uhat omega a' :=
    hmax a₀ (Finset.mem_univ a₀)
  refine ⟨a', ?_⟩
  have h1 := hstabGE a₀
  have h2 := hstabLE a'
  linarith

end Directional

end Hagi
