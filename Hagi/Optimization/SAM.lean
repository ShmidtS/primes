import Mathlib

/-!
# SAM (источник №81: Foret et al., "Sharpness-Aware
# Minimization", arXiv 2010.01412)

Минимизация остроты: вместо L(w) оптимизируют
worst-neighbor лосс sam_ρ(L, w) = sup{L(w+ε) : ‖ε‖ ≤ ρ} —
поиск ПЛОСКИХ минимумов (низкая чувствительность к
возмущениям весов = к квантованию/дистилляции).

1. `samW` — супремум лосса на ρ-шаре;
2. `sam_ge` — sam ≥ L(w) (нулевое возмущение в шаре);
3. `sam_mono` — монотонность по ρ (острота растёт
   с окрестностью);
4. `sam_flat` — константный на шаре лосс ⟹ sam = L(w)
   — идеальная плоскость (нулевая острота).
-/

namespace Hagi.Optimization.SAM

variable {k : Type*} [Fintype k]

/-- Евклидова полинорма возмущения (сумма квадратов). -/
noncomputable def norm2 (e : k → ℝ) : ℝ := ∑ i, (e i)^2

/-- ρ-шар возмущений. -/
def ball (rho : ℝ) : Set (k → ℝ) := {e | norm2 e ≤ rho ^ 2}

/-- НУЛЕВОЕ ВОЗМУЩЕНИЕ лежит в шаре при ρ ≥ 0. -/
theorem zero_mem_ball {rho : ℝ} (hr : 0 ≤ rho) :
    (0 : k → ℝ) ∈ ball (k := k) rho := by
  refine Set.mem_setOf.mpr ?_
  have h0 : norm2 (0 : k → ℝ) = 0 := by
    unfold norm2; simp
  rw [h0]
  exact sq_nonneg rho

noncomputable def samW (L : (k → ℝ) → ℝ) (rho : ℝ)
    (w : k → ℝ) : ℝ :=
  sSup (L '' (fun e => w + e) '' ball rho)

/-- sam ≥ L(w): worst-case не хуже текущей точки. -/
theorem sam_ge (L : (k → ℝ) → ℝ) (rho : ℝ) (hr : 0 ≤ rho)
    (w : k → ℝ)
    (hBdd : BddAbove (L '' (fun e => w + e) '' ball rho)) :
    L w ≤ samW L rho w :=
  le_csSup hBdd ⟨w + 0, ⟨0, zero_mem_ball hr, by simp⟩, by simp⟩

/-- ВЛОЖЕНИЕ ШАРОВ: r1 ≤ r2 ⟹ ball r1 ⊆ ball r2. -/
theorem ball_mono {r1 r2 : ℝ} (h : r1 ≤ r2) (hr1 : 0 ≤ r1)
    (hr2 : 0 ≤ r2) : ball (k := k) r1 ⊆ ball (k := k) r2 := by
  intro e he
  unfold ball at he ⊢
  have hsq : r1 ^ 2 ≤ r2 ^ 2 := by nlinarith
  exact le_trans he hsq

/-- МОНОТОННОСТЬ ПО РАДИУСУ: ρ₁ ≤ ρ₂ ⟹ worst-case лосс
монотонно растёт с окрестностью. -/
theorem sam_mono (L : (k → ℝ) → ℝ) (r1 r2 : ℝ)
    (h : r1 ≤ r2) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (w : k → ℝ)
    (hB2 : BddAbove (L '' (fun e => w + e) '' ball r2)) :
    samW L r1 w ≤ samW L r2 w := by
  have hsne : (L '' (fun e => w + e) '' ball r1).Nonempty :=
    ⟨L (w + 0), ⟨w + 0, ⟨0, zero_mem_ball hr1, by simp⟩, by simp⟩⟩
  unfold samW
  refine csSup_le_csSup hB2 hsne ?_
  rintro y ⟨z, ⟨e, he, hez⟩, hyz⟩
  rw [← hez] at hyz
  exact ⟨w + e, ⟨e, ball_mono h hr1 hr2 he, rfl⟩, hyz⟩

/-- ИДЕАЛЬНАЯ ПЛОСКОСТЬ: L постоянна на ρ-шаре ⟹
sam = L(w) — нулевая острота (цель SAM-обучения). -/
theorem sam_flat (L : (k → ℝ) → ℝ) (rho : ℝ) (hr : 0 ≤ rho)
    (w : k → ℝ)
    (hconst : ∀ e ∈ ball rho, L (w + e) = L w)
    (hBdd : BddAbove (L '' (fun e => w + e) '' ball rho)) :
    samW L rho w = L w := by
  have hsne : (L '' (fun e => w + e) '' ball rho).Nonempty :=
    ⟨L (w + 0), ⟨w + 0, ⟨0, zero_mem_ball hr, by simp⟩, by simp⟩⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le hsne ?_
    rintro y ⟨z, ⟨e, he, hez⟩, hyz⟩
    rw [← hez] at hyz
    rw [← hyz, hconst e he]
  · exact sam_ge L rho hr w hBdd

end Hagi.Optimization.SAM
