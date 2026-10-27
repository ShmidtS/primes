import Mathlib.Tactic

/-!
# DataPruning — no free lunch для прореживания данных

Ядро результата Paul–Santamaria et al. (NeurIPS 2023,
«No Free Lunch Theorems for Data Pruning»; контекст — Sorscher
et al., NeurIPS 2022, «Beyond Neural Scaling Laws»): если
правило прореживания отбрасывает точку p, то любой ученик,
зависящий только от оставшихся данных, НЕ РАЗЛИЧАЕТ два
таргета, согласных на оставшихся точках и расходящихся в p —
сумма ошибок на них ≥ 1. Прореживание не бесплатно.
-/

namespace Hagi.Pretraining

/-- NO FREE LUNCH ДЛЯ PRUNING: ученик g, зависящий только от
значений на kept-подмножестве (hagree), на паре таргетов
y₀ ≡ 0 и y₁ (единица только в выброшенной точке p) ошибается
в сумме не менее чем на 1. -/
theorem pruning_nfl (kept : Finset ℕ) (p : ℕ) (hp : p ∉ kept)
    (g : (ℕ → ℝ) → ℝ)
    (hagree : ∀ y1 y2 : ℕ → ℝ, (∀ i ∈ kept, y1 i = y2 i) →
      g y1 = g y2) :
    |g (fun _ => (0:ℝ)) - (fun _ => (0:ℝ)) p|
      + |g (fun i => if i = p then (1:ℝ) else 0)
          - (fun i => if i = p then (1:ℝ) else 0) p| ≥ 1 := by
  have hsame : g (fun _ => (0:ℝ))
      = g (fun i => if i = p then (1:ℝ) else 0) := by
    apply hagree
    intro i hi
    have hip : i ≠ p := fun h => absurd (h ▸ hi) hp
    simp [hip]
  have hv2 : g (fun i => if i = p then (1:ℝ) else 0)
      = g (fun _ => (0:ℝ)) := hsame.symm
  have e0 : (fun _ => (0:ℝ)) p = (0:ℝ) := rfl
  have e1 : (fun i => if i = p then (1:ℝ) else 0) p = (1:ℝ) := by
    simp
  rw [e1, hv2, e0]
  have htri : ∀ v : ℝ, |v| + |v - 1| ≥ 1 := by
    intro v
    rcases lt_or_ge v 0 with h2 | h2
    · rw [abs_of_nonpos (by linarith : v ≤ 0)]
      rw [abs_of_nonpos (by linarith : v - 1 ≤ 0)]
      linarith
    · rw [abs_of_nonneg h2]
      rcases lt_or_ge v 1 with h3 | h3
      · rw [abs_of_nonpos (by linarith : v - 1 ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - 1)]
        linarith
  simpa using htri (g (fun _ => (0:ℝ)))
end Hagi.Pretraining
