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
/-- ОБРАТНАЯ СТОРОНА NFL: на ИЗБЫТОЧНЫХ данных (таргет
константен) прореживание БЕСПЛАТНО — предиктор-константа
ошибается нуль на любой выброшенной точке. Разрыв с
pruning_nfl: цена pruning возникает только на
информативных точках. -/
theorem pruning_free_for_constant (c : ℝ)
    (kept : Finset ℕ) (p : ℕ)
    (g : (ℕ → ℝ) → ℝ)
    (hg : ∀ y : ℕ → ℝ, (∀ i ∈ kept, y i = c) → g y = c) :
    |g (fun _ => c) - (fun _ => c) p|
      + |g (fun i => if i = p then c else c)
          - (fun i => if i = p then c else c) p| = 0 := by
  have h1 : g (fun _ => c) = c := hg _ (fun i _ => rfl)
  have h2 : g (fun i => if i = p then c else c) = c := by
    apply hg
    intro i _
    simp
  rw [h1, h2]
  simp

/-- ВОССТАНОВЛЕНИЕ ПРУНЕННОЙ ТОЧКИ: если таргет — L-липшицева
функция f, а выброшенная точка t лежит между соседними
kept-точками с расстоянием ≤ δ, то значение в t
восстанавливается из соседа с ошибкой ≤ L·δ. Плотная сетка
на гладких таргетах делает pruning почти бесплатным —
дополняет pruning_nfl (ломается на крутых таргетах). -/
theorem pruning_recovery_bound (f : ℝ → ℝ) (t x0 x1 : ℝ)
    (L δ : ℝ)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hl : x0 ≤ t) (hr : t ≤ x1)
    (hδ : |x1 - x0| ≤ δ) :
    |f t - f x0| ≤ L * δ := by
  have hL : (0:ℝ) ≤ L := by
    have h1 : |f 0 - f 1| ≤ L := by
      simpa using hlip 0 1
    have h2 : (0:ℝ) ≤ |f 0 - f 1| := abs_nonneg _
    linarith
  have h1 : |f t - f x0| ≤ L * |t - x0| := hlip t x0
  have h2 : |t - x0| = t - x0 := abs_of_nonneg (by linarith)
  have h3 : t - x0 ≤ |x1 - x0| := by
    have : x0 ≤ x1 := le_trans hl hr
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h4 : |x1 - x0| ≤ δ := hδ
  calc |f t - f x0| ≤ L * |t - x0| := h1
    _ = L * (t - x0) := by rw [h2]
    _ ≤ L * |x1 - x0| := mul_le_mul_of_nonneg_left h3 hL
    _ ≤ L * δ := mul_le_mul_of_nonneg_left h4 hL

end Hagi.Pretraining
