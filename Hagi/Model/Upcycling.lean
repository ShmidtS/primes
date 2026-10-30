import Mathlib

/-!
# Sparse Upcycling (источник №50)

Источник №50: Komatsuzaki et al., "Sparse Upcycling:
Training Mixture-of-Experts from Dense Checkpoints"
(arXiv 2210.06264). MoE инициализируется из dense-модели:
эксперты — копии FFN, роутер стартует равномерно: начальная
ФУНКЦИЯ модели сохраняется (переиспользование обучения).

Формализованное ядро (строгое):
- `upcycle_preserves`: если все эксперты — копии dense-FFN
  (f i = f) и роутер равномерен (P i = 1/n), то MoE-выход
  ∑ P i * f i = f — upcycling НЕ МЕНЯЕТ функцию модели в
  стартовой точке (вся предобученная функция наследуется).
-/

namespace Hagi.Model.Upcycling

open Finset

variable {n : ℕ}

/-- Равномерный роутер + идентичные эксперты сохраняют
dense-функцию. -/
theorem upcycle_preserves (fd : ℝ) (f : Fin n → ℝ)
    (hf : ∀ i, f i = fd) (_hn : 0 < n) :
    ∑ i, (1 / (n : ℝ)) * f i = fd := by
  have hconv : ∀ i ∈ Finset.univ,
      (1 / (n : ℝ)) * f i = (1 / (n : ℝ)) * fd :=
    fun i _ => by rw [hf i]
  rw [Finset.sum_congr rfl hconv, ← Finset.mul_sum,
    Finset.sum_const]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [Finset.card_univ, Fintype.card_fin]
  field_simp

end Hagi.Model.Upcycling
