import Mathlib

/-!
# LoRA: низкоранговая адаптация (источник №35)

Источник №35: Hu et al., "LoRA: Low-Rank Adaptation of
Large Language Models" (arXiv 2106.09685). Адаптация
ΔW = B·A с рангом r ≪ min(m,n): обучается m·r + n·r
параметров вместо m·n — переиспользование замороженного
базового W.

Формализованное ядро (строгое):
- `lora_out`: выход адаптированной модели
  (W + B·A)·x = W·x + B·(A·x) — адаптация идёт через
  НИЗКОРАНГОВЫЙ канал B(A(·));
- `lora_kernel_preserved`: если A·x = 0 (адаптер не видит
  x), поведение модели НЕ МЕНЯЕТСЯ:
  (W + B·A)·x = W·x — LoRA сохраняет базу на всём, что
  вне охвата адаптера (аналог GPM zero-forgetting);
- `lora_param_saving`: при r ≤ mn/(m+n) число обучаемых
  параметров (m+n)·r не превосходит m·n — экономия против
  полного fine-tuning.
-/

namespace Hagi.Model.LoRA

open Matrix

variable {m n k : ℕ}

/-- Выход адаптированной модели. -/
theorem lora_out (W : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ) :
    (W + B * A) *ᵥ x = W *ᵥ x + B *ᵥ (A *ᵥ x) := by
  rw [add_mulVec]
  congr 1
  exact (mulVec_mulVec x B A).symm

/-- ЯДРО №35: адаптер не видит x ⟹ поведение неизменно. -/
theorem lora_kernel_preserved (W : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ)
    (hAx : A *ᵥ x = 0) :
    (W + B * A) *ᵥ x = W *ᵥ x := by
  rw [lora_out W B A x, hAx]
  simp

/-- Экономия параметров: (m+n)·r ≤ m·n при малом ранге. -/
theorem lora_param_saving (m n r : ℕ)
    (hr : (m + n : ℕ) * r ≤ m * n) :
    (m * r + n * r : ℕ) ≤ m * n := by
  have hsplit : m * r + n * r = (m + n) * r := by ring
  omega

end Hagi.Model.LoRA
