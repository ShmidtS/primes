import Mathlib

/-!
# SwiGLU: гейтинг не усиливает норму (источник №26)

Источник №26: Shazeer, "GLU Variants Improve Transformer"
(arXiv 2002.05202). SwiGLU — гейтрованный блок
FFN(x) = Swish(W₁x) ⊙ W₃x — стандарт современных LLM
(PaLM, LLaMA). В отличие от ReLU-MLP, произведение двух
проекций делает нелинейность управляемой гейтом.

Формализованное ядро (строгое):
- swish_abs_le: |Swish(z)| ≤ |z| — сигмоид-гейт ∈ (0,1)
  никогда не УСИЛИВАЕТ активацию (σ(z) ∈ (0,1));
- swiglu_abs_le: |Swish(a)·b| ≤ |a·b| — гейтрованный выход
  ограничен обычным произведением координат: drift-границы
  residual-потока (№22) переносятся на SwiGLU-блоки без
  изменения констант.
-/

namespace Hagi.Model.SwiGLU

open Real

/-- Сигмоида. -/
noncomputable def sig (z : ℝ) : ℝ := 1 / (1 + exp (-z))

/-- Swish-активация: z · σ(z). -/
noncomputable def swish (z : ℝ) : ℝ := z * sig z

/-- SwiGLU-выход: гейт Swish(a) умножает значение b. -/
noncomputable def swiglu (a b : ℝ) : ℝ := swish a * b

/-- Сигмоида строго между 0 и 1. -/
theorem sig_lt_one (z : ℝ) : sig z < 1 := by
  unfold sig
  have h1 : 0 < 1 + exp (-z) := by positivity
  have h2 : 1 < 1 + exp (-z) := by
    have := exp_pos (-z)
    linarith
  exact (div_lt_one h1).2 h2

theorem sig_pos (z : ℝ) : 0 < sig z := by
  unfold sig
  positivity

/-- Гейт не усиливает: |Swish(z)| ≤ |z| (ядро №26). -/
theorem swish_abs_le (z : ℝ) : |swish z| ≤ |z| := by
  unfold swish
  have h : |sig z| ≤ 1 := by
    rw [abs_of_pos (sig_pos z)]
    exact le_of_lt (sig_lt_one z)
  calc |z * sig z| = |z| * |sig z| := abs_mul z (sig z)
    _ ≤ |z| * 1 := mul_le_mul_of_nonneg_left h (abs_nonneg z)
    _ = |z| := mul_one |z|

/-- SwiGLU-выход ограничен произведением входов: гейтинг
не может усилить норму пары (a, b). -/
theorem swiglu_abs_le (a b : ℝ) : |swiglu a b| ≤ |a| * |b| := by
  unfold swiglu
  have h : |swish a| ≤ |a| := swish_abs_le a
  calc |swish a * b| = |swish a| * |b| := abs_mul (swish a) b
    _ ≤ |a| * |b| := mul_le_mul_of_nonneg_right h (abs_nonneg b)

end Hagi.Model.SwiGLU
