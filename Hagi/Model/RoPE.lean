import Mathlib

/-!
# RoPE: вращательное позиционное кодирование (источник №24)

Источник №24: Su et al., "RoFormer" (arXiv 2104.09864):
позиционное кодирование вращением (комплексное
представление: 2D-вращение ≅ умножение на e^{iθ}).

Формализованное ядро:
- `rot`: вращение позиции k — (e^{iθ})^k;
- `rot_normSq_one`: единичность вращения (normSq = 1,
  через cos²+sin²);
- `rope_normSq_preserved`: вращение сохраняет normSq
  вектора — позиционное кодирование ИЗОМЕТРИчно: меняется
  только фаза, информация токена не искажается.
-/

namespace Hagi.Model.RoPE

open Complex

/-- Вращение на угол k·θ. -/
noncomputable def rot (k : ℕ) (theta : ℝ) : ℂ :=
  (exp (theta * I)) ^ k

/-- Единичность вращения: normSq (rot k θ) = 1. -/
theorem rot_normSq_one (k : ℕ) (theta : ℝ) :
    normSq (rot k theta) = 1 := by
  have h1 : normSq (exp (theta * I)) = 1 := by
    simp only [Complex.normSq_apply, Complex.exp_re, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    nlinarith [Real.cos_sq_add_sin_sq theta]
  unfold rot
  induction k with
  | zero => simp
  | succ t ih =>
      rw [pow_succ, Complex.normSq_mul, h1, ih, mul_one]

/-- ИЗОМЕТРИЧНОСТЬ: вращение сохраняет normSq вектора —
ядро корректности RoPE (фаза меняется, модуль нет). -/
theorem rope_normSq_preserved (u : ℂ) (k : ℕ) (theta : ℝ) :
    normSq (rot k theta * u) = normSq u := by
  rw [Complex.normSq_mul, rot_normSq_one, one_mul]

end Hagi.Model.RoPE
