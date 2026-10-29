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


/-- «Внутреннее произведение» RoPE-пары на позициях (m,n):
Re-часть (star w_m·u)·(w_n·v). -/
noncomputable def ropeInner (u v : ℂ) (m n : ℕ) (theta : ℝ) : ℝ :=
  re (star (rot m theta * u) * (rot n theta * v))

/-- Локальная связь: star z * z = normSq z. -/
private theorem star_mul_self (z : ℂ) :
    star z * z = normSq z := by
  have hstar : star z = Complex.mk z.re (-z.im) := rfl
  rw [hstar, Complex.normSq_apply]
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re]
    simp
  · simp only [Complex.mul_im, Complex.ofReal_im]
    simp
    ring

/-- ОТНОСИТЕЛЬНОСТЬ (ядро RoPE, уровень 2): одновременный
сдвиг d обеих позиций НЕ меняет внутреннего произведения —
взаимодействие токенов зависит только от их ВЗАИМНОГО
расположения. star w_d·w_d = 1 (вращение единично) —
d-экспоненты сокращаются. -/
theorem rope_shift_invariant (u v : ℂ) (m n d : ℕ) (theta : ℝ) :
    ropeInner u v (m + d) (n + d) theta
      = ropeInner u v m n theta := by
  have hexp : (exp (theta * I)) ^ (m + d)
      = (exp (theta * I)) ^ m * (exp (theta * I)) ^ d :=
    pow_add _ m d
  have hexp2 : (exp (theta * I)) ^ (n + d)
      = (exp (theta * I)) ^ n * (exp (theta * I)) ^ d :=
    pow_add _ n d
  set W : ℂ := (exp (theta * I)) with hW
  -- единичность вращения d
  have hunit : star (W ^ d) * W ^ d = 1 := by
    have hrd : W ^ d = rot d theta := by rw [hW, rot]
    rw [hrd, star_mul_self, rot_normSq_one]
    norm_num
  unfold ropeInner
  rw [rot, rot, rot, rot, hexp, hexp2]
  simp only [star_mul]
  calc (star u * (star (W ^ d) * star (W ^ m)) * (W ^ n * W ^ d * v)).re
      = ((star u * star (W ^ m) * (W ^ n * v))
          * (star (W ^ d) * W ^ d)).re := by
        apply congrArg Complex.re
        ring
    _ = ((star u * star (W ^ m) * (W ^ n * v)) * 1).re := by
        rw [hunit]
    _ = (star u * star (W ^ m) * (W ^ n * v)).re := by
        simp

end Hagi.Model.RoPE

