import Mathlib

/-!
# PreNorm — стабильность pre-norm residual-блока
# (источник №66: Wang et al., DeepNet 2203.04627;
# математическое ядро: pre-norm сохраняет ограниченность
# residual-потока)

Ключевое преимущество pre-norm (x + f(LN x)) перед
post-norm (LN(x + f(x))): residual-поток НЕ нормализуется,
но при ограниченной f норма выхода растёт не быстрее
аддитивно — по глубине L: ‖x_L‖ ≤ ‖x_0‖ + L·B. Отсюда
глубина не взрывает норму (основа стабильности DeepNet).
-/

namespace Hagi.Model.PreNorm

variable {X : Type*} [NormedAddCommGroup X]

/-- Pre-norm residual-шаг: x ↦ x + f x (f уже применена к
нормализованному входу; ограничения — на f как целое). -/
def preNormStep (x : X) (fx : X) : X := x + fx

/-- ИСТОЧНИК №66, УРОВЕНЬ 1: АДДИТИВНЫЙ РОСТ НОРМЫ — один
pre-norm шаг растит норму не более чем на ‖f‖
(неравенство треугольника). -/
theorem preNorm_step_bound (x fx : X) :
    ‖preNormStep x fx‖ ≤ ‖x‖ + ‖fx‖ := by
  unfold preNormStep
  exact norm_add_le x fx

/-- УРОВЕНЬ 2: ПО ГЛУБИНЕ L — L последовательных pre-norm
шагов с ограниченными f (‖f_t‖ ≤ B) дают
‖x_L‖ ≤ ‖x_0‖ + L·B: глубина НЕ взрывает норму
(экспоненциальный рост невозможен; основа
стабильности глубоких pre-norm сетей). -/
theorem preNorm_depth_bound (x0 : X) (fs : ℕ → X)
    (B : ℝ) (_hB : 0 ≤ B) (hfs : ∀ t, ‖fs t‖ ≤ B)
    (L : ℕ) :
    ‖(List.range L).foldl (fun acc t =>
      preNormStep acc (fs t)) x0‖ ≤ ‖x0‖ + L * B := by
  induction L with
  | zero => simp
  | succ k ih =>
      have hk1 : ((k+1):ℝ) * B = (k:ℝ) * B + B := by push_cast; ring
      have hstep := preNorm_step_bound
        ((List.range k).foldl (fun acc t =>
          preNormStep acc (fs t)) x0) (fs k)
      have h2 : (‖fs k‖:ℝ) ≤ B := hfs k
      have hfold : (List.range (k + 1)).foldl (fun acc t =>
          preNormStep acc (fs t)) x0
          = preNormStep ((List.range k).foldl (fun acc t =>
            preNormStep acc (fs t)) x0) (fs k) := by
        simp [List.range_succ, List.foldl_append]
      rw [hfold]
      push_cast
      linarith [hstep, ih, h2, hk1]

end Hagi.Model.PreNorm
