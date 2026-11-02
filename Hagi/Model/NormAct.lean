/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Model.RMSNorm
import Hagi.Architecture.AlignedMerge

/-!
# Нормировки и активации (объединённые)

PreNorm, QKNorm, SwiGLU. Имена сохранены.
-/

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

/-!
# QK-Norm: ограниченность логитов внимания (источник №36)

Источник №36: Henry, Dmitriev, et al., "Query-Key
Normalization for Transformers" (arXiv 2002.10872).
Нормировка запросов и ключей (RMSNorm/LayerNorm на q, k)
устраняет attention-спайки: логиты scores = q·k ограничены
КОНСТАНТОЙ, не зависящей от масштаба входов — вместо
неограниченного роста при обучении.

Формализованное ядро (строгое):
- `qk_logit_bound`: для нормированных q, k
  (rnVec, единичный RMS) |q·k| ≤ n — логит ограничен
  размерностью головы (Cauchy–Schwarz через dotCS),
  масштаб входов исключён.
-/

namespace Hagi.Model.QKNorm

open Finset

variable {n : ℕ}

/-- ЯДРО №36: после RMS-норм q и k логит ограничен n:
attention-спайки исключены константой размерности. -/
theorem qk_logit_bound (q k : Fin n → ℝ)
    (hq : Hagi.Model.RMSNorm.ms q ≠ 0)
    (hk : Hagi.Model.RMSNorm.ms k ≠ 0) :
    |Hagi.Model.RMSNorm.rnVec q ⬝ᵥ Hagi.Model.RMSNorm.rnVec k| ≤ (n : ℝ) := by
  have hconv : ∀ x : Fin n → ℝ,
      (x ⬝ᵥ x) = ∑ i, (x i) ^ 2 := fun x => by
    unfold dotProduct
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hq2 : (Hagi.Model.RMSNorm.rnVec q ⬝ᵥ Hagi.Model.RMSNorm.rnVec q)
      = (n : ℝ) := (hconv _).trans (Hagi.Model.RMSNorm.rn_unit_rms q hq)
  have hk2 : (Hagi.Model.RMSNorm.rnVec k ⬝ᵥ Hagi.Model.RMSNorm.rnVec k)
      = (n : ℝ) := (hconv _).trans (Hagi.Model.RMSNorm.rn_unit_rms k hk)
  have hcs := Hagi.Architecture.dotCS
    (Hagi.Model.RMSNorm.rnVec q) (Hagi.Model.RMSNorm.rnVec k)
  rw [hq2, hk2] at hcs
  have hd := hcs
  set d : ℝ := Hagi.Model.RMSNorm.rnVec q ⬝ᵥ Hagi.Model.RMSNorm.rnVec k with hdd
  have habs2 : |d| ^ 2 = d ^ 2 := sq_abs d
  have hnpos : 0 ≤ ((n : ℝ) * (n : ℝ)) := by positivity
  nlinarith [habs2, hd, abs_nonneg d, sq_nonneg ((n : ℝ))]

/-- Softmax-вероятность внимания по логитам. -/
noncomputable def attP {n : ℕ} (l : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (l i) / ∑ j, Real.exp (l j)

/-- УРОВЕНЬ 2 №36: если ВСЕ попарные логит-разности
ограничены D (после QK-норм D = 2n), то отношение любых
двух вероятностей внимания ≤ e^D — полная сатурация
(p → 1) СТРУКТУРНО исключена: каждый токен получает
не менее e^{−D} доли внимания. -/
theorem qk_no_saturation {n : ℕ} (l : Fin n → ℝ)
    (i j : Fin n) (hgap : l i - l j ≤ 2 * ((n : ℝ)))
    (hsum : ∑ k, Real.exp (l k) ≠ 0) :
    attP l i / attP l j ≤ Real.exp (2 * ((n : ℝ))) := by
  unfold attP
  have hS : (∑ k, Real.exp (l k)) ≠ 0 := hsum
  field_simp
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Hagi.Model.QKNorm

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
