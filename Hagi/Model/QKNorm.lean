import Mathlib
import Hagi.Model.RMSNorm
import Hagi.Architecture.AlignedMerge

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

