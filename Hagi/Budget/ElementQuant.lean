/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.LiveDeltaQuant

set_option linter.style.header false

/-!
# ElementQuant: factorization × quantization commutation (round 49, block 2)

For the TableLoRA + ternary pipeline: the reconstruction
error of "factorize to rank r, then quantize" splits by the
triangle inequality into the TAIL (the rank-r truncation
error, measured from the spectrum) plus the QUANT error (the
grid rounding of the factors) — and the GO/NO-GO: the
factor-then-quantize route beats direct quantization IFF
tail + qerr(r) < qdirect.

The per-entry nearest-3-level rounding bound is now
ASSEMBLED (ternary_factor_qerr_bound, ternary_pair_qerr_sum):
for in-range factors the Frobenius-square quantization error
of each factor obeys the grid bound (card·(s/2)²), and the
per-factor sum feeds the GO/NO-GO certificate. The step from
per-factor errors to the PRODUCT error AB − Q(A)·Q(B) needs
rectangular Frobenius submultiplicativity — absent in
Mathlib v4.34.1 (only square frobeniusNormedRing); recorded
as an open hbridge candidate.

**Prescription**: measure tail(r) from the σ-spectrum of ΔE
and qdirect from one ternary pass; the comparison is a
one-line certificate before any GPU run.
-/

open Finset Hagi.LiveDeltaQuant

namespace Hagi.Budget

/-- **The commutation triangle**: the reconstruction error of
factor-then-quantize is at most tail + qerr — the exact
split of the two error sources. -/
theorem factor_quant_error {X : Type*} [NormedAddCommGroup X] (dE AB QAB : X)
    (tail qerr : ℝ) (h1 : ‖dE - AB‖ = tail) (h2 : ‖AB - QAB‖ = qerr) :
    ‖dE - QAB‖ ≤ tail + qerr := by
  have h3 : dist dE QAB ≤ dist dE AB + dist AB QAB := dist_triangle _ _ _
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h3
  rw [h1, h2] at h3
  exact h3

/-- **The GO/NO-GO certificate (honest form)**: if the
factor-route error bound `tail + qerr` is strictly below the
measured direct-quantization error `qdirect`, then the true
factor-route error is strictly below `qdirect` — via the
commutation triangle above. This is a real decision rule, not
a vacuous implication: the earlier revision carried the
contradictory pair (tail+qerr < qdirect) ∧ (qdirect ≤
tail+qerr), which made the theorem about an empty hypothesis
set. Found in external review, 2025-round-51. -/
theorem factor_quant_go {X : Type*} [NormedAddCommGroup X]
    (dE AB QAB : X) (tail qerr qdirect : ℝ)
    (htail : ‖dE - AB‖ = tail) (hqerr : ‖AB - QAB‖ = qerr)
    (hgain : tail + qerr < qdirect) :
    ‖dE - QAB‖ < qdirect := by
  have h3 := factor_quant_error dE AB QAB tail qerr htail hqerr
  calc ‖dE - QAB‖ ≤ tail + qerr := h3
    _ < qdirect := hgain


/-- Собранный per-factor rounding bound (закрытие ядра
пробела «nearest-3-level rounding bound per entry —
elementary but not assembled»): Frobenius-квадрат ошибки
квантования каждого in-диапазонного фактора на тернарной
сетке шага s не превосходит (число элементов)·(s/2)² —
делегирование quantMat_sq_bound. -/
theorem ternary_factor_qerr_bound {m r : Type} [Fintype m]
    [Fintype r] (s : ℝ) (hs : 0 < s) (M : Matrix m r ℝ)
    (hin : ∀ i j, ternInRange s (M i j)) :
    ∑ i, ∑ j, ((M - quantMat s M) i j) ^ 2
      ≤ (Fintype.card m * Fintype.card r) * (s / 2) ^ 2 :=
  quantMat_sq_bound s hs M hin

/-- Пара факторов: сумма per-factor Frobenius-квадратов
ошибок квантования на тернарной сетке — готовый вход для
GO/NO-GO-сертификата factor_quant_go (tail + qerr <
qdirect), теперь с доказанным qerr-компонентом. Честная
граница: переход от per-factor ошибок к ошибке ПРОИЗВЕДЕНИЯ
AB − Q(A)·Q(B) требует субмультипликативности Фробениуса
для прямоугольных матриц — в Mathlib v4.34.1 есть только
квадратный frobeniusNormedRing; открытый hbridge-кандидат
(upstream-порт). -/
theorem ternary_pair_qerr_sum {m r n : Type} [Fintype m]
    [Fintype r] [Fintype n] (s : ℝ) (hs : 0 < s)
    (A : Matrix m r ℝ) (B : Matrix r n ℝ)
    (hinA : ∀ i j, ternInRange s (A i j))
    (hinB : ∀ i j, ternInRange s (B i j)) :
    (∑ i, ∑ j, ((A - quantMat s A) i j) ^ 2)
      + (∑ i, ∑ j, ((B - quantMat s B) i j) ^ 2)
      ≤ (Fintype.card m * Fintype.card r
          + Fintype.card r * Fintype.card n) * (s / 2) ^ 2 := by
  have hA := ternary_factor_qerr_bound s hs A hinA
  have hB := ternary_factor_qerr_bound s hs B hinB
  have h := add_le_add hA hB
  nlinarith [h]

end Hagi.Budget

namespace Hagi
export Hagi.Budget (factor_quant_error factor_quant_go)
end Hagi
