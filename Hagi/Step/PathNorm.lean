/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# PathNorm — weight decay как group-lasso на нейроны

Liu, Zhang, Shenouda et al., «PathProx», arXiv:2210.03069: для ReLU-сетей
регуляризация `Σ‖w‖²` с точностью до калибровки пары `(|w_in|, |w_out|)`
эквивалентна `Σ 2·|w_in|·|w_out|` — path norm, group-lasso по нейронам,
который обнуляет нейрон целиком (neural heat death, arXiv:2611.27889). В
HAGI-Prime пары `(W_up,:,j, W_down,j,:)`, `(B_u, B_v)`, `(W_kv_down, [W_uk, W_uv])`
подпадают под это напрямую.

* `penalty_eq_path_norm` — в сбалансированной точке (`a² = b²`) penalty равен
  `2|ab|`: gauge balance делает decay «чистым» path-lasso;
* `path_norm_shrinks` — decay `(1 − lam)` на обоих факторах сжимает path norm
  как `(1 − lam)^(2t)`;
* `prox_kills_small`, `prox_threshold` — prox-шаг по path norm: `s ≤ lam`
  обнуляет нейрон за один шаг, иначе `s ← s − lam`.
-/

namespace Hagi.Step.PathNorm
/-- При балансе (`|a| = |b| = √s`) penalty `a² + b²` равен `2s`, где `s = |ab|` —
path norm нейрона (PathProx, Liu et al. 2022): weight decay для ReLU-пары
действует как group-lasso `2·Σ s_j` на нейроны, а не на отдельные веса. -/
theorem penalty_eq_path_norm (a b : ℝ) (h : a ^ 2 = b ^ 2) :
    a ^ 2 + b ^ 2 = 2 * |a * b| := by
  have hab : |a| = |b| := by
    apply (sq_eq_sq₀ (abs_nonneg a) (abs_nonneg b)).mp
    rw [sq_abs, sq_abs]; exact h
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  rw [abs_mul, ← hab]
  nlinarith [sq_nonneg b, abs_nonneg b]
/-- Затухание `(1 − lam)` на обоих факторах пары сжимает path norm как
`(1 − lam)^(2t)`: произведение — квадрат шага, поэтому нейрон с малым `s`
достигает нуля быстрее, чем отдельный вес. -/
theorem path_norm_shrinks (lam a b : ℝ) (t : ℕ) :
    ((1 - lam) ^ t * a) * ((1 - lam) ^ t * b) = (1 - lam) ^ (2 * t) * (a * b) := by
  rw [show (1 - lam) ^ (2 * t) = (1 - lam) ^ t * (1 - lam) ^ t by rw [two_mul, pow_add]]
  ring
/-- Prox-шаг по path norm (порог `lam`): нейрон с `s ≤ lam` обнуляется за один
шаг (удаление), иначе `s ← s − lam` — soft-threshold, точное решение
`min ½(s − s₀)² + lam·s`. -/
theorem prox_kills_small (s lam : ℝ) (hs : s ≤ lam) :
    (s - lam) + |s - lam| = 0 := by
  rw [abs_of_nonpos (sub_nonpos.mpr hs)]; ring
theorem prox_threshold (s lam : ℝ) (hs : lam ≤ s) :
    (s - lam) + |s - lam| = 2 * (s - lam) := by
  rw [abs_of_nonneg (sub_nonneg.mpr hs)]; ring

end Hagi.Step.PathNorm
