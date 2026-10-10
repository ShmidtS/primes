 /-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.RoPELimit

set_option linter.style.header false

/-!
# RoPEMoments — моменты высокочастотного счёта (Prop 1,
слайс)

Ядро Proposition 1 из «RoPE at the End of Its Rope?»
(arXiv:2609.39929): высокочастотный attention-счёт
S(m) = Σ_n z_n·cos(m·ω_n) при равномерном m ∈ {0..M−1}.

Доказано (ТОЧНЫЕ моментные тождества — редукция Prop 1 к
частотным контрактам окна):
* `rope_mean_sum`: Σ_m S(m) = Σ_n z_n·C(ω_n), где
  C(ω) := Σ_m cos(mω) — среднее = сумма геометрических
  косинус-сумм (обмен сумм);
* `rope_second_moment_sum`: 2·Σ_m S(m)² = Σ_{n,k} z_n z_k·
  [C(ω_n+ω_k) + C(ω_n−ω_k)] — косинусное
  произведение-тождество: ВТОРОЙ момент полностью
  определяется парными фазовыми суммами C.

Смысл: Prop 1-оценки |E[S]| ≤ εU, |Var − U²/2| ≤ εU²
сводятся к контрактам на C (малость геометрических сумм на
высоких частотах — lacunary-условия сертифицированного
окна); моментная структура — точная, без приближений.

Честная граница: сами оценки |C(ω)| — эмпирические
контракты окна; формализованы тождества.
-/

open Finset

namespace Hagi.RoPEMoments

variable (M : ℕ) (omega : Fin M → ℝ) (z : Fin M → ℝ)

/-- Высокочастотный счёт: S(m) = Σ_n z_n cos(m ω_n). -/
noncomputable def ropeScore (m : ℕ) : ℝ :=
  ∑ n, z n * Real.cos (m * omega n)

/-- Косинус-сумма окна: C(ω) := Σ_{m<M} cos(mω). -/
noncomputable def cosSum (w : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M, Real.cos (m * w)

/-- Среднее: Σ_m S(m) = Σ_n z_n·C(ω_n) — обмен сумм. -/
theorem rope_mean_sum :
    ∑ m ∈ Finset.range M, ropeScore M omega z m
      = ∑ n, z n * cosSum M (omega n) := by
  unfold ropeScore cosSum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => (Finset.mul_sum _ _ _).symm

/-- Второй момент: 2·Σ_m S(m)² = Σ_{n,k} z_n z_k·
[C(ω_n+ω_k) + C(ω_n−ω_k)] — косинусное
произведение-тождество (Fintype.sum_mul_sum) + обмены
сумм. -/
theorem rope_second_moment_sum :
    2 * ∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2
      = ∑ n, ∑ k, z n * z k
          * (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) := by
  have hcos2 : ∀ (m : ℕ) (a b : ℝ),
      2 * (Real.cos (m * a) * Real.cos (m * b))
        = Real.cos (m * (a + b)) + Real.cos (m * (a - b)) := by
    intro m a b
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring
  have hpermMini : ∀ (m : ℕ),
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, 2 * (z n * Real.cos (m * omega n))
            * (z k * Real.cos (m * omega k)) := by
    intro m
    rw [sq, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    ring
  have hperm : ∀ m ∈ Finset.range M,
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, z n * z k
            * (Real.cos (m * (omega n + omega k))
              + Real.cos (m * (omega n - omega k))) := by
    intro m _
    rw [hpermMini m]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcos2 m (omega n) (omega k)]
    ring_nf
  unfold ropeScore
  unfold cosSum

  have hcos2 : ∀ (m : ℕ) (a b : ℝ),
      2 * (Real.cos (m * a) * Real.cos (m * b))
        = Real.cos (m * (a + b)) + Real.cos (m * (a - b)) := by
    intro m a b
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring_nf
  have hpermMini : ∀ (m : ℕ),
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, 2 * (z n * Real.cos (m * omega n))
            * (z k * Real.cos (m * omega k)) := by
    intro m
    rw [sq, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    ring_nf
  have hperm : ∀ m ∈ Finset.range M,
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, z n * z k
            * (Real.cos (m * (omega n + omega k))
              + Real.cos (m * (omega n - omega k))) := by
    intro m _
    rw [hpermMini m]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcos2 m (omega n) (omega k)]
    ring_nf
  conv_lhs => rw [Finset.mul_sum]
  have h1 := Finset.sum_congr rfl (fun m hm => hperm m hm)
  rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsplit : ∀ x ∈ Finset.range M,
      z n * z k * (Real.cos (x * (omega n + omega k))
        + Real.cos (x * (omega n - omega k)))
      = z n * z k * Real.cos (x * (omega n + omega k))
        + z n * z k * Real.cos (x * (omega n - omega k)) :=
    fun x _ => mul_add _ _ _
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end Hagi.RoPEMoments
