/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Softmax-weighted error damping

For weights `p i ≥ 0`, the deviation of the weighted output
`∑ i, p i • (v i + e i)` from the exact output `∑ i, p i • v i` is
bounded by the weighted average `∑ i, p i * ‖e i‖` of the error
norms (`attention_error_damped_sum`), by their maximum when `p` is
a probability distribution (`attention_error_damped`), and by any
uniform bound `M` (`attention_error_damped'`).
-/

namespace Hagi

/-- Error damping, weighted form: the deviation of the softmax-weighted
output `∑ i, p i • (v i + e i)` from the exact output `∑ i, p i • v i` is
bounded by the weighted average `∑ i, p i * ‖e i‖` of the error norms. -/
theorem attention_error_damped_sum {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ι → ℝ) (v e : ι → E)
    (hp : ∀ i, 0 ≤ p i) :
    ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ ∑ i, p i * ‖e i‖ := by
  have key : (∑ i, p i • (v i + e i)) - ∑ i, p i • v i = ∑ i, p i • e i := by
    rw [← Finset.sum_sub_distrib]
    simp [add_sub_cancel_left]
  rw [key]
  calc ‖∑ i, p i • e i‖ ≤ ∑ i, ‖p i • e i‖ := norm_sum_le Finset.univ (fun i => p i • e i)
    _ ≤ ∑ i, p i * ‖e i‖ :=
        Finset.sum_le_sum fun i _ =>
          le_of_eq (by rw [norm_smul, Real.norm_of_nonneg (hp i)])

/-- Error damping, max form: if p is a probability distribution, the
deviation of the softmax-weighted output from the exact output is at
most the largest individual error norm `‖e i‖`. -/
theorem attention_error_damped {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ι → ℝ) (v e : ι → E)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤
      Finset.univ.sup'
        (by
          by_contra h
          have h0 : ∑ i, p i = 0 :=
            Finset.sum_eq_zero fun i _ => (h ⟨i, Finset.mem_univ i⟩).elim
          rw [h0] at hp1
          exact zero_ne_one hp1)
        fun i => ‖e i‖ := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    have h0 : ∑ i, p i = 0 :=
      Finset.sum_eq_zero fun i _ => (h ⟨i, Finset.mem_univ i⟩).elim
    rw [h0] at hp1
    exact zero_ne_one hp1
  calc ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ ∑ i, p i * ‖e i‖ :=
        attention_error_damped_sum p v e hp
    _ ≤ ∑ i, p i * Finset.univ.sup' hne (fun i => ‖e i‖) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => ‖e i‖) (Finset.mem_univ i)) (hp i)
    _ = Finset.univ.sup' hne (fun i => ‖e i‖) := by
        rw [← Finset.sum_mul, hp1, one_mul]

/-- Error damping, uniform-bound form: if every stored entry has
quantization error at most `M`, the deviation of the softmax-weighted
output from the exact output is at most `M`. -/
theorem attention_error_damped' {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ι → ℝ) (v e : ι → E)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (M : ℝ) (hM : ∀ i, ‖e i‖ ≤ M) :
    ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ M := by
  calc ‖(∑ i, p i • (v i + e i)) - ∑ i, p i • v i‖ ≤ ∑ i, p i * ‖e i‖ :=
        attention_error_damped_sum p v e hp
    _ ≤ ∑ i, p i * M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp i)
    _ = M := by rw [← Finset.sum_mul, hp1, one_mul]

end Hagi
