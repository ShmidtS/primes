/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.SpikeThreshold

/-!
# STEBias — смещение straight-through-оценки спайкинга

`_spike` (optimal_lm.py): `spike V h = round(h/V)·V`, обратный проход —
тождество (STE). Керас `SPIKE_START = 0.8`: STE включается только на
последних 20% шагов. Истинная производная спайка — 0 почти всюду, поэтому
STE-градиент — градиент тождества; расхождение оценок потери ограничено
Липшицевой оценкой через ошибку округления.

* `spike_l2_error_le` — `‖h − spike V h‖₂² ≤ d·(V/2)²`;
* `spike_loss_shift_le` — для `Lip`-Липшицевой по ℓ₂ потери
  `|ℓ(spike) − ℓ(h)| ≤ Lip·√d·V/2`; адаптивный `V = ‖h‖₁/(d·k)` делает
  смещение `≤ Lip·‖h‖₁/(2k√d)` — убывает с нормой, что и оправдывает
  включение STE в конце обучения.
-/

namespace Hagi.Energy.STEBias
open Finset
open Hagi.Energy.SpikeThreshold
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι]
/-- ℓ₂-ошибка спайкинга: `‖h − spike V h‖₂ ≤ √d · V/2`. -/
theorem spike_l2_error_le (V : ℝ) (hV : 0 < V) (h : ι → ℝ) :
    ∑ i, (h i - spike V h i) ^ 2 ≤ Fintype.card ι * (V / 2) ^ 2 := by
  have h1 : ∀ i, (h i - spike V h i) ^ 2 ≤ (V / 2) ^ 2 := by
    intro i
    have habs : |h i - round (h i / V) * V| ≤ V / 2 := spike_pointwise V hV (h i)
    obtain ⟨hlo, hhi⟩ := abs_le.1 habs
    have he : h i - spike V h i = h i - round (h i / V) * V := rfl
    rw [he]
    nlinarith [sq_nonneg (h i - round (h i / V) * V + V / 2), sq_nonneg (h i - round (h i / V) * V - V / 2)]
  calc ∑ i, (h i - spike V h i) ^ 2 ≤ ∑ i, (V / 2) ^ 2 :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = Fintype.card ι * (V / 2) ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
/-- Для `Lip`-Липшицевой по ℓ₂ потери: `|ℓ(spike) − ℓ(h)| ≤ Lip·√d·V/2` —
смещение STE (градиент тождества вместо спайка) не превышает этой величины. -/
theorem spike_loss_shift_le (V : ℝ) (hV : 0 < V) (h : ι → ℝ) (ℓ : (ι → ℝ) → ℝ)
    (Lip : ℝ) (hL : 0 ≤ Lip)
    (hlip : ∀ x y, |ℓ x - ℓ y| ≤ Lip * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    |ℓ (spike V h) - ℓ h| ≤ Lip * Real.sqrt (Fintype.card ι) * V / 2 := by
  have h2 := hlip (spike V h) h
  have hsq := spike_l2_error_le V hV h
  have hcomm : ∀ i, spike V h i - h i = -(h i - spike V h i) := fun i => by ring
  have hsq' : ∀ i, (spike V h i - h i) ^ 2 = (h i - spike V h i) ^ 2 := by
    intro i; rw [hcomm i]; ring
  have h2' : |ℓ (spike V h) - ℓ h| ≤ Lip * Real.sqrt (∑ i, (h i - spike V h i) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hsq' i)] at h2
    exact h2
  have hsqrt : Real.sqrt (∑ i, (h i - spike V h i) ^ 2) ≤ Real.sqrt (Fintype.card ι * (V / 2) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  have hsqrteq : Real.sqrt (Fintype.card ι * (V / 2) ^ 2) = Real.sqrt (Fintype.card ι) * V / 2 := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (div_nonneg hV.le (by norm_num))]
    ring
  rw [hsqrteq] at hsqrt
  calc |ℓ (spike V h) - ℓ h| ≤ Lip * Real.sqrt (∑ i, (h i - spike V h i) ^ 2) := h2'
    _ ≤ Lip * (Real.sqrt (Fintype.card ι) * V / 2) := mul_le_mul_of_nonneg_left hsqrt hL
    _ = Lip * Real.sqrt (Fintype.card ι) * V / 2 := by ring

end Hagi.Energy.STEBias
