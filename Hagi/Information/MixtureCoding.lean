/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# MixtureCoding — сжатие смесью экспертов: регрет-форма

`archiver.py` (HAGI_v2) кодирует только предсказанием модели и проигрывает
`zlib -9` ~25% на типичных потоках. Альтернатива: арифметический кодер на
смеси `p_mix = Σ w_k p_k` экспертов (модель, PPM-3, zlib как эксперт), веса —
Hedge (`MirrorHedge`, `mwu_sqrt_bound`).

* `mixCE w p = -log Σ w_k p_k` — CE смеси на символе;
* `mixCE_le_best_regret` — `mixCE ≤ CE_j − log w_j`: смесь не хуже любого
  эксперта с положительным весом на `log(1/w_j)`;
* `hedge_negLogW_le` — для Hedge-весов `w_k = e^{-L_k}/Z`:
  `-log w_j ≤ (L_j − m) + log K` (`m ≤ L_k`), т.е. bpb смеси ≤ bpb лучшего
  эксперта + `log₂K + regret` нат/символ.
-/

namespace Hagi.Information.MixtureCoding

/-- CE смеси предикторов на символе: `-log Σ w_k p_k`. -/
noncomputable def mixCE {K : Type*} [Fintype K] (w : K → ℝ) (p : K → ℝ) : ℝ :=
  -Real.log (∑ k, w k * p k)
theorem mixCE_le_best_regret {K : Type*} [Fintype K] (w : K → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (j : K) (hwj : 0 < w j) (p : K → ℝ) (hp : ∀ k, 0 < p k) :
    mixCE w p ≤ -Real.log (p j) - Real.log (w j) := by
  have hle : w j * p j ≤ ∑ k, w k * p k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (hw0 k) (hp k).le) (Finset.mem_univ j)
  have h1 : Real.log (w j * p j) ≤ Real.log (∑ k, w k * p k) :=
    Real.log_le_log (mul_pos hwj (hp j)) hle
  rw [Real.log_mul hwj.ne' (hp j).ne'] at h1
  unfold mixCE
  linarith
theorem hedge_negLogW_le {K : Type*} [Fintype K] [Nonempty K] (L : K → ℝ) (m : ℝ)
    (hmin : ∀ k, m ≤ L k) (j : K) :
    -Real.log (Real.exp (-L j) / ∑ k, Real.exp (-L k))
      ≤ (L j - m) + Real.log (Fintype.card K : ℝ) := by
  have hZpos : 0 < ∑ k, Real.exp (-L k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  have hZle : ∑ k, Real.exp (-L k) ≤ (Fintype.card K : ℝ) * Real.exp (-m) := by
    calc ∑ k, Real.exp (-L k) ≤ ∑ k, Real.exp (-m) := Finset.sum_le_sum (fun k _ =>
        Real.exp_monotone (by linarith [hmin k]))
      _ = (Fintype.card K : ℝ) * Real.exp (-m) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hK : (0:ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hexpm : Real.exp m * Real.exp (-m) = 1 := by rw [← Real.exp_add]; simp
  have hZm : Real.exp m * ∑ k, Real.exp (-L k) ≤ (Fintype.card K : ℝ) := by
    calc Real.exp m * ∑ k, Real.exp (-L k)
        ≤ Real.exp m * ((Fintype.card K : ℝ) * Real.exp (-m)) :=
          mul_le_mul_of_nonneg_left hZle (Real.exp_pos _).le
      _ = (Fintype.card K : ℝ) := by
        rw [← mul_assoc, mul_comm (Real.exp m) (Fintype.card K : ℝ), mul_assoc, hexpm, mul_one]
  have hw : Real.exp (-(L j - m)) / (Fintype.card K : ℝ)
      ≤ Real.exp (-L j) / ∑ k, Real.exp (-L k) := by
    rw [div_le_div_iff₀ hK hZpos]
    have hmul : Real.exp (-(L j - m)) = Real.exp (-L j) * Real.exp m := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hmul]
    have hcancel : (0:ℝ) < Real.exp (-L j) := Real.exp_pos _
    calc Real.exp (-L j) * Real.exp m * ∑ k, Real.exp (-L k)
        = Real.exp (-L j) * (Real.exp m * ∑ k, Real.exp (-L k)) := by ring
      _ ≤ Real.exp (-L j) * (Fintype.card K : ℝ) := mul_le_mul_of_nonneg_left hZm hcancel.le
  have h1 := Real.log_le_log (div_pos (Real.exp_pos _) hK) hw
  rw [Real.log_div (Real.exp_ne_zero _) hK.ne', Real.log_exp,
    Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp] at h1
  have h2 : -Real.log (Real.exp (-L j) / ∑ k, Real.exp (-L k))
      = L j + Real.log (∑ k, Real.exp (-L k)) := by
    rw [Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]; ring
  have h3 : Real.log (∑ k, Real.exp (-L k)) ≤ Real.log (Fintype.card K : ℝ) - m := by linarith
  rw [h2]
  linarith

end Hagi.Information.MixtureCoding
