/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Recurrence
import Hagi.Core.RootContrast
/-!
# CycleChannel — generation-decay law and channel switching

Under a saturating-decay model, a generation's free-energy gap `F`
shrinks by `k·F/(F+s)`. Two conditional results (the model is
phenomenological, calibrated on data, and assumed as hypotheses;
nothing here is a convergence theorem):

* `cycle_decay_mono`: if `0 < k < F + s` and `s ≥ 0`, then
  `F·(1 − k/(F+s)) < F` and is nonnegative;
* `cycle_decay_ratio`: the exact step-ratio identity
  `Δ'/Δ = F'·(F+s)/(F·(F'+s))` for the model gains
  `Δ = k·F/(F+s)`;
* `channel_switch`: with movement gain `k·F/(F+s)` at cost `Cm`
and rank gain `b·√F` at cost `Cr` (all constants positive), if
`√F·k·Cr < b·Cm·s` then the rank index strictly dominates:
`k·F/(F+s)/Cm < b·√F/Cr`.

T2 additionally assumes channel independence; the measured
LoRA-over-clamp8 super-additivity is a recorded deviation outside
this model.
-/

open Finset Real

namespace Hagi.Growth

section CycleDecay

/-- If `0 ≤ s`, `0 < F`, `0 < k`, and `k < F + s`, then
`F * (1 - k/(F + s)) < F` and `0 ≤ F * (1 - k/(F + s))`. -/
theorem cycle_decay_mono (F k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hk : 0 < k) (hklt : k < F + s) :
    F * (1 - k/(F + s)) < F ∧ 0 ≤ F * (1 - k/(F + s)) := by
  constructor
  · have heq : F * (1 - k/(F + s)) = F - F * k/(F + s) := by ring
    rw [heq]
    have hpos2 : 0 < F * k/(F + s) := by positivity
    linarith
  · have hfrac2 : 0 ≤ 1 - k/(F + s) := by
      have : k ≤ F + s := by linarith
      rw [sub_nonneg, div_le_one (by linarith : (0:ℝ) < F + s)]
      linarith
    positivity

/-- Exact step-ratio identity for the saturating model gains
`Δ = k·F/(F+s)`: if `0 ≤ s`, `0 < F`, `0 < F'`, `0 < k`, then
`(k·F'/(F'+s)) / (k·F/(F+s)) = F'·(F+s)/(F·(F'+s))`. -/
theorem cycle_decay_ratio (F F' k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hF' : 0 < F') (hk : 0 < k) :
    (k * F' / (F' + s)) / (k * F / (F + s))
      = F' * (F + s) / (F * (F' + s)) := by
  field_simp

end CycleDecay

section ChannelBudget

/-- If all constants are positive (`0 < s`, `0 < k`, `0 < b`,
`0 < Cm`, `0 < Cr`, `0 < F`) and `√F·k·Cr < b·Cm·s`, then the
rank index dominates the movement index:
`k·F/(F+s)/Cm < b·√F/Cr`. -/
theorem channel_switch (F k s b Cm Cr : ℝ)
    (hs : 0 < s) (hk : 0 < k) (hb : 0 < b) (hCm : 0 < Cm)
    (hCr : 0 < Cr) (hF : 0 < F)
    (hswitch : √F * (k * Cr) < b * Cm * s) :
    k * F / (F + s) / Cm < b * √F / Cr := by
  set t := √F with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hF
  have hF2 : t * t = F := Real.mul_self_sqrt (le_of_lt hF)
  have hFs : (0:ℝ) < F + s := by nlinarith
  have h1 : k * F / (F + s) ≤ k * F / s := by
    rw [div_le_div_iff₀ hFs hs]
    nlinarith [mul_nonneg (le_of_lt hk) (le_of_lt hF),
      mul_nonneg (le_of_lt hk) (le_of_lt hF), mul_nonneg hs.le hs.le,
      mul_nonneg hFs.le hFs.le]
  have h2 : k * F / s * Cr < b * t * Cm := by
    have hstep : (t * (k * Cr)) * (t / s) < b * Cm * t := by
      have h1' : (t * (k * Cr)) * (t / s) < (b * Cm * s) * (t / s) :=
        mul_lt_mul_of_pos_right hswitch (by positivity : (0:ℝ) < t / s)
      rw [show (b * Cm * s) * (t / s) = b * Cm * t by field_simp] at h1'
      exact h1'
    calc k * F / s * Cr = (t * (k * Cr)) * (t / s) := by
          conv_lhs => rw [← hF2]
          field_simp
      _ < b * Cm * t := hstep
      _ = b * t * Cm := by ring
  have hA : k * F / (F + s) / Cm ≤ k * F / s / Cm :=
    div_le_div_of_nonneg_right h1 (le_of_lt hCm)
  have hB : k * F / s / Cm < b * t / Cr := by
    rw [div_lt_div_iff₀ hCm hCr]
    exact h2
  linarith

end ChannelBudget

end Hagi.Growth

set_option linter.style.header false

/-!
# SeedOnly — ограничение разнообразия для seed-only siblings

* `geom_range_identity`: `(a − 1)·Σ_{i<n} a^i = a^n − 1`;
* `disp_recurrence_general`: при `0 ≤ a`, `0 ≤ s`,
  `D (t+1) ≤ a·D t + s` следует
  `D t ≤ a^t·D 0 + s·Σ_{i<t} a^i` (любое a ≥ 0);
* `sum_dist_mean_le`: `Σ‖x a − x̄‖² ≤ Σ‖x a − y‖²` для любого y;
* `seed_only_disp_bound`: при `dispL t ≤ Λ²·dispP t`,
  `dispP (t+1) ≤ a·dispP t + s` и `dispP 0 = 0` —
  `dispL t ≤ Λ²·s·Σ_{i<t} a^i`;
* `seed_only_grow_stop`: если
  `gapInf ≤ c·Λ²·s/(1−a) < eps`, то `gapInf < eps`.

Ядро «gap ⇒ dispersion» (Jensen/Hoeffding, константа c) здесь
НЕ доказано и цитируется как посылка; результат применим к
gen ≥ 2 (одинаковый init). Режим a < 1 решается измерением.
-/

open Finset Real InnerProductSpace

namespace Hagi.Growth

section SeedOnly

/-- При `0 < n` и любом y:
`Σ‖x a − x̄‖² ≤ Σ‖x a − y‖²`, где `x̄` — среднее. -/
theorem sum_dist_mean_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (hn : 0 < n) (x : Fin n → V) (y : V) :
    ∑ a, ‖x a - ((1/(n:ℝ)) • ∑ i, x i)‖^2 ≤ ∑ a, ‖x a - y‖^2 := by
  set m : V := (1/(n:ℝ)) • ∑ i, x i with hmdef
  have hmsum : ((n:ℕ):ℝ) • m = ∑ i, x i := by
    rw [hmdef, smul_smul]

    field_simp
    simp
  have hsumx : ∑ a, x a = ((n:ℕ):ℝ) • m := hmsum.symm
  have hsumsub : ∑ a, (x a - m) = 0 := by
    have hsplit : ∑ a : Fin n, (x a - m) = ∑ a : Fin n, x a - ∑ a : Fin n, m :=
      sum_sub_distrib (fun a : Fin n => x a) (fun _ : Fin n => m)
    rw [hsplit, hsumx]
    have hsumconst : ∑ a ∈ (Finset.univ : Finset (Fin n)), m = ((n:ℕ):ℝ) • m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_smul_eq_nsmul ℝ]
    rw [hsumconst, sub_self]
  have hexp : ∀ a : Fin n, ‖x a - y‖^2 = ‖x a - m‖^2 + 2 * ⟪x a - m, m - y⟫_ℝ + ‖m - y‖^2 := by
    intro a
    have hs : x a - y = (x a - m) + (m - y) := by simp only [hmdef]; abel
    have ha := norm_add_pow_two (𝕜 := ℝ) (x a - m) (m - y)
    simp only [RCLike.re_to_real] at ha
    rw [hs, ha]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← sum_inner (𝕜 := ℝ) (Finset.univ : Finset (Fin n))
    (fun a => x a - m) (m - y), hsumsub, inner_zero_left, mul_zero]
  have hnn : (0:ℝ) ≤ ∑ a ∈ (Finset.univ : Finset (Fin n)), ‖m - y‖^2 := by
    refine Finset.sum_nonneg ?_
    intro a _
    positivity
  linarith

/-- Если `dispL t ≤ Λ²·dispP t`, `dispP (t+1) ≤ a·dispP t + s`
и `dispP 0 = 0`, то
`dispL t ≤ Λ²·s·Σ_{i<t} a^i`. -/
theorem seed_only_disp_bound (Lam a s : ℝ)
    (dispL dispP : ℕ → ℝ)
    (h_emp_lip : ∀ t, dispL t ≤ Lam^2 * dispP t)
    (ha : 0 ≤ a) (hs : 0 ≤ s)
    (h_emp_disp_step : ∀ t, dispP (t+1) ≤ a * dispP t + s)
    (hd0 : dispP 0 = 0) (t : ℕ) :
    dispL t ≤ Lam^2 * s * ∑ i ∈ Finset.range t, a^i := by
  have hP := Hagi.Foundations.disp_recurrence_general (D := dispP) ha hs h_emp_disp_step t
  rw [hd0, mul_zero, zero_add] at hP
  calc dispL t ≤ Lam^2 * dispP t := h_emp_lip t
    _ ≤ Lam^2 * (s * ∑ i ∈ Finset.range t, a^i) := by
        exact mul_le_mul_of_nonneg_left hP (sq_nonneg Lam)
    _ = Lam^2 * s * ∑ i ∈ Finset.range t, a^i := by ring

/-- Если `gapInf ≤ c·Λ²·s/(1−a)` и
`c·Λ²·s/(1−a) < eps`, то `gapInf < eps`. -/
theorem seed_only_grow_stop (c Lam a s eps gapInf : ℝ)
    (_hc : 0 ≤ c) (_hLam : 0 ≤ Lam) (_ha : 0 ≤ a) (_ha1 : a < 1) (_hs : 0 ≤ s)
    (hbound : gapInf ≤ c * Lam^2 * s / (1 - a))
    (hfloor : c * Lam^2 * s / (1 - a) < eps) :
    gapInf < eps := by
  linarith

end SeedOnly

end Hagi.Growth

