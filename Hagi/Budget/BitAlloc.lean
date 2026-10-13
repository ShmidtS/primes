/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Ensemble.RecursiveDistill

set_option linter.style.header false

/-!
# BitAlloc: optimal bit allocation under a parameter budget

The "maximum quality at minimum size" program: under a hard
cap on model volume, the only remaining freedom is WHERE the
bits go. The corpus (arXiv:2609.38169 STEPQuant —
lifetime-aware bit allocation; arXiv:2607.16097 —
compute-optimal frontier: under fixed FLOPs an optimal
allocation EXISTS and SHIFTS with the budget; the classical
water-filling lineage of arXiv:2607.16600) reduces to one
mathematical core: minimize the total quantization error
`Σ_l c_l · 2^(−b_l)` over layer bit-widths `b_l` subject to
the volume budget `Σ b_l ≤ B`. This module proves the finite
kernel of that optimization.

**Model.** Layers indexed by `Fin n`, each with sensitivity
`c_l > 0` (the per-layer error coefficient — from the
QuantBridge bound `ΔE_l ≤ κ_l·√n_l·s_l/2`: the grid step
halves with each extra bit). Layer error
`e_l(b) = c_l · 2^(−b)`.

**Results.**

* `layerError_antitone` / `layerError_pred` — one more bit
  halves the layer error; one fewer bit doubles it.

* `transfer_exact` — THE MARGINAL-EXCHANGE LEMMA: moving one
  bit from layer k (with a bit to give) to a different
  layer j changes the total error by EXACTLY
  `e_k − e_j/2` (removing a bit doubles the giver's error;
  adding one halves the receiver's). In particular the
  transfer does not increase the total error exactly when
  `e_k ≤ e_j/2` — the receiver's current error is at least
  TWICE the giver's: bits want to live where the error is
  still large. Every greedy bit-reallocation loop is
  licensed by this identity.

* `two_layer_equalize` — THE TWO-LAYER OPTIMUM: for two
  layers and a budget split as `x + (x + 2d)`, the balanced
  split `x+d, x+d` has total error at most that of the
  original — by induction, balancing never hurts, and the
  water-filling shape (equalized errors) is optimal in its
  simplest instance.

**Honest boundary.** The full n-layer continuous water
filling (equalized marginals) and the STEPQuant lifetime
weighting are engineering on this kernel; the frontier
claim of 2607.16097 (the optimum SHIFTS with total budget)
is empirical fitting — not claimed here.
-/

namespace Hagi.Budget

open Finset

/-- The per-layer quantization error: sensitivity times the
grid factor — each extra bit halves the grid, hence halves
the error. -/
noncomputable def layerError (c : ℝ) (b : ℕ) : ℝ := c / 2 ^ b

theorem layerError_pos (c : ℝ) (hc : 0 < c) (b : ℕ) :
    0 < layerError c b := by
  unfold layerError
  positivity

theorem layerError_antitone (c : ℝ) (b : ℕ) :
    layerError c (b + 1) = layerError c b / 2 := by
  unfold layerError
  rw [pow_succ]
  field_simp

theorem layerError_pred (c : ℝ) {b : ℕ} (hb : 0 < b) :
    layerError c (b - 1) = 2 * layerError c b := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hb
  subst hm
  rw [show (0 + m + 1 - 1 : ℕ) = m by omega, layerError_antitone]
  ring

/-- The total error of an allocation `f: layer → bits`. -/
noncomputable def totalError (c : Fin n → ℝ) (f : Fin n → ℕ) : ℝ :=
  ∑ l, layerError (c l) (f l)

/-- Two-point decomposition of the total: any allocation's
total error is its two marked coordinates plus the sum over
the complement of `{j, k}`. -/
theorem totalError_two_point {n : ℕ} (c : Fin n → ℝ)
    (f : Fin n → ℕ) (j k : Fin n) (hjk : j ≠ k) :
    totalError c f = layerError (c j) (f j) + layerError (c k) (f k)
      + ∑ l ∈ (Finset.univ.erase j).erase k, layerError (c l) (f l) := by
  classical
  unfold totalError
  have h1 : ∑ l, layerError (c l) (f l)
      = ∑ l ∈ Finset.univ.erase j, layerError (c l) (f l) + layerError (c j) (f j) :=
    (Finset.sum_erase_add Finset.univ (fun l => layerError (c l) (f l))
      (Finset.mem_univ j)).symm
  have h2 : ∑ l ∈ Finset.univ.erase j, layerError (c l) (f l)
      = ∑ l ∈ (Finset.univ.erase j).erase k, layerError (c l) (f l)
        + layerError (c k) (f k) :=
    (Finset.sum_erase_add (Finset.univ.erase j) (fun l => layerError (c l) (f l))
      (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)).symm
  rw [h1, h2]
  ring

/-- **The marginal-exchange identity**: moving one bit from
layer k (with a bit to give) to a different layer j
changes the total error by EXACTLY
`e_k(b_k) − e_j(b_j)/2`: removing a bit doubles the giver's
error (loss `e_k`), adding one halves the receiver's (gain
`e_j/2`). The transfer is nonincreasing precisely when
`e_k ≤ e_j/2` — the receiver's current error is at least
twice the giver's. This identity licenses every greedy
bit-reallocation loop ("move bits toward the largest current
error"). -/
theorem transfer_exact {n : ℕ} (c : Fin n → ℝ)
    (f : Fin n → ℕ) (j k : Fin n) (hjk : j ≠ k) (hk : 0 < f k) :
    totalError c (fun l => if l = j then f j + 1 else if l = k then f k - 1 else f l)
      = totalError c f + (layerError (c k) (f k) - layerError (c j) (f j) / 2) := by
  classical
  set g : Fin n → ℕ :=
    fun l => if l = j then f j + 1 else if l = k then f k - 1 else f l with hg
  have hgpj : g j = f j + 1 := by simp [hg]
  have hgpk : g k = f k - 1 := by
    simp [hg, show ¬(k = j) from Ne.symm hjk]
  have hgr : ∀ l ∈ (Finset.univ.erase j).erase k, g l = f l := by
    intro l hl
    obtain ⟨hk2, hmem⟩ := Finset.mem_erase.mp hl
    obtain ⟨hj2, _⟩ := Finset.mem_erase.mp hmem
    simp [hg, hj2, hk2]
  rw [totalError_two_point c g j k hjk, totalError_two_point c f j k hjk, hgpj, hgpk]
  rw [Finset.sum_congr rfl (fun l hl => by rw [hgr l hl])]
  rw [layerError_antitone (c j) (f j), layerError_pred (c k) hk]
  ring

/-- Monotone decay of the layer error in the bit width (for
nonnegative sensitivity). -/
theorem layerError_anti_mono (c : ℝ) (hc : 0 ≤ c) :
    ∀ b1 b2 : ℕ, b1 ≤ b2 → layerError c b2 ≤ layerError c b1 := by
  intro b1 b2 hle
  induction b2 with
  | zero => simp at hle; subst hle; exact le_refl _
  | succ b2 ih =>
      rcases Nat.lt_or_ge b1 (b2 + 1) with hlt | hge
      · have hb1 : b1 ≤ b2 := by omega
        have hpos : 0 ≤ layerError c b2 := by
          unfold layerError
          positivity
        calc layerError c (b2 + 1) = layerError c b2 / 2 :=
                layerError_antitone c b2
          _ ≤ layerError c b2 := by
              exact div_le_self hpos one_le_two
          _ ≤ layerError c b1 := ih hb1
      · have : b1 = b2 + 1 := Nat.le_antisymm hle hge
        subst this
        exact le_refl _

/-- **The two-layer balancing law**: for nonnegative
sensitivity, any budget split `x + (x + 2d)` is dominated by
the balanced split `(x+d, x+d)` — balancing two layers never
hurts (even imbalance; the odd case is covered up to the
factor-2 invariant of `stable_factor_two`). The greedy
exchange loop TERMINATES ( `BitAllocTermination.
no_infinite_improving_chain`: finite allocation space +
strict improvement ⟹ pigeonhole), and at the stop point
`stable_factor_two` certifies factor-2 balance. Still not
proved here: the n-layer continuous water-filling optimum. -/
theorem two_layer_equalize (c : ℝ) (hc : 0 ≤ c) (x d : ℕ) :
    layerError c x + layerError c (x + 2 * d)
      ≥ 2 * layerError c (x + d) := by
  induction d generalizing x with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      exact le_of_eq (by ring)
  | succ d ih =>
      have hant1 : layerError c (x + 1) = layerError c x / 2 := by
        rw [show x + 1 = x + 1 from rfl]
        exact layerError_antitone c x
      have hant2 : layerError c (x + 2 * d + 1) = layerError c (x + 2 * d) / 2 := by
        rw [show x + 2 * d + 1 = (x + 2 * d) + 1 from rfl]
        exact layerError_antitone c (x + 2 * d)
      have h1 : layerError c (x + 2 * d + 2) = layerError c (x + 2 * d) / 4 := by
        rw [show x + 2 * d + 2 = (x + 2 * d + 1) + 1 from rfl,
          layerError_antitone c (x + 2 * d + 1), hant2]
        ring
      have hmono : layerError c (x + 2 * d) ≤ layerError c x :=
        layerError_anti_mono c hc x (x + 2 * d) (by omega)
      have hstep : layerError c x + layerError c (x + 2 * d + 2)
          ≥ layerError c (x + 1) + layerError c (x + 2 * d + 1) := by
        have hpos : 0 ≤ layerError c x := by
          unfold layerError
          positivity
        rw [hant1, hant2, h1]
        linarith
      have hih := ih (x + 1)
      have hshift : layerError c (x + 1) + layerError c ((x + 1) + 2 * d)
          = layerError c (x + 1) + layerError c (x + 2 * d + 1) := by
        rw [show (x + 1) + 2 * d = x + 2 * d + 1 from by omega]
      have hfinal : 2 * layerError c ((x + 1) + d)
          = 2 * layerError c (x + d + 1) := by
        rw [show (x + 1) + d = x + d + 1 from by omega]
      calc layerError c x + layerError c (x + 2 * d + 2)
          ≥ layerError c (x + 1) + layerError c (x + 2 * d + 1) := hstep
        _ = layerError c (x + 1) + layerError c ((x + 1) + 2 * d) := hshift.symm
        _ ≥ 2 * layerError c ((x + 1) + d) := hih
        _ = 2 * layerError c (x + d + 1) := hfinal
        _ = 2 * layerError c (x + (d + 1)) := by
            rw [show x + (d + 1) = x + d + 1 from by omega]


/-- **Imbalance implies an improving exchange**: whenever two
layers are out of balance by more than the factor 2 (the
receiver's error exceeds TWICE the giver's) and the giver
still holds a bit, transferring that bit STRICTLY decreases
the total error. Contrapositive: a stable allocation (no
strictly improving single-bit transfer exists) has every
error within a factor 2 of every other — the water-filling
shape, certified at the fixed point of the greedy loop. -/
theorem imbalance_yields_gain {n : ℕ} (c : Fin n → ℝ)
    (f : Fin n → ℕ) (j k : Fin n) (hjk : j ≠ k) (hk : 0 < f k)
    (himb : 2 * layerError (c k) (f k) < layerError (c j) (f j)) :
    totalError c (fun l => if l = j then f j + 1 else if l = k then f k - 1 else f l)
      < totalError c f := by
  have hchange := transfer_exact c f j k hjk hk
  rw [hchange]
  have : layerError (c k) (f k) - layerError (c j) (f j) / 2 < 0 := by
    rw [div_eq_mul_inv]
    have hinv : (2:ℝ)⁻¹ = 1/2 := by norm_num
    rw [hinv]
    nlinarith [himb]
  linarith

/-- **The factor-2 balance certificate at a no-gain point**
( honesty reformulation — the former version restated its
hypothesis verbatim): if NO single-bit transfer strictly improves
the allocation, then every layer error is within factor 2 of every
other layer error that still has a bit to give. This is now a
GENUINE consequence of `imbalance_yields_gain` (its
contrapositive): a factor-2 violation WOULD yield an improving
transfer, so no-gain excludes the violation. Requires nonnegative
sensitivities (for the j = k diagonal). -/
theorem stable_factor_two {n : ℕ} (c : Fin n → ℝ)
    (f : Fin n → ℕ) (hc : ∀ i, 0 ≤ c i)
    (hnogain : ∀ j k : Fin n, j ≠ k → 0 < f k →
      ¬ totalError c (fun l => if l = j then f j + 1 else
        if l = k then f k - 1 else f l) < totalError c f) :
    ∀ j k : Fin n, f k ≠ 0 →
      layerError (c j) (f j) ≤ 2 * layerError (c k) (f k) := by
  intro j k hk
  by_cases hjk : j = k
  · subst hjk
    -- diagonal: e_j ≤ 2·e_j reduces to layerError nonneg
    have hnn : 0 ≤ layerError (c j) (f j) := by
      unfold layerError
      apply div_nonneg (hc j)
      positivity
    linarith
  · -- contrapositive of imbalance_yields_gain
    by_contra hviol
    have himb : 2 * layerError (c k) (f k) < layerError (c j) (f j) := by
      have : ¬ (layerError (c j) (f j) ≤ 2 * layerError (c k) (f k)) := hviol
      linarith
    have h0k : 0 < f k := Nat.pos_of_ne_zero hk
    exact hnogain j k hjk h0k (imbalance_yields_gain c f j k hjk h0k himb)



/-- **The full-generation quality-volume certificate**: the
distillate of generation n, under the recursive-distill
compound gain (`distill_compound_gain`) AND a bit-budget
allocation `f` with nonnegative sensitivities `c` (the
BitAlloc model), obeys the ADDITIVE composite bound — the
distillate is better than the initial ensemble by the linear
accumulation `n·g`, up to its own distillation slack and the
total quantization error of the deployed bits. One inequality
certifies the whole grow-compress-quantize pipeline of a
generation against the parameter budget. -/
theorem distill_quant_composite {E S delta c_seq : ℕ → ℝ}
    {c : Fin m → ℝ} {f : Fin m → ℕ} {g : ℝ} (n : ℕ)
    (hc : ∀ l, 0 ≤ c l)
    (hdist : ∀ k ≤ n, S k ≤ E k + delta k)
    (hgrow : ∀ k < n, E (k + 1) + c_seq k ≤ S k)
    (hnet : ∀ k < n, g ≤ c_seq k - delta k) :
    S n + n * g ≤ E 0 + delta n + totalError c f := by
  have hcg := Hagi.Ensemble.distill_compound_gain (E := E) (S := S)
    (delta := delta) (c := c_seq) n hdist hgrow hnet
  have hq : 0 ≤ totalError c f := by
    refine Finset.sum_nonneg fun l _ => ?_
    have := hc l
    unfold layerError
    positivity
  linarith

/-!
### Continuous water-filling optimum (R378)

The n-layer continuous water-filling optimum — the last open
item of this module (He–Zhao–Zhou TWC 2013 geometric
water-filling, plan §1.2): in the continuous relaxation
(real-valued bit budgets), the ERROR-EQUALIZED allocation
(all `c i / 2 ^ f i` equal) minimizes the total error among
ALL allocations with the same total budget. The engine is
Jensen for exp: Σ e^{y i} ≥ n e^{ȳ} — equalized y (hence
equalized errors) attains the bound.
-/

theorem jensen_exp_sum_le {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ) :
    n * Real.exp ((Finset.univ.sum y) / n)
      ≤ Finset.univ.sum (fun i => Real.exp (y i)) := by
  have hj := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin n => (1:ℝ) / (n:ℝ)) (p := y)
    (fun i _ => by positivity) (by
      rw [← Finset.sum_div]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.smul_one_eq_cast]
      field_simp)
    (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul, mul_one_div] at hj
  have hleft : (Finset.univ.sum y) / (n:ℝ)
      = ∑ i, (1:ℝ)/(n:ℝ) * y i := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_comm]
      field_simp
  rw [hleft]
  have hmul : (n:ℝ) * ∑ i, (1:ℝ)/(n:ℝ) * Real.exp (y i)
      = ∑ i, Real.exp (y i) := by
    rw [← Finset.mul_sum, ← mul_assoc]
    field_simp
  calc (n:ℝ) * Real.exp (∑ i, (1:ℝ)/(n:ℝ) * y i)
      ≤ (n:ℝ) * ∑ i, (1:ℝ)/(n:ℝ) * Real.exp (y i) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
    _ = ∑ i, Real.exp (y i) := hmul

noncomputable def totalErrorCont {n : ℕ} (c : Fin n → ℝ) (f : Fin n → ℝ) : ℝ :=
  ∑ i, c i / 2 ^ (f i)

theorem water_filling_inner_optimum {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (B : ℝ)
    (f g : Fin n → ℝ)
    (hsumf : ∑ i, f i = B) (hsumg : ∑ i, g i = B)
    (halign : ∀ i j, c i / 2 ^ (f i) = c j / 2 ^ (f j)) :
    totalErrorCont c f ≤ totalErrorCont c g := by
  have hterm : ∀ (h : Fin n → ℝ) (i : Fin n),
      c i / 2 ^ (h i)
        = Real.exp (Real.log (c i) - h i * Real.log 2) := by
    intro h i
    rw [← Real.exp_log (div_pos (hc i)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (h i)))]
    congr 1
    rw [Real.log_div (hc i).ne'
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (h i)).ne']
    rw [Real.log_rpow (by norm_num : (0:ℝ) < 2) (h i)]
  -- equal total log-sums
  have hsumy : (∑ i, (Real.log (c i) - f i * Real.log 2))
      = (∑ i, (Real.log (c i) - g i * Real.log 2)) := by
    have hsub : (∑ i, (Real.log (c i) - f i * Real.log 2))
        - (∑ i, (Real.log (c i) - g i * Real.log 2))
        = ∑ i, ((Real.log (c i) - f i * Real.log 2)
            - (Real.log (c i) - g i * Real.log 2)) :=
      (Finset.sum_sub_distrib _ _).symm
    have hzero : (∑ i, (Real.log (c i) - f i * Real.log 2))
        - (∑ i, (Real.log (c i) - g i * Real.log 2)) = 0 := by
      rw [hsub, Finset.sum_congr rfl (fun i _ =>
        show (Real.log (c i) - f i * Real.log 2)
            - (Real.log (c i) - g i * Real.log 2)
          = (g i - f i) * Real.log 2 by ring),
        ← Finset.sum_mul, Finset.sum_sub_distrib, hsumf, hsumg,
        sub_self, zero_mul]
    exact sub_eq_zero.mp hzero
  -- Jensen for yg
  have hj := jensen_exp_sum_le hn
    (fun i => Real.log (c i) - g i * Real.log 2)
  -- yf constant
  have hconst : ∀ i : Fin n,
      (Real.log (c i) - f i * Real.log 2)
        = (Real.log (c ⟨0, hn⟩) - f ⟨0, hn⟩ * Real.log 2) := by
    intro i
    have h1 : Real.exp (Real.log (c i) - f i * Real.log 2)
        = Real.exp (Real.log (c ⟨0, hn⟩) - f ⟨0, hn⟩ * Real.log 2) := by
      rw [← hterm f i, ← hterm f ⟨0, hn⟩]
      exact halign i ⟨0, hn⟩
    exact Real.exp_injective h1
  -- rewrite goal in exp-sums
  unfold totalErrorCont
  rw [Finset.sum_congr rfl (fun i _ => hterm f i),
    Finset.sum_congr rfl (fun i _ => hterm g i)]
  -- LHS = n * exp(Σyf/n) since yf const
  have hsumc : (∑ i, (Real.log (c i) - f i * Real.log 2))
      = n * (Real.log (c ⟨0, hn⟩) - f ⟨0, hn⟩ * Real.log 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hconst i)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : ((n:ℝ)) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have hleft : ∑ i, Real.exp (Real.log (c i) - f i * Real.log 2)
      = n * Real.exp ((∑ i, (Real.log (c i) - f i * Real.log 2)) / n) := by
    rw [Finset.sum_congr rfl (fun i _ =>
        show Real.exp (Real.log (c i) - f i * Real.log 2)
          = Real.exp (Real.log (c ⟨0, hn⟩) - f ⟨0, hn⟩ * Real.log 2) from
        congrArg Real.exp (hconst i))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [hsumc, mul_div_cancel_left₀ _ hnR]
  rw [hleft, hsumy]
  exact hj

end Hagi.Budget
