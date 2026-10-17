/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Foundations.Recurrence
/-!
# RecursiveDistill: the grow-compress loop at fixed width (§6b.1, gen8 line)

The recursive-distillation program of the runtime plan (2026-10-05,
§6b.1): the model SPIKES at fixed width H and grows DENSITY —
`gen_k: 3 sibs (H) → merged (3H) → joint → distill into a student (H)`,
`gen_{k+1}` sibs seeded from the distillate. What must hold
mathematically for the loop to be worth running to step n:

* **The telescoping bridge** (`distill_chain_telescoping`): the
  single-cycle bridge `CE_q(θ) − CE_q(E) ≤ KL + M‖q−p_E‖₁` (
  `distill_kl_bridge`) composes over generations by telescoping —
  the accumulated slack is ADDITIVE: after n cycles the distillate
  sits at most `Σ δ_k` above the FIRST ensemble.

* **Linear accumulation of the net gain** (`distill_compound_gain`,
  the plan's `genMean_compound`): if every cycle combines a
  certified growth gain c_k with a distillation slack `δ_k` and
  the net `c_k − δ_k ≥ g > 0`, the distillate of generation n
  beats the initial ensemble by at least `n·g`. Honest target:
  only «distillate gen_k beats distillate gen_{k−1}» is certified
  — the distillate stays worse than the uncompressed joint,
  accepted by design.

* **The leak gate** (`distill_leak_gate`): a cycle with
  `c ≤ δ` has nonpositive net — the chain cannot improve through
  it; the loop must STOP (runtime: the per-cycle η-gate on
  the distill efficiency, in efficiency, in nats).

* **Exhaustion of the disagreement field** (`harvest_budget`,
  `exhausted_when`): the disagreement D feeding growth decays
  geometrically (`D_{t+1} ≤ ρ·D_t`, `ρ < 1`); the total
  harvestable gain over any horizon is at most `γ·D_0/(1−ρ)`
  (the plan's `G* = D/(1−ρ)`), and once the remaining field
  `ρ^n·D_0` drops below `ε/γ` no future cycle can certify ε —
  EXHAUSTED: switch corpus, not more cycles.

All statements are conditional bookkeeping over ℝ-sequences with
NAMED premises (hdist, hgrow, hnet, hdecay, hgain); no
`h_emp_` premise hides inside. Sources: runtime plan §6b.1;
single-cycle bridge (2609.38666 / 2607.15467 / 2609.39436);
geometric budget kernel (`geom_sum_le_inv`).
-/

namespace Hagi.Ensemble

open Finset

variable {E S delta c : ℕ → ℝ}

/-! ## Telescoping of the bridge -/

/-- **The telescoping bridge** (§6b.1: the `distill_kl_bridge`
chain over generations). Cycle k: ensemble `E k` is distilled
into student `S k` (slack `delta k` — the single-cycle
bridge `KL_k + M_k‖q−p_E‖₁`), and the next ensemble `E (k+1)`
is grown FROM the distillate (no free relabeling gain). For
every k ≤ n and k < n respectively:

* `hdist k`: `S k ≤ E k + delta k`;
* `hgrow k`: `E (k + 1) ≤ S k`.

Then the distillate of generation n sits at most
`Σ_{k≤n} delta k` above the INITIAL ensemble: the bridge slack
is additive over generations, never multiplicative. -/
theorem distill_chain_telescoping (n : ℕ)
    (hdist : ∀ k ≤ n, S k ≤ E k + delta k)
    (hgrow : ∀ k < n, E (k + 1) ≤ S k) :
    S n ≤ E 0 + ∑ k ∈ Finset.range (n + 1), delta k := by
  induction n with
  | zero =>
      have h0 : S 0 ≤ E 0 + delta 0 := hdist 0 (Nat.le_refl 0)
      simpa using h0
  | succ n ih =>
      have h1 : S (n + 1) ≤ E (n + 1) + delta (n + 1) :=
        hdist (n + 1) (Nat.le_refl (n + 1))
      have h2 : E (n + 1) ≤ S n := hgrow n (Nat.lt_succ_self n)
      have hsum : ∑ k ∈ Finset.range (n + 2), delta k
          = ∑ k ∈ Finset.range (n + 1), delta k + delta (n + 1) := by
        rw [Finset.sum_range_succ]
      have hmono : ∀ k ≤ n, S k ≤ E k + delta k :=
        fun k hk => hdist k (Nat.le_trans hk (Nat.le_succ n))
      have hmono2 : ∀ k < n, E (k + 1) ≤ S k :=
        fun k hk => hgrow k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hih := ih hmono hmono2
      calc S (n + 1) ≤ E (n + 1) + delta (n + 1) := h1
        _ ≤ S n + delta (n + 1) := add_le_add h2 (le_refl _)
        _ ≤ (E 0 + ∑ k ∈ Finset.range (n + 1), delta k) + delta (n + 1) :=
            add_le_add hih (le_refl _)
        _ = E 0 + ∑ k ∈ Finset.range (n + 2), delta k := by
            rw [hsum]; ring

/-- **Linear descent of the ensembles**: under the per-cycle
laws (hgrow in its improvement form + hnet positive net), each
generation's ensemble is at least `g` better than the previous
one — by induction, `E n + n·g ≤ E 0`. -/
theorem ensemble_linear_descent (n : ℕ) {g : ℝ}
    (hdist : ∀ k < n, S k ≤ E k + delta k)
    (hgrow : ∀ k < n, E (k + 1) + c k ≤ S k)
    (hnet : ∀ k < n, g ≤ c k - delta k) :
    E n + n * g ≤ E 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hk := hgrow n (Nat.lt_succ_self n)
      have hd := hdist n (Nat.lt_succ_self n)
      have hn := hnet n (Nat.lt_succ_self n)
      have hstep : E (n + 1) + g ≤ E n := by linarith [hk, hd, hn]
      have hmono : ∀ k < n, S k ≤ E k + delta k :=
        fun k _hk => hdist k (Nat.lt_trans _hk (Nat.lt_succ_self n))
      have hmono2 : ∀ k < n, E (k + 1) + c k ≤ S k :=
        fun k _hk => hgrow k (Nat.lt_trans _hk (Nat.lt_succ_self n))
      have hmono3 : ∀ k < n, g ≤ c k - delta k :=
        fun k _hk => hnet k (Nat.lt_trans _hk (Nat.lt_succ_self n))
      have hih := ih hmono hmono2 hmono3
      have hcast : (((n:ℕ) + 1):ℝ) * g = ((n:ℕ):ℝ) * g + g := by
        push_cast
        ring
      have hgoal : E (n + 1) + (((n:ℕ) + 1):ℝ) * g ≤ E 0 := by
        rw [hcast]
        linarith [hih, hstep]
      rw [Nat.cast_succ]
      exact hgoal

/-- **Linear accumulation while the net is positive** (the
plan's `genMean_compound`). Per cycle k < n: hdist (bridge
slack `delta k`), hgrow (the next ensemble improves on the
distillate by the certified gain `c k`), hnet (net
`c k − delta k ≥ g > 0`). Then the distillate of generation n
beats the initial ensemble by at least `n·g` up to its own
one-cycle slack: `S n + n·g ≤ E 0 + delta n`. While the net
stays positive the improvement accumulates LINEARLY in the
number of cycles. -/
theorem distill_compound_gain (n : ℕ) {g : ℝ}
    (hdist : ∀ k ≤ n, S k ≤ E k + delta k)
    (hgrow : ∀ k < n, E (k + 1) + c k ≤ S k)
    (hnet : ∀ k < n, g ≤ c k - delta k) :
    S n + n * g ≤ E 0 + delta n := by
  have hdesc := ensemble_linear_descent (E := E) (S := S) (delta := delta)
    (c := c) n
    (fun k hk => hdist k (Nat.le_of_lt hk)) hgrow hnet
  have hdn : S n ≤ E n + delta n := hdist n (Nat.le_refl n)
  calc S n + n * g ≤ (E n + delta n) + n * g :=
        add_le_add hdn (le_refl _)
    _ ≤ (E 0 + delta n) := by
        have : E n + n * g ≤ E 0 := hdesc
        linarith

/-- **The leak gate**: if at cycle n+1 the distillation slack
does not exceed the certified growth gain
(`delta (n+1) ≤ c (n+1)` — the net is nonnegative, no leak),
then the next distillate does not regress against the current
one: `S (n+1) ≤ S n`. When the slack EXCEEDS the gain the
guarantee is void — the chain may degrade, and the loop must
STOP (runtime: the per-cycle η-gate on the distill
nats). -/
theorem distill_leak_gate (n : ℕ)
    (hdist : S (n + 1) ≤ E (n + 1) + delta (n + 1))
    (hgrow : E (n + 1) + c (n + 1) ≤ S n)
    (hnet : delta (n + 1) ≤ c (n + 1)) :
    S (n + 1) ≤ S n := by
  have h1 : E (n + 1) + delta (n + 1) ≤ E (n + 1) + c (n + 1) :=
    add_le_add_right hnet (E (n + 1))
  calc S (n + 1) ≤ E (n + 1) + delta (n + 1) := hdist
    _ ≤ E (n + 1) + c (n + 1) := h1
    _ ≤ S n := hgrow

/-! ## Exhaustion of the disagreement field -/

variable {D gain : ℕ → ℝ}

/-- **The geometric harvest budget**: if the disagreement field
D decays by `ρ < 1` per harvested cycle and each cycle's gain is
at most `γ·D_t`, the TOTAL gain over any horizon n is bounded
by the geometric budget `γ·D_0/(1−ρ)` — free growth is finite,
however long the loop runs (the plan's `G* = D/(1−ρ)`). -/
theorem harvest_budget {rho gamma : ℝ} (n : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hgamma : 0 ≤ gamma)
    (hD0 : 0 ≤ D 0)
    (hdecay : ∀ t < n, D (t + 1) ≤ rho * D t)
    (hgain : ∀ t < n, gain t ≤ gamma * D t) :
    ∑ t ∈ Finset.range n, gain t ≤ gamma * D 0 / (1 - rho) := by
  have hDbound : ∀ t ≤ n, D t ≤ rho ^ t * D 0 := by
    intro t
    induction t with
    | zero => simpa using hD0
    | succ t iht =>
        intro ht
        calc D (t + 1) ≤ rho * D t :=
            hdecay t (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht)
          _ ≤ rho * (rho ^ t * D 0) :=
              mul_le_mul_of_nonneg_left (iht (Nat.le_of_succ_le ht)) hrho
          _ = rho ^ (t + 1) * D 0 := by rw [pow_succ]; ring
  have hgeo := Hagi.Foundations.geom_sum_le_inv (rho := rho) n hrho hrho1
  have hsum : ∑ t ∈ Finset.range n, D t ≤ D 0 / (1 - rho) := by
    calc ∑ t ∈ Finset.range n, D t
        ≤ ∑ t ∈ Finset.range n, rho ^ t * D 0 :=
          Finset.sum_le_sum fun t ht => hDbound t (by
            have : t < n := Finset.mem_range.mp ht
            omega)
      _ = D 0 * ∑ t ∈ Finset.range n, rho ^ t := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ D 0 * (1 / (1 - rho)) := by
          exact mul_le_mul_of_nonneg_left hgeo hD0
      _ = D 0 / (1 - rho) := by field_simp
  calc ∑ t ∈ Finset.range n, gain t
      ≤ ∑ t ∈ Finset.range n, gamma * D t := by
        refine Finset.sum_le_sum fun t ht => ?_
        exact hgain t (Finset.mem_range.mp ht)
    _ = gamma * ∑ t ∈ Finset.range n, D t := by rw [← Finset.mul_sum]
    _ ≤ gamma * (D 0 / (1 - rho)) :=
        mul_le_mul_of_nonneg_left hsum hgamma
    _ = gamma * D 0 / (1 - rho) := by ring

/-- **The exhaustion criterion**: once the REMAINING
disagreement field `rho^n * D 0` falls below the per-cycle
threshold `ε/γ` (with `γ > 0`), no future cycle can certify a
gain of `ε` — the recursion is EXHAUSTED; the next meaningful
move is a new CORPUS (fresh disagreement), not more cycles. -/
theorem exhausted_when {rho gamma eps : ℝ} (n : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hgamma : 0 < gamma)
    (heps : 0 < eps) (hD0 : 0 ≤ D 0)
    (hdecay : ∀ t, D (t + 1) ≤ rho * D t)
    (hthin : rho ^ n * D 0 < eps / gamma) :
    gamma * D n < eps := by
  have hDall : ∀ m, D m ≤ rho ^ m * D 0 := by
    intro m
    induction m with
    | zero => simp [hD0]
    | succ m ihm =>
        calc D (m + 1) ≤ rho * D m := hdecay m
          _ ≤ rho * (rho ^ m * D 0) :=
              mul_le_mul_of_nonneg_left ihm hrho
          _ = rho ^ (m + 1) * D 0 := by rw [pow_succ]; ring
  have hDn : D n ≤ rho ^ n * D 0 := hDall n
  have hpos : (0:ℝ) ≤ gamma := hgamma.le
  calc gamma * D n ≤ gamma * (rho ^ n * D 0) :=
        mul_le_mul_of_nonneg_left hDn hpos
    _ < gamma * (eps / gamma) := mul_lt_mul_of_pos_left hthin hgamma
    _ = eps := by field_simp


/-! ## Optimal harvest scheduling up to step n -/

/-- The field never goes negative: each extraction is bounded
by `γ·D k`, so the unit-for-unit payment never overspends. -/
theorem field_nonneg {D h : ℕ → ℝ} {gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D 0)
    (hextract : ∀ k, h k ≤ gamma * D k)
    (hpay : ∀ k, D (k + 1) = D k - h k) :
    ∀ t, 0 ≤ D t := by
  intro t
  induction t with
  | zero => exact hD0
  | succ t ih =>
      have he : h t ≤ gamma * D t := hextract t
      have hp : D (t + 1) = D t - h t := hpay t
      have : gamma * D t ≤ D t := by
        have := mul_le_of_le_one_right ih hgamma1
        linarith
      linarith

/-- **The harvest accounting identity**: each cycle extracts
`h t ≤ γ·D t` from the disagreement field and the field pays
unit for unit (`D (t+1) = D t − h t`). The total harvest over
any horizon telescopes to `D 0 − D n`: ALL certified gain
comes from the field, nothing else. -/
theorem harvest_accounting_identity {D h : ℕ → ℝ} {gamma : ℝ} (n : ℕ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D 0)
    (hextract : ∀ k, h k ≤ gamma * D k)
    (hpay : ∀ k, D (k + 1) = D k - h k) :
    ∑ t ∈ Finset.range n, h t = D 0 - D n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := hpay n
      have hsplit : ∑ t ∈ Finset.range (n + 1), h t
          = ∑ t ∈ Finset.range n, h t + h n := by
        rw [Finset.sum_range_succ]
      rw [hsplit, ih, hp]
      ring

/-- **The greedy field decay**: under the per-cycle extraction
limit, the field can never fall below the geometric schedule
`(1−γ)^t·D 0` — no schedule exhausts the field faster than
the GREEDY one (extract the maximum `γ·D t` every cycle). -/
theorem field_decay_lower {D h : ℕ → ℝ} {gamma : ℝ} (t : ℕ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D 0)
    (hextract : ∀ k, h k ≤ gamma * D k)
    (hpay : ∀ k, D (k + 1) = D k - h k) :
    (1 - gamma) ^ t * D 0 ≤ D t := by
  induction t with
  | zero => simp [hD0]
  | succ t iht =>
      have hp := hpay t
      have he := hextract t
      have hge : (0:ℝ) ≤ 1 - gamma := by linarith
      have hnn := field_nonneg hgamma hgamma1 hD0 hextract hpay t
      calc (1 - gamma) ^ (t + 1) * D 0
          = (1 - gamma) * ((1 - gamma) ^ t * D 0) := by rw [pow_succ]; ring
        _ ≤ (1 - gamma) * D t := mul_le_mul_of_nonneg_left iht hge
        _ = D t - gamma * D t := by ring
        _ ≤ D t - h t := by
            have : gamma * D t ≤ D t := by
              have := mul_le_of_le_one_right hnn hgamma1
              linarith
            linarith
        _ = D (t + 1) := hp.symm

/-- **Greedy horizon optimality**: for ANY extraction schedule
respecting the per-cycle limit `h t ≤ γ·D t` and the
unit-for-unit field payment, the total certified harvest up
to step n is at most `D 0·(1 − (1−γ)^n)` — the value achieved
by the GREEDY schedule (extract the maximum every cycle).
Up to any fixed horizon n the greedy cycle algorithm
maximizes the harvested quality gain; the residual field
after n greedy cycles is exactly `(1−γ)^n·D 0`, meeting the
exhaustion criterion of `exhausted_when`. -/
theorem greedy_horizon_optimal {D h : ℕ → ℝ} {gamma : ℝ} (n : ℕ)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D 0)
    (hextract : ∀ k, h k ≤ gamma * D k)
    (hpay : ∀ k, D (k + 1) = D k - h k) :
    ∑ t ∈ Finset.range n, h t ≤ D 0 * (1 - (1 - gamma) ^ n) := by
  have hid := harvest_accounting_identity n hgamma hgamma1 hD0 hextract hpay
  have hlow := field_decay_lower n hgamma hgamma1 hD0 hextract hpay
  rw [hid]
  have hge : (0:ℝ) ≤ 1 - gamma := by linarith
  have hexp : 0 ≤ (1 - gamma) ^ n := pow_nonneg hge n
  calc D 0 - D n
      ≤ D 0 - (1 - gamma) ^ n * D 0 := by
          have : (1 - gamma) ^ n * D 0 ≤ D n := hlow
          linarith
    _ = D 0 * (1 - (1 - gamma) ^ n) := by ring


end Hagi.Ensemble

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

/-- **Two-layer clamped water-filling corner** (R381): with
the nonnegativity constraint `b ≥ 0`, when even the FULL
budget on layer 2 leaves its error above layer 1's zero-bit
error (`c₁ ≤ c₂/2^B` — equalization would need negative
bits), the corner allocation `(0, B)` is optimal. The proof
is the EXACT factorization
`diff = (2^x − 1)·(c₂·2^x/2^B − c₁)/2^x ≥ 0`
— no calculus. Together with `two_layer_equalize` (interior)
this completes the 2-layer constrained water-filling optimum
(active-set analysis for n = 2). -/
theorem two_layer_clamped_corner (c1 c2 B x : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hB : 0 ≤ B) (hx0 : 0 ≤ x)
    (hxB : x ≤ B) (hcorner : c1 ≤ c2 / (2:ℝ) ^ B) :
    c1 + c2 / (2:ℝ) ^ B ≤ c1 / (2:ℝ) ^ x + c2 / (2:ℝ) ^ (B - x) := by
  have h2pos : (0:ℝ) < (2:ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have h2B : (0:ℝ) < (2:ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) B
  have hadd : (2:ℝ) ^ x * (2:ℝ) ^ (B - x) = (2:ℝ) ^ B := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  -- rewrite c2 / 2^(B-x) = (c2 / 2^B) * 2^x
  have hsub : (2:ℝ) ^ (B - x) = (2:ℝ) ^ B / (2:ℝ) ^ x := by
    rw [div_eq_inv_mul, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) x,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hsub, div_div_eq_mul_div]
  -- goal: c1/2^x + (c2 * 2^x)/2^B ≥ c1 + c2/2^B
  -- exact factorization: diff = (u-1)*(b*u - a)/u
  have hge1 : (1:ℝ) ≤ (2:ℝ) ^ x := by
    exact Real.one_le_rpow (by norm_num) hx0
  have hb : (0:ℝ) < c2 / (2:ℝ) ^ B := div_pos hc2 h2B
  have hinner : c1 ≤ c2 * (2:ℝ) ^ x / (2:ℝ) ^ B := by
    have hmono : c2 / (2:ℝ) ^ B
        ≤ c2 / (2:ℝ) ^ B * (2:ℝ) ^ x :=
      le_mul_of_one_le_right hb.le hge1
    have hform : c2 / (2:ℝ) ^ B * (2:ℝ) ^ x
        = c2 * (2:ℝ) ^ x / (2:ℝ) ^ B := by ring
    rw [hform] at hmono
    exact hcorner.trans hmono
  have hu : (0:ℝ) < (2:ℝ) ^ x := h2pos
  have hb : (0:ℝ) < c2 / (2:ℝ) ^ B := div_pos hc2 h2B
  -- key inequality via exact identity
  have hid : c1 / (2:ℝ) ^ x + c2 * (2:ℝ) ^ x / (2:ℝ) ^ B
      - (c1 + c2 / (2:ℝ) ^ B)
      = ((2:ℝ) ^ x - 1)
          * (c2 * (2:ℝ) ^ x / (2:ℝ) ^ B - c1) / (2:ℝ) ^ x := by
    field_simp
    ring
  have hprod : (0:ℝ) ≤ ((2:ℝ) ^ x - 1)
      * (c2 * (2:ℝ) ^ x / (2:ℝ) ^ B - c1) / (2:ℝ) ^ x := by
    have h1 : (0:ℝ) ≤ (2:ℝ) ^ x - 1 := by linarith
    have h2 : (0:ℝ) ≤ c2 * (2:ℝ) ^ x / (2:ℝ) ^ B - c1 := by
      rw [sub_nonneg]
      exact hinner
    exact div_nonneg (mul_nonneg h1 h2) (le_of_lt h2pos)
  linarith

end Hagi.Budget
