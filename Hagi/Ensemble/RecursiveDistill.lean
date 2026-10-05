/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.DistillTransfer
import Hagi.Foundations.Recurrence
import Hagi.Foundations.Telescope

set_option linter.style.header false

/-!
# RecursiveDistill: the grow-compress loop at fixed width (§6b.1, gen8 line)

The recursive-distillation program of the runtime plan (2026-10-05,
§6b.1): the model SPIKES at fixed width H and grows DENSITY —
`gen_k: 3 sibs (H) → merged (3H) → joint → distill into a student (H)`,
`gen_{k+1}` sibs seeded from the distillate. What must hold
mathematically for the loop to be worth running to step n:

* **The telescoping bridge** (`distill_chain_telescoping`): the
  single-cycle bridge `CE_q(θ) − CE_q(E) ≤ KL + M‖q−p_E‖₁` (R134
  `distill_kl_bridge`) composes over generations by telescoping —
  the accumulated slack is ADDITIVE: after n cycles the distillate
  sits at most `Σ δ_k` above the FIRST ensemble.

* **Linear accumulation of the net gain** (`distill_compound_gain`,
  the plan's `genMean_compound`): if every cycle combines a
  certified growth gain `c_k` with a distillation slack `δ_k` and
  the net `c_k − δ_k ≥ g > 0`, the distillate of generation n
  beats the initial ensemble by at least `n·g`. Honest target:
  only «distillate gen_k beats distillate gen_{k−1}» is certified
  — the distillate stays worse than the uncompressed joint,
  accepted by design.

* **The leak gate** (`distill_leak_gate`): a cycle with
  `c ≤ δ` has nonpositive net — the chain cannot improve through
  it; the loop must STOP (runtime: the per-cycle η-gate on
  the R134 distill efficiency, in efficiency, in nats).

* **Exhaustion of the disagreement field** (`harvest_budget`,
  `exhausted_when`): the disagreement D feeding growth decays
  geometrically (`D_{t+1} ≤ ρ·D_t`, `ρ < 1`); the total
  harvestable gain over any horizon is at most `γ·D_0/(1−ρ)`
  (the plan's `G* = D/(1−ρ)`), and once the remaining field
  `ρ^n·D_0` drops below `ε/γ` no future cycle can certify ε —
  EXHAUSTED: switch corpus, not more cycles.

All statements are conditional bookkeeping over ℝ-sequences with
NAMED premises (`hdist`, `hgrow`, `hnet`, `hdecay`, `hgain`); no
`h_emp_` premise hides inside. Sources: runtime plan §6b.1;
single-cycle bridge R134 (2609.38666 / 2607.15467 / 2609.39436);
geometric budget kernel R172 (`geom_sum_le_inv`).
-/

namespace Hagi.Ensemble

open Finset

variable {E S delta c : ℕ → ℝ}

/-! ## Telescoping of the bridge -/

/-- **The telescoping bridge** (§6b.1: the `distill_kl_bridge`
chain over generations). Cycle k: ensemble `E k` is distilled
into student `S k` (slack `delta k` — the single-cycle R134
bridge `KL_k + M_k‖q−p_E‖₁`), and the next ensemble `E (k+1)`
is grown FROM the distillate (no free relabeling gain). For
every k ≤ n and k < n respectively:

* `hdist k` : `S k ≤ E k + delta k`;
* `hgrow k` : `E (k + 1) ≤ S k`.

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
laws (`hgrow` in its improvement form + `hnet` positive net), each
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
plan's `genMean_compound`). Per cycle k < n: `hdist` (bridge
slack `delta k`), `hgrow` (the next ensemble improves on the
distillate by the certified gain `c k`), `hnet` (net
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
STOP (runtime: the per-cycle η-gate on the R134 distill
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
move is a NEW CORPUS (fresh disagreement), not more cycles. -/
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
