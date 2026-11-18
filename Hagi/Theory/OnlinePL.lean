/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEGlobalConvergence
import Hagi.Model.CEMarginPL

/-!
# Online PL tracking rate for a frozen extractor (streaming head)

C412. The streaming counterpart of the static PL convergence theory
(C351): data arrive sequentially, the extractor is FROZEN, and only
the head trains online with gradient descent (`plStep`, step `1/L`).
The per-round objective changes (`L_t`), so two regimes live here:

* STATIC (fixed distribution): per-t PL + smoothness give the
  geometric loss rate `(1 - μ/L)^T` of `margin_pl_convergence` —
  the C351 machinery applies verbatim per t; nothing new is needed.
* DYNAMIC (drifting optimum): the iterate TRACKS the moving optimum
  `θ*_t` with the affine recursion `d(t+1) ≤ q·d t + Δ`,
  `q = 1 - μ/L`, hence the steady-state radius `Δ·L/μ`.

Key honesty points (the C412 plan-review challenges):

* DISTANCE contraction needs STRONG CONVEXITY, not bare PL: PL alone
  bounds the loss gap (`pl_descent_step_at`); the bridge
  `sc_implies_pl` proves SC ⊂ PL, so the PL framing is consistent.
* The loss-tracking corollary uses smoothness at the optimum plus
  stationarity only (the `L/2·dist²` form) — no strong convexity of
  the distance argument is smuggled in.
* The drift `Δ` is a premise (drift binder): NO model of the
  distribution shift is given; per-t PL/SC constants are uniform
  (single μ, L); `grad θ*_t = 0` (stationarity of the current
  optimum) is a premise; confinement to a ball is NOT needed (global
  premise forms).
* `coco_half` has the non-sharp constant `1/(2M)`; the FINAL
  contraction constant is still exactly `1 - μ/L`.
* PL is not discharged for any concrete CE instance here — the
  margin route of `margin_pl_ball` is the intended per-head
  discharger.

Streaming composition pointer (C402): each `HeadPhase` of the
alternating joint training loop is a frozen-extractor head phase; its
per-phase certificate gets the rate form
`‖θ_t − θ*_t‖ ≤ (1 - μ/L)^t·d₀ + Δ·L/μ` and the induced loss bound of
`online_loss_tracking` — the phase-local optimum is the tracked
reference, and the phase-to-phase drift enters as the `Δ` binder.

no reference: Mathlib snapshot has no co-coercivity or PL-tracking
API (C351 survey); classical shift-plus-descent proof route adapted.
-/

open scoped InnerProductSpace

namespace Hagi.Theory.OnlinePL

open Hagi.Model.CEGlobalConvergence

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inner-product identity: `‖y‖² = ‖x‖² + 2⟪x, y−x⟫ + ‖y−x‖²`
(the shift-lemma of the quadratic argument; used to move the
strong-convexity and smoothness premises onto the shifted map
`f − μ/2‖·‖²`). -/
theorem norm_split (x y : E) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
  have h := norm_add_sq_real x (y - x)
  have hy : x + (y - x) = y := by abel
  rw [hy] at h
  exact h

/-- Expansion of `‖u − c • v‖²` (the one-step distance identity for a
gradient step `u = θ − θ*`, `c = 1/L`, `v = grad θ`). -/
theorem norm_sub_smul_sq (u v : E) (c : ℝ) :
    ‖u - c • v‖ ^ 2 = ‖u‖ ^ 2 - 2 * c * ⟪u, v⟫_ℝ + c ^ 2 * ‖v‖ ^ 2 := by
  have h := norm_add_sq_real u (-(c • v))
  have e : u - c • v = u + (-(c • v)) := by abel_nf
  have h1 : ⟪u, -(c • v)⟫_ℝ = -(c * ⟪u, v⟫_ℝ) := by
    rw [show -(c • v) = (-c) • v from (neg_smul c v).symm,
      real_inner_smul_right]
    ring
  have h2 : ‖-(c • v)‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
    rw [show -(c • v) = (-c) • v from (neg_smul c v).symm,
      norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
  rw [e, h, h1, h2]
  ring_nf

/-- Half co-coercivity from premise forms: a pair `(k, gk)` with the
first-order convexity form `k x + ⟪gk x, y−x⟫ ≤ k y` and the descent
lemma with constant `M` satisfies
`‖gk x − gk y‖²/(2M) ≤ ⟪gk x − gk y, x−y⟫`. Non-sharp constant
`1/(2M)` (the φ-trick: descent lemma at `x` toward
`x − (1/M)(gk x − gk y)`, sandwiched by the two convexity
directions); sufficient for the exact final constant of
`gd_dist_contraction`. -/
theorem coco_half (k : E → ℝ) (gk : E → E) (M : ℝ) (hM : 0 < M)
    (h_conv : ∀ x y : E, k x + ⟪gk x, y - x⟫_ℝ ≤ k y)
    (h_smooth : ∀ x y : E, k y ≤ k x + ⟪gk x, y - x⟫_ℝ + M / 2 * ‖y - x‖ ^ 2)
    (x y : E) :
    ‖gk x - gk y‖ ^ 2 / (2 * M) ≤ ⟪gk x - gk y, x - y⟫_ℝ := by
  set δ := gk x - gk y with hδ
  set u := x - (1 / M) • δ with hu
  have hsm := h_smooth x u
  have hin : ⟪gk x, u - x⟫_ℝ = -(1 / M) * ⟪gk x, δ⟫_ℝ := by
    rw [show u - x = (-(1 / M)) • δ from by rw [hu]; simp, real_inner_smul_right]
  have hns : ‖u - x‖ ^ 2 = (1 / M) ^ 2 * ‖δ‖ ^ 2 := by
    rw [show u - x = (-(1 / M)) • δ from by rw [hu]; simp, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity), mul_pow]
  rw [hin, hns] at hsm
  have hcoef : M / 2 * ((1 / M) ^ 2 * ‖δ‖ ^ 2) = ‖δ‖ ^ 2 / (2 * M) := by
    field_simp
  rw [hcoef] at hsm
  have hconv := h_conv y u
  rw [show u - y = (x - y) - (1 / M) • δ from by rw [hu, hδ]; abel,
    inner_sub_right, real_inner_smul_right] at hconv
  have hδin : ⟪gk x, δ⟫_ℝ - ⟪gk y, δ⟫_ℝ = ‖δ‖ ^ 2 := by
    rw [← inner_sub_left, hδ, real_inner_self_eq_norm_sq]
  have hD : (1 / M) * ‖δ‖ ^ 2 = 2 * (‖δ‖ ^ 2 / (2 * M)) := by
    field_simp
  have h2 : (1 / M) * ⟪gk x, δ⟫_ℝ - (1 / M) * ⟪gk y, δ⟫_ℝ
      = 2 * (‖δ‖ ^ 2 / (2 * M)) := by
    linear_combination (1 / M) * hδin + hD
  have key : k y + ⟪gk y, x - y⟫_ℝ + ‖δ‖ ^ 2 / (2 * M) ≤ k x := by
    linarith [hconv, hsm, h2]
  have hconx := h_conv x y
  have hxy : ⟪gk x, y - x⟫_ℝ = -⟪gk x, x - y⟫_ℝ := by
    rw [show y - x = -(x - y) by abel, inner_neg_right]
  have hxy2 : ⟪gk x, x - y⟫_ℝ - ⟪gk y, x - y⟫_ℝ
      = ⟪gk x - gk y, x - y⟫_ℝ := by
    rw [inner_sub_left]
  rw [hxy] at hconx
  nlinarith [key, hconx, hxy2, sq_nonneg (‖δ‖ : ℝ)]

/-- THE TRACKING STEP: one gradient descent step (`plStep`, step
size `1/L`) contracts the DISTANCE to a stationary point `θstar` by
the exact factor `1 − μ/L`, under strong convexity (`h_sconv`) and
smoothness (`h_smooth`, descent-lemma form) — both global premise
forms. Route: co-coercivity of the shifted map
`grad − μ·id` (`coco_half` with `M = L − μ`) gives
`‖grad θ‖² ≤ 2L(m − μ d²) + μ²d²`, and the one-step expansion yields
`(1 − μ/L)²d²`. Requires `0 < μ < L` (the shifted smoothness constant
`L − μ` must be positive). This is the honest replacement for the
false "PL ⟹ distance contraction": PL gives loss contraction only. -/
theorem gd_dist_contraction (f : E → ℝ) (grad : E → E) (L μ : ℝ) (hL : 0 < L)
    (hμ : 0 < μ) (hμL : μ < L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_sconv : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (θstar : E) (h_star : grad θstar = 0) (θ : E) :
    ‖plStep grad L θ - θstar‖ ≤ (1 - μ / L) * ‖θ - θstar‖ := by
  set M := L - μ with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  set k : E → ℝ := fun u => f u - μ / 2 * ‖u‖ ^ 2 with hk
  set gk : E → E := fun u => grad u - μ • u with hgk
  have hgkin : ∀ x y : E, ⟪gk x, y - x⟫_ℝ
      = ⟪grad x, y - x⟫_ℝ - μ * ⟪x, y - x⟫_ℝ := by
    intro x y
    rw [hgk]
    simp only
    rw [inner_sub_left, real_inner_smul_left]
  have h_conv : ∀ x y : E, k x + ⟪gk x, y - x⟫_ℝ ≤ k y := by
    intro x y
    have hs := h_sconv x y
    have hns := norm_split x y
    have hnsμ : μ / 2 * ‖y‖ ^ 2
        = μ / 2 * ‖x‖ ^ 2 + μ * ⟪x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 := by
      rw [hns]; ring
    rw [hgkin x y]
    simp only [hk]
    linarith
  have h_smooth' : ∀ x y : E,
      k y ≤ k x + ⟪gk x, y - x⟫_ℝ + M / 2 * ‖y - x‖ ^ 2 := by
    intro x y
    have hs := h_smooth x y
    have hns := norm_split x y
    have hnsμ : μ / 2 * ‖y‖ ^ 2
        = μ / 2 * ‖x‖ ^ 2 + μ * ⟪x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 := by
      rw [hns]; ring
    rw [hgkin x y]
    simp only [hk, hMdef]
    linarith
  have hco := coco_half k gk M hM h_conv h_smooth' θ θstar
  set δh : E := grad θ - μ • (θ - θstar) with hδh
  have hgkδh : gk θ - gk θstar = δh := by
    rw [hδh, hgk]
    simp only [h_star]
    module
  rw [hgkδh] at hco
  set d2 : ℝ := ‖θ - θstar‖ ^ 2 with hd2
  set m : ℝ := ⟪grad θ, θ - θstar⟫_ℝ with hm
  have hchin : ⟪δh, θ - θstar⟫_ℝ = m - μ * d2 := by
    rw [hδh, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hchin] at hco
  have hdl2 : ‖δh‖ ^ 2 ≤ 2 * M * (m - μ * d2) := by
    have h2M : 0 < 2 * M := by positivity
    have hc2 := (div_le_iff₀ h2M).mp hco
    linarith
  have hinner : ⟪δh, μ • (θ - θstar)⟫_ℝ = μ * (m - μ * d2) := by
    rw [real_inner_smul_right, hchin]
  have hnorms : ‖μ • (θ - θstar)‖ ^ 2 = μ ^ 2 * d2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hd2]
  have hG2 : ‖grad θ‖ ^ 2 ≤ 2 * L * (m - μ * d2) + μ ^ 2 * d2 := by
    have hexp := norm_add_sq_real δh (μ • (θ - θstar))
    have heq : δh + μ • (θ - θstar) = grad θ := by
      rw [hδh]; abel
    rw [heq, hinner, hnorms] at hexp
    have h2Mμ : 2 * M * (m - μ * d2) + 2 * (μ * (m - μ * d2))
        = 2 * L * (m - μ * d2) := by
      rw [hMdef]; ring
    linarith
  have hstep := norm_sub_smul_sq (θ - θstar) (grad θ) (1 / L)
  have hmodeq : (θ - θstar) - (1 / L) • grad θ = plStep grad L θ - θstar := by
    rw [plStep]; abel
  rw [hmodeq, real_inner_comm, ← hm, ← hd2] at hstep
  set c : ℝ := 1 - μ / L with hc
  have hcpos : 0 ≤ c := by
    rw [hc, sub_nonneg, div_le_one hL]
    linarith
  have hfinal : ‖plStep grad L θ - θstar‖ ^ 2 ≤ c ^ 2 * d2 := by
    have hmul : (1 / L) ^ 2 * ‖grad θ‖ ^ 2
        ≤ (1 / L) ^ 2 * (2 * L * (m - μ * d2) + μ ^ 2 * d2) :=
      mul_le_mul_of_nonneg_left hG2 (by positivity)
    have hE : d2 - 2 * (1 / L) * m
          + (1 / L) ^ 2 * (2 * L * (m - μ * d2) + μ ^ 2 * d2)
        = c ^ 2 * d2 := by
      have hmch : m = (m - μ * d2) + μ * d2 := by ring
      rw [hmch, hc]
      field_simp
      ring
    linarith
  have hcd : c ^ 2 * d2 = (c * ‖θ - θstar‖) ^ 2 := by
    rw [mul_pow, hd2]
  rw [hcd] at hfinal
  exact (abs_le_of_sq_le_sq' hfinal
    (mul_nonneg hcpos (norm_nonneg _))).2

/-- The SC ⊂ PL bridge: first-order strong convexity plus
stationarity of `θ*` (`grad θstar = 0`), `fstar = f θstar` and the
floor imply the PL inequality `2μ(f θ − fstar) ≤ ‖grad θ‖²` at every
point — so the static C351 machinery (`pl_descent_step_at`,
`margin_pl_convergence`) applies per t under SC. -/
theorem sc_implies_pl (f : E → ℝ) (grad : E → E) (μ fstar : ℝ) (hμ : 0 < μ)
    (h_sconv : ∀ x y : E, f x + ⟪grad x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (θstar : E) (_h_star : grad θstar = 0) (hval : f θstar = fstar)
    (h_floor : ∀ x : E, fstar ≤ f x) (θ : E) :
    2 * μ * (f θ - fstar) ≤ ‖grad θ‖ ^ 2 := by
  have hs := h_sconv θ θstar
  have hnegg : ⟪grad θ, θstar - θ⟫_ℝ = -⟪grad θ, θ - θstar⟫_ℝ := by
    rw [show θstar - θ = -(θ - θstar) from by abel, inner_neg_right]
  rw [hnegg] at hs
  rw [hval] at hs
  have hcs : ⟪grad θ, θ - θstar⟫_ℝ ≤ ‖grad θ‖ * ‖θ - θstar‖ :=
    real_inner_le_norm _ _
  have hkey : f θ - fstar + μ / 2 * ‖θ - θstar‖ ^ 2
      ≤ ‖grad θ‖ * ‖θ - θstar‖ := by
    have hf : (0:ℝ) ≤ f θ - fstar := by
      have := h_floor θ
      linarith
    rw [show ‖θstar - θ‖ ^ 2 = ‖θ - θstar‖ ^ 2 from by
      rw [show θstar - θ = -(θ - θstar) from by abel, norm_neg]]
    at hs
    linarith
  nlinarith [hkey, sq_nonneg (‖grad θ‖ - μ * ‖θ - θstar‖)]

/-- Loss-to-distance bound: smoothness at the optimum plus
stationarity give `f θ − f θstar ≤ (L/2)‖θ − θstar‖²` — the
`L`-Lipschitz-in-θ form of the loss gap (upper quadratic bound;
no strong convexity of the distance argument is used). -/
theorem loss_dist_bound (f : E → ℝ) (grad : E → E) (L : ℝ)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (θstar : E) (h_star : grad θstar = 0) (θ : E) :
    f θ - f θstar ≤ L / 2 * ‖θ - θstar‖ ^ 2 := by
  have hs := h_smooth θstar θ
  rw [h_star, inner_zero_left] at hs
  linarith

/-- The affine tracking recursion: `d(n+1) ≤ q·d n + Δ` with
`0 ≤ q < 1` and `0 ≤ Δ` implies `d n ≤ q^n·d 0 + Δ/(1−q)`.
Direct induction with the geometric partial sum (the C355
`nonlin_rec_bound` is a quadratic recursion — different algebra). With
`q = 1 − μ/L` the steady-state radius is `Δ/(1−q) = Δ·L/μ`. -/
theorem track_rec_bound {d : ℕ → ℝ} {q Δ : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hΔ : 0 ≤ Δ) (hrec : ∀ n : ℕ, d (n + 1) ≤ q * d n + Δ) (n : ℕ) :
    d n ≤ q ^ n * d 0 + Δ / (1 - q) := by
  have hq1le : q ≤ 1 := le_of_lt hq1
  have hkey : ∀ n : ℕ, d n ≤ q ^ n * d 0 + Δ * (1 - q ^ n) / (1 - q) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hrec n
      have hqpow : 0 ≤ q ^ n := pow_nonneg hq n
      have hne : (1:ℝ) - q ≠ 0 := sub_ne_zero_of_ne (by linarith)
      have hfield : q * (Δ * (1 - q ^ n) / (1 - q)) + Δ
          = Δ * (1 - q ^ (n + 1)) / (1 - q) := by
        rw [pow_succ]
        field_simp
        ring
      have hmul : q * d n
          ≤ q * (q ^ n * d 0 + Δ * (1 - q ^ n) / (1 - q)) :=
        mul_le_mul_of_nonneg_left ih hq
      have hlast : q * (q ^ n * d 0 + Δ * (1 - q ^ n) / (1 - q)) + Δ
          = q ^ (n + 1) * d 0 + Δ * (1 - q ^ (n + 1)) / (1 - q) := by
        have hd : q * (q ^ n * d 0 + Δ * (1 - q ^ n) / (1 - q)) + Δ
            = q * q ^ n * d 0 + (q * (Δ * (1 - q ^ n) / (1 - q)) + Δ) := by
          ring
        rw [hd, hfield]
        simp only [pow_succ]
        ring
      linarith [h, hmul, hlast]
  have hqn : q ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ k ih =>
      have h2 : q * q ^ k ≤ q * 1 := mul_le_mul_of_nonneg_left ih hq
      rw [mul_one] at h2
      rw [pow_succ]
      linarith
  have hmul2 : Δ * (1 - q ^ n) ≤ Δ := by
    have hle1 : (1:ℝ) - q ^ n ≤ 1 := by linarith [pow_nonneg hq n]
    have h3 : Δ * (1 - q ^ n) ≤ Δ * 1 := mul_le_mul_of_nonneg_left hle1 hΔ
    rw [mul_one] at h3
    exact h3
  have hdiv : Δ * (1 - q ^ n) / (1 - q) ≤ Δ / (1 - q) := by
    have hpos : (0:ℝ) < 1 - q := by linarith
    exact (div_le_div_iff_of_pos_right hpos).mpr hmul2
  linarith [hkey n, hdiv]

/-- MAIN TRACKING THEOREM: online gradient descent on the head
(`θ(t+1) = plStep (grad t) L (θ t)`) under frozen extractor tracks
the drifting optimum `θs t` within the geometric-plus-steady-state
envelope `(1 − μ/L)^n·d₀ + Δ·L/μ`, where `Δ` is the drift binder
(`‖θs(t+1) − θs t‖ ≤ Δ`, the distribution-shift premise) and each
`θs t` is stationary for its round objective (`grad t (θs t) = 0`).
Static case `Δ = 0`: pure geometric contraction to the fixed
optimum; per-t loss rate = `pl_descent_step_at` (C351) at each round. -/
theorem online_tracking (f : ℕ → E → ℝ) (grad : ℕ → E → E) (L μ Δ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ < L) (hΔ : 0 ≤ Δ)
    (h_smooth : ∀ t : ℕ, ∀ x y : E,
      f t y ≤ f t x + ⟪grad t x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_sconv : ∀ t : ℕ, ∀ x y : E,
      f t x + ⟪grad t x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f t y)
    (θs : ℕ → E) (h_star : ∀ t : ℕ, grad t (θs t) = 0)
    (h_drift : ∀ t : ℕ, ‖θs (t + 1) - θs t‖ ≤ Δ)
    (θ : ℕ → E)
    (h_step : ∀ t : ℕ, θ (t + 1) = plStep (grad t) L (θ t))
    (n : ℕ) :
    ‖θ n - θs n‖ ≤ (1 - μ / L) ^ n * ‖θ 0 - θs 0‖ + Δ * L / μ := by
  set q : ℝ := 1 - μ / L with hqdef
  have hq : 0 ≤ q := by
    rw [hqdef, sub_nonneg, div_le_one hL]
    linarith
  have hq1 : q < 1 := by
    rw [hqdef]
    linarith [div_pos hμ hL]
  have hrec : ∀ t : ℕ,
      ‖θ (t + 1) - θs (t + 1)‖ ≤ q * ‖θ t - θs t‖ + Δ := by
    intro t
    rw [h_step t]
    have hcontr := gd_dist_contraction (f t) (grad t) L μ hL hμ hμL
      (h_smooth t) (h_sconv t) (θs t) (h_star t) (θ t)
    have htri : ‖θ (t + 1) - θs (t + 1)‖
        ≤ ‖θ (t + 1) - θs t‖ + ‖θs t - θs (t + 1)‖ := by
      have h := dist_triangle (θ (t + 1)) (θs t) (θs (t + 1))
      rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
    have hdr' : ‖θs t - θs (t + 1)‖ ≤ Δ := by
      rw [norm_sub_rev]
      exact h_drift t
    rw [h_step t] at htri
    rw [← hqdef] at hcontr
    linarith
  have hmain := track_rec_bound hq hq1 hΔ hrec n
  have hconv : Δ / (1 - q) = Δ * L / μ := by
    rw [hqdef]
    have h1 : (1:ℝ) - (1 - μ / L) = μ / L := by ring
    rw [h1]
    field_simp
  rw [hconv] at hmain
  exact hmain

/-- LOSS-TRACKING COROLLARY: the per-round excess loss of the
online iterate is bounded by `(L/2)` times the square of the
tracking envelope — combining `loss_dist_bound` with
`online_tracking`. -/
theorem online_loss_tracking (f : ℕ → E → ℝ) (grad : ℕ → E → E) (L μ Δ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ < L) (hΔ : 0 ≤ Δ)
    (h_smooth : ∀ t : ℕ, ∀ x y : E,
      f t y ≤ f t x + ⟪grad t x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_sconv : ∀ t : ℕ, ∀ x y : E,
      f t x + ⟪grad t x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f t y)
    (θs : ℕ → E) (h_star : ∀ t : ℕ, grad t (θs t) = 0)
    (h_drift : ∀ t : ℕ, ‖θs (t + 1) - θs t‖ ≤ Δ)
    (θ : ℕ → E) (h_step : ∀ t : ℕ, θ (t + 1) = plStep (grad t) L (θ t))
    (n : ℕ) :
    f n (θ n) - f n (θs n)
      ≤ L / 2 * ((1 - μ / L) ^ n * ‖θ 0 - θs 0‖ + Δ * L / μ) ^ 2 := by
  have hloss := loss_dist_bound (f n) (grad n) L (h_smooth n) (θs n)
    (h_star n) (θ n)
  have htrack := online_tracking f grad L μ Δ hL hμ hμL hΔ h_smooth h_sconv θs
    h_star h_drift θ h_step n
  have hnn : (0:ℝ) ≤ (1 - μ / L) ^ n * ‖θ 0 - θs 0‖ + Δ * L / μ := by
    have h1 : (0:ℝ) ≤ (1 - μ / L) ^ n * ‖θ 0 - θs 0‖ :=
      mul_nonneg (pow_nonneg (by
        rw [sub_nonneg, div_le_one hL]
        linarith) n) (norm_nonneg _)
    have h2 : (0:ℝ) ≤ Δ * L / μ := by positivity
    linarith
  have hsq : L / 2 * ‖θ n - θs n‖ ^ 2
      ≤ L / 2 * ((1 - μ / L) ^ n * ‖θ 0 - θs 0‖ + Δ * L / μ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [htrack, hnn, norm_nonneg (θ n - θs n)]
  exact le_trans hloss hsq

end Hagi.Theory.OnlinePL
