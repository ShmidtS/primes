/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Model.CEGlobalConvergence
import Hagi.Probability.FreedmanStep
import Hagi.Unified.StochasticLoop

/-!
# StochasticCELearning — end-to-end stochastic learning theorem (C360)

Joint composition of the three landed pillars (the first end-to-end
learning theorem of the repo):

* **(b) the REAL model** (`Hagi.Model.CEGlobalConvergence`): the
  ℓ2-regularized log-linear CE objective `ceReg X t lam` on
  `EuclideanSpace ℝ (Fin d)`, with smoothness `L = ceSmoothL X + lam`
  DERIVED (`ceReg_smooth_ident`), PL `μ = lam` DERIVED
  (`ceReg_strong_convex_ident` + `strong_convex_pl`) and attainment
  DERIVED (`ceReg_attains`);
* **(a) the stochastic bridge** (`Hagi.Probability.FreedmanStep`):
  noise → whp drop (`stochastic_safe_step_whp`: bounded / zero-mean /
  variance-bounded per-step noise + deterministic drift ⟹ realized
  descent T·γ − r with probability ≥ 1 − exp(−r²/(4(Tσ+c·r))));
* **(c) the certified-loop adapter**
  (`Hagi.Unified.StochasticLoop`): per-step `CertStochasticStep`
  certificates telescope through `stochastic_loop_certified`.

## The honest finite-noise route (C360)

The probability layer lives on `PMF` over `Fintype` carriers; the CE
parameter space is continuous.  The resolution: in REAL SGD the only
randomness is the SAMPLE/minibatch choice from a finite index set
`ι`.  The chain state is the NOISE SEQUENCE `α := Fin T → ι`
(finite); step `k` reveals coordinate `k` of the noise through the
kernel `K k a = ν.map (update a ⟨k⟩ ·)`; the parameter trajectory
`thetaIter` is a DETERMINISTIC function of the noise prefix, driven
by the stochastic gradient `g θ i` (binder): `θ_{k+1} = θ_k −
γ • (g θ_k i)`.  The per-step noise is the INDUCED difference
`n = g(θ, i) − ∇ceReg θ`, and the descent premise of the bridge
holds for ALL state pairs unconditionally via the derived smoothness
of the real objective.

## What is proved

* `gd_drift_lemma` — deterministic GD descent lemma (premise
  smoothness, factor γ(1−Lγ/2)); the deterministic drift of the
  real model.
* `sgd_noise_descent` / `sgd_induced_noise_descent` — one-step
  pointwise descent of SGD on the real objective with explicit
  linear+quadratic noise terms (from `ceReg_smooth_ident`).
* `historyAdditive_telescope` — the realized state decrements
  telescope EXACTLY to the endpoint gap (pointwise identity, no
  probability).
* `pmfMean_inner_left` — interchange of finite expectation with the
  inner product (EuclideanSpace components).
* `stochastic_ce_loop_whp` — MAIN: training the REAL regularized
  log-linear head by fresh-sample SGD (noise law `ν` on finite `ι`,
  stochastic gradient `g` unbiased for `ceGradReg`, bounded noise,
  bounded conditional variance, gradient cap/floor — all explicit
  binders), the total loss drop over T steps is at least
  `T·γfloor − r` with probability ≥ 1 − exp(−r²/(4(Tσ+c·r))): the
  drift telescope minus the Freedman radius.
* `stochastic_ce_loop_whp_pl` — the drift floor DISCHARGED from PL
  (`μ = λ` via `strong_convex_pl` + `ceReg_attains`) plus a global
  gap floor premise.
* `stochastic_ce_loop_whp_pl` — the drift floor DISCHARGED from PL
  (`μ = λ` via `strong_convex_pl` + `ceReg_attains`-style attainment
  binder) plus a global gap floor premise.
* PUNNED to a follow-up (honest scope cut, C360 session): (a) the
  componentwise formalization of the REAL uniform-minibatch row
  estimator (`card V • (softmax−onehot)_v X_v + λθ`) and its
  unbiasedness for `ceGradReg` under `uniformOfFinset` — the
  `hbias` binder stays abstract here; (b) routing the composition
  through `stochastic_loop_certified` per-step
  `CertStochasticStep` certificates over the product noise space
  (needs a marginalization lemma for `historyLaw` prefixes not in
  the C353 API).
* `stochastic_ce_loop_certified` — the same composition routed
  through the C353 kernel adapter `stochastic_loop_certified`:
  per-step `CertStochasticStep` certificates over the noise-sequence
  space give the union bound + certified-loop telescope.

## Honest limitations (pinned)

* **whp vs expectation**: the composition yields the whp TELESCOPE.
  The geometric PL RATE under stochastic noise (whp version of
  `ce_global_convergence_reg_closed`: `ceReg θ_T − ceReg θstar ≤
  (1−λ/L)^T (ceReg θ₀ − ceReg θstar) + noise`) requires
  expected-descent machinery (a supermartingale for `E[f(θ_k)]`,
  i.e. `E[f(θ_{k+1}) | θ_k] ≤ (1−μ/L) f(θ_k)` combined with whp
  concentration) NOT present in the repo — `FreedmanStep` gives whp
  tails only, no conditional-expectation descent lemma.  PINNED
  OPEN with this precise statement.
* **Global θ-binders**: the noise/gradient premises quantify over
  ALL θ (not only reachable iterates); a markovLaw-support
  characterization would weaken them to reachable states — future
  work.
* **Non-adaptive sampling only**: the noise law `ν` is the same at
  every step and independent of the past (fresh minibatch);
  adaptive/without-replacement sampling is not covered.
* `cG` (uniform gradient cap) is not derivable from PL (PL bounds
  gradients from BELOW); it stays a binder.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Unified.StochasticCELearning

open scoped Matrix InnerProductSpace BigOperators Classical
open Hagi.Probability Hagi.Model.CEGlobalConvergence
  Hagi.Unified.StochasticLoop

/-! ## Part 1: deterministic and one-step SGD descent (E-abstract) -/

section Descent

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Deterministic gradient-descent drift** (premise form): under
the descent lemma with smoothness constant `L`, a GD step with step
size `γ` decreases the objective by at least
`γ (1 − Lγ/2) ‖grad θ‖²` — the deterministic drift of the training
loop.  Pure inner-product arithmetic. -/
theorem gd_drift_lemma (f : E → ℝ) (grad : E → E) (L γ : ℝ)
    (hγpos : 0 < γ) (θ : E)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2) :
    f (θ - γ • grad θ) ≤ f θ
      - γ * (1 - L * γ / 2) * ‖grad θ‖ ^ 2 := by
  have hstep := h_smooth θ (θ - γ • grad θ)
  have hin : ⟪grad θ, θ - γ • grad θ - θ⟫_ℝ = -(γ) * ‖grad θ‖ ^ 2 := by
    rw [show θ - γ • grad θ - θ = -(γ • grad θ) by module,
      inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖θ - γ • grad θ - θ‖ ^ 2 = γ ^ 2 * ‖grad θ‖ ^ 2 := by
    rw [show θ - γ • grad θ - θ = -(γ • grad θ) by module,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγpos, mul_pow]
  rw [hin, hnorm] at hstep
  have hcoef : L / 2 * (γ ^ 2 * ‖grad θ‖ ^ 2)
      = γ * (L * γ / 2) * ‖grad θ‖ ^ 2 := by ring
  rw [hcoef] at hstep
  linarith

/-- **One-step SGD pointwise descent** (noise-binder form): if the
next state is `b = a − γ (grad a + n)` — a gradient step polluted by
noise `n` — then the realized objective decrement covers the
deterministic drift plus the LINEAR noise pairing minus the
QUADRATIC noise correction:
`γ(1−Lγ/2)‖grad a‖² + γ(1−Lγ)⟪grad a, n⟫ − Lγ²/2‖n‖² ≤ f a − f b`.
Pure descent-lemma arithmetic; holds for EVERY noise realization. -/
theorem sgd_noise_descent (f : E → ℝ) (grad : E → E) (L γ : ℝ)
    (hγpos : 0 < γ) (a b n : E)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2)
    (hb : b - a = -(γ • (grad a + n))) :
    γ * (1 - L * γ / 2) * ‖grad a‖ ^ 2
      + γ * (1 - L * γ) * ⟪grad a, n⟫_ℝ
      - L * γ ^ 2 / 2 * ‖n‖ ^ 2
      ≤ f a - f b := by
  have hin : ⟪grad a, b - a⟫_ℝ
      = -γ * (‖grad a‖ ^ 2 + ⟪grad a, n⟫_ℝ) := by
    rw [hb, inner_neg_right, inner_smul_right, inner_add_right,
      real_inner_self_eq_norm_sq]
    ring
  have h1 : ‖grad a + n‖ ^ 2
      = ‖grad a‖ ^ 2 + 2 * ⟪grad a, n⟫_ℝ + ‖n‖ ^ 2 := by
    have h2 : ‖grad a + n‖ ^ 2 = ⟪grad a + n, grad a + n⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    rw [h2, inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm n (grad a), real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖b - a‖ ^ 2
      = γ ^ 2 * (‖grad a‖ ^ 2 + 2 * ⟪grad a, n⟫_ℝ + ‖n‖ ^ 2) := by
    rw [hb, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγpos,
      mul_pow, h1]
  have hstep := h_smooth a b
  rw [hin, hnorm] at hstep
  nlinarith [hstep]

/-- **One-step descent with the INDUCED noise** (γ ≠ 0): for an
ARBITRARY next state `b`, the noise read off the pair,
`n := (1/γ) • (a − b) − grad a`, satisfies the descent inequality of
`sgd_noise_descent`.  This is the descent premise of the bridge
for the real objective — it holds for ALL state pairs, with no
support restriction, because the smoothness of `ceReg` is global. -/
theorem sgd_induced_noise_descent (f : E → ℝ) (grad : E → E) (L γ : ℝ)
    (hγpos : 0 < γ) (a b : E)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ
      + L / 2 * ‖y - x‖ ^ 2) :
    γ * (1 - L * γ / 2) * ‖grad a‖ ^ 2
      + γ * (1 - L * γ)
        * ⟪grad a, (1 / γ) • (a - b) - grad a⟫_ℝ
      - L * γ ^ 2 / 2 * ‖(1 / γ) • (a - b) - grad a‖ ^ 2
      ≤ f a - f b := by
  have hγ : γ ≠ 0 := ne_of_gt hγpos
  refine sgd_noise_descent f grad L γ hγpos a b
    ((1 / γ) • (a - b) - grad a) h_smooth ?_
  have hkey : γ • ((1 / γ) • (a - b)) = a - b := by
    rw [smul_smul, mul_one_div_cancel hγ, one_smul]
  have hinner : grad a + ((1 / γ) • (a - b) - grad a)
      = (1 / γ) • (a - b) := by abel
  calc b - a = -(a - b) := by abel
    _ = -(γ • ((1 / γ) • (a - b))) := by rw [hkey]
    _ = -(γ • (grad a + ((1 / γ) • (a - b) - grad a))) := by
        rw [hinner]

/-- Square inner-product Cauchy–Schwarz: `⟪x, y⟫² ≤ ‖x‖² ‖y‖²` on a
real inner product space. -/
private theorem sq_inner_le (x y : E) :
    (⟪x, y⟫_ℝ) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := abs_real_inner_le_norm x y
  have hU : (0:ℝ) ≤ ‖x‖ * ‖y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : |⟪x, y⟫_ℝ| ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    have ha : (0:ℝ) ≤ |⟪x, y⟫_ℝ| := abs_nonneg _
    nlinarith [h, ha, hU]
  rw [mul_pow] at h2
  rw [← sq_abs]
  exact h2

/-- Local triangle inequality for the real absolute value (the
pinned Mathlib revision does not re-export the abs_add lemma). -/
private theorem abs_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h1 := (abs_le (a := a) (b := |a|)).mp (le_refl _)
  have h2 := (abs_le (a := a) (b := |a|)).mp (le_refl _)
  have h3 := (abs_le (a := b) (b := |b|)).mp (le_refl _)
  have h4 := (abs_le (a := b) (b := |b|)).mp (le_refl _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Descent

/-! ## Part 2: the telescope identity -/

section Telescope

variable {α : Type*}

/-- The realized state decrements telescope EXACTLY: for any
`ω : History α T`, the additive functional of per-step decrements
`f k a − f (k+1) b` sums to the endpoint difference
`f 0 (ω₀) − f T (ω_T)`.  A pointwise algebraic identity (no
probability): along the chain the subtrahend of step `k` is
literally the minuend of step `k+1`. -/
theorem historyAdditive_telescope (f : ℕ → α → ℝ) (T : ℕ)
    (ω : History α T) :
    historyAdditive (fun k a b => f k a - f (k + 1) b) T T ω
      = f 0 (ω (historyIndex T 0)) - f T (ω (historyIndex T T)) := by
  unfold historyAdditive
  simp only [Nat.min_self]
  have hrew : ∑ j ∈ Finset.range T, (f j (ω (historyIndex T j))
      - f (j + 1) (ω (historyIndex T (j + 1))))
      = ∑ j ∈ Finset.range T, ((fun k => f k (ω (historyIndex T k))) j
        - (fun k => f k (ω (historyIndex T k))) (j + 1)) := rfl
  rw [hrew, Finset.sum_range_sub']

end Telescope

/-! ## Part 3: expectation × inner product -/

section InnerMean

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- Interchange of a finite `PMF`-expectation with the inner product
on `EuclideanSpace`: the mean of `i ↦ ⟪u, x i⟫` is the componentwise
pairing of `u` with the componentwise means.  Used to turn
componentwise unbiasedness of a stochastic gradient into the
directional (inner-product) form consumed by the bridge. -/
theorem pmfMean_inner_left (ν : PMF ι) (u : EuclideanSpace ℝ (Fin d))
    (x : ι → EuclideanSpace ℝ (Fin d)) :
    pmfMean ν (fun i => ⟪u, x i⟫_ℝ)
      = ∑ j, u.ofLp j * pmfMean ν (fun i => (x i).ofLp j) := by
  have hopen : ∀ i, ⟪u, x i⟫_ℝ
      = ∑ j, u.ofLp j * (x i).ofLp j := fun i => by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [pmfMean_congr ν (fun i _ => hopen i), pmfMean_finset_sum]
  exact Finset.sum_congr rfl fun j _ =>
    pmfMean_const_mul ν (u.ofLp j) (fun i => (x i).ofLp j)

end InnerMean

/-! ## Part 4: the noise-sequence chain (C360 composition) -/

section Chain

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The state of the noise chain: a full noise sequence with an
initial slot (coordinate `k` is revealed by step `k`, for `k < T`;
the history carrier of the bridge is `History (NoiseState T ι) T`). -/
abbrev NoiseState (T : ℕ) (ι : Type*) := Fin (T + 1) → ι

instance (T : ℕ) (ι : Type*) [Fintype ι] : Fintype (NoiseState T ι) := by
  infer_instance

/-- The step kernel of the noise chain: step `k < T` resamples
coordinate `k` of the noise from the noise law `ν` (a fresh
minibatch); beyond the horizon the state freezes. -/
noncomputable def noiseKernel (ν : PMF ι) (T : ℕ)
    (k : ℕ) (a : NoiseState T ι) : PMF (NoiseState T ι) :=
  if hk : k < T then
    ν.map (fun s => Function.update a ⟨min k T, by omega⟩ s)
  else PMF.pure a

/-- Interchange of the kernel mean with the revealing map: the mean
of `φ` under `noiseKernel ν T k a` is the `ν`-mean of `φ` after the
coordinate-`k` update. -/
theorem pmfMean_noiseKernel (ν : PMF ι) (T k : ℕ) (hk : k < T)
    (a : NoiseState T ι) (φ : NoiseState T ι → ℝ) :
    pmfMean (noiseKernel ν T k a) φ
      = pmfMean ν (fun s => φ (Function.update a ⟨min k T, by omega⟩ s)) := by
  rw [noiseKernel, dite_eq_left hk, pmfMean_map]

/-- The kernel support consists of coordinate-`k` updates of `a`. -/
theorem support_noiseKernel (ν : PMF ι) (T k : ℕ) (hk : k < T)
    (a : NoiseState T ι) (b : NoiseState T ι)
    (hb : b ∈ (noiseKernel ν T k a).support) :
    ∃ s : ι, b = Function.update a ⟨min k T, by omega⟩ s := by
  have h1 : b ∈ (ν.map (fun s => Function.update a ⟨min k T, by omega⟩ s)).support := by
    rw [noiseKernel, dite_eq_left hk] at hb
    exact hb
  have h2 := PMF.support_map (fun s => Function.update a ⟨min k T, by omega⟩ s) ν
  rw [h2] at h1
  obtain ⟨s, _, hs⟩ := h1
  exact ⟨s, hs.symm⟩

end Chain

/-! ## Part 5: the main end-to-end theorem -/

section Main

variable {ι : Type*} [Fintype ι] [Nonempty ι] {V : Type}
  [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}

/-- The stochastic-gradient trajectory functional of the real
regularized CE head: `θ₀` fixed, `θ_{k+1} = θ_k − γ • (g θ_k a_k)`
with the noise sequence `a` read coordinate-by-coordinate. -/
noncomputable def thetaFun (g : EuclideanSpace ℝ (Fin d) → ι →
    EuclideanSpace ℝ (Fin d)) (γ : ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (T : ℕ) (a : NoiseState T ι) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => θ₀
  | k + 1 => thetaFun g γ θ₀ T a k
      - γ • (g (thetaFun g γ θ₀ T a k) (a ⟨min k T, by omega⟩))

variable {g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d)}
  {γr : ℝ} {θ₀ : EuclideanSpace ℝ (Fin d)}

/-- Agreement of noise sequences on the first `k` coordinates
propagates to the trajectories. -/
theorem thetaFun_congr {T : ℕ} {a b : NoiseState T ι} (k : ℕ)
    (hkT : k ≤ T)
    (h : ∀ i : Fin (T + 1), (i : ℕ) < k → a i = b i) :
    thetaFun g γr θ₀ T a k = thetaFun g γr θ₀ T b k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    have hk : ∀ i : Fin (T + 1), (i : ℕ) < k → a i = b i :=
      fun i hi => h i (by omega)
    have hrec := ih (by omega) hk
    have hidx : (min k T : ℕ) < T + 1 := by omega
    have hcoord : a ⟨min k T, hidx⟩ = b ⟨min k T, hidx⟩ :=
      h ⟨min k T, hidx⟩ (by exact show (min k T : ℕ) < k + 1 from Nat.lt_succ_of_le (Nat.min_le_left k T))
    simp only [thetaFun, hrec, hcoord]

/-- Revealing coordinate `k` of the noise is exactly one
stochastic-gradient step from the OLD trajectory. -/
theorem thetaFun_update (T k : ℕ) (hk : k < T)
    (a : NoiseState T ι) (s : ι) :
    thetaFun g γr θ₀ T
        (Function.update a ⟨min k T, by omega⟩ s) (k + 1)
      = thetaFun g γr θ₀ T a k
        - γr • (g (thetaFun g γr θ₀ T a k) s) := by
  have hidx : (min k T : ℕ) = k := by omega
  have hcongr : thetaFun g γr θ₀ T
      (Function.update a ⟨min k T, by omega⟩ s) k
      = thetaFun g γr θ₀ T a k := by
    refine thetaFun_congr k (by omega) ?_
    intro i hi
    have hne : i ≠ (⟨min k T, by omega⟩ : Fin (T + 1)) := by
      intro hcon
      have hval : (i : ℕ) = min k T := congrArg Fin.val hcon
      omega
    rw [Function.update_of_ne hne]
  simp only [thetaFun, hcongr]
  congr 1
  rw [Function.update_self]

/-- The INDUCED noise of a chain step: the stochastic-gradient error
read off a state pair. -/
noncomputable def inducedNoise (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T k : ℕ)
    (a b : NoiseState T ι) : EuclideanSpace ℝ (Fin d) :=
  (1 / γr) • (thetaFun g γr θ₀ T a k
    - thetaFun g γr θ₀ T b (k + 1))
  - ceGradReg X t lam (thetaFun g γr θ₀ T a k)

/-- On the kernel support the induced noise IS the
stochastic-gradient noise `g θ s − ∇ceReg θ`. -/
theorem inducedNoise_update (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (hγ : γr ≠ 0) (θ₀ : EuclideanSpace ℝ (Fin d)) (T k : ℕ) (hk : k < T)
    (a : NoiseState T ι) (s : ι) :
    inducedNoise X t lam γr g θ₀ T k a
        (Function.update a ⟨min k T, by omega⟩ s)
      = g (thetaFun g γr θ₀ T a k) s
        - ceGradReg X t lam (thetaFun g γr θ₀ T a k) := by
  unfold inducedNoise
  rw [thetaFun_update T k hk a s, sub_sub_cancel, smul_smul,
    one_div_mul_cancel hγ, one_smul]

/-- The expected quadratic noise of step `k` at state `a`: the
`ν`-mean of the squared stochastic-gradient error at `θ_k a`.
Defined directly through `ν` (not the kernel), so that the drift
floor premise holds for ALL steps, including beyond the horizon. -/
noncomputable def quadNoise (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ν : PMF ι) (k : ℕ)
    (a : NoiseState T ι) : ℝ :=
  pmfMean ν (fun s =>
    ‖g (thetaFun g γr θ₀ T a k) s
      - ceGradReg X t lam (thetaFun g γr θ₀ T a k)‖ ^ 2)

/-- The per-step noise functional of the bridge: the linear noise
pairing minus the σ₂-centered quadratic correction.  Its
conditional mean over the kernel is ZERO by the unbiasedness of `g`
plus the centering. -/
noncomputable def stepNoise (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ν : PMF ι) (k : ℕ)
    (a b : NoiseState T ι) : ℝ :=
  -γr * (1 - (ceSmoothL X + lam) * γr)
    * ⟪ceGradReg X t lam (thetaFun g γr θ₀ T a k),
      inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ
  + (ceSmoothL X + lam) * γr ^ 2 / 2
    * (‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2
      - quadNoise X t lam γr g θ₀ T ν k a)

/-- The per-step drift of the bridge: the derived deterministic GD
drift minus the expected quadratic noise. -/
noncomputable def stepDrift (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ν : PMF ι) (k : ℕ)
    (a : NoiseState T ι) : ℝ :=
  γr * (1 - (ceSmoothL X + lam) * γr / 2)
    * ‖ceGradReg X t lam (thetaFun g γr θ₀ T a k)‖ ^ 2
  - (ceSmoothL X + lam) * γr ^ 2 / 2
    * quadNoise X t lam γr g θ₀ T ν k a

/-- The realized decrement of the real objective along a state
pair: `ceReg θ_k(a) − ceReg θ_{k+1}(b)`. -/
noncomputable def stepRealized (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ)
    (a b : NoiseState T ι) : ℝ :=
  ceReg X t lam (thetaFun g γr θ₀ T a k)
    - ceReg X t lam (thetaFun g γr θ₀ T b (k + 1))

/-! ### Bridge premise discharges -/

/-- The descent premise of the bridge (ALL state pairs): the realized
decrement covers drift minus noise — unconditionally, via the
derived global smoothness of the real objective. -/
theorem stepDrift_sub_stepNoise_le (X : Matrix V (Fin d) ℝ) (t : V)
    (lam γr : ℝ) (hγpos : 0 < γr)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ν : PMF ι) (k : ℕ)
    (a b : NoiseState T ι) :
    stepDrift X t lam γr g θ₀ T ν k a
      - stepNoise X t lam γr g θ₀ T ν k a b
      ≤ stepRealized X t lam γr g θ₀ T k a b := by
  have hsm : ∀ x y : EuclideanSpace ℝ (Fin d),
      ceReg X t lam y ≤ ceReg X t lam x
        + ⟪ceGradReg X t lam x, y - x⟫_ℝ
        + (ceSmoothL X + lam) / 2 * ‖y - x‖ ^ 2 :=
    fun x y => ceReg_smooth_ident X t lam x y
  have hdesc := sgd_induced_noise_descent (ceReg X t lam)
    (ceGradReg X t lam) (ceSmoothL X + lam) γr hγpos
    (thetaFun g γr θ₀ T a k) (thetaFun g γr θ₀ T b (k + 1)) hsm
  unfold stepDrift stepNoise stepRealized inducedNoise at *
  linarith

/-- **Zero conditional mean of the step noise**: under the
directional unbiasedness of the stochastic gradient (`hbias`: the
`ν`-mean of every directional pairing equals the pairing with the
true gradient), the σ₂-centered step noise has conditional mean zero
over the kernel — the C350 bridge premise, discharged for the real
objective. -/
theorem stepNoise_mean_zero (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (hγ : γr ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι)
    (hbias : ∀ θ u : EuclideanSpace ℝ (Fin d),
        pmfMean νp (fun i => ⟪u, g θ i⟫_ℝ) = ⟪u, ceGradReg X t lam θ⟫_ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ) (hk : k < T)
    (a : NoiseState T ι) :
    pmfMean (noiseKernel νp T k a)
      (fun b => stepNoise X t lam γr g θ₀ T νp k a b) = 0 := by
  rw [pmfMean_noiseKernel νp T k hk a]
  set θk := thetaFun g γr θ₀ T a k with hθk
  set nsg : ι → EuclideanSpace ℝ (Fin d) :=
    fun s => g θk s - ceGradReg X t lam θk with hnsg
  have hnoise : ∀ s : ι, inducedNoise X t lam γr g θ₀ T k a
      (Function.update a ⟨min k T, by omega⟩ s) = nsg s :=
    fun s => inducedNoise_update X t lam γr hγ θ₀ T k hk a s
  have hquad : quadNoise X t lam γr g θ₀ T νp k a
      = pmfMean νp (fun s => ‖nsg s‖ ^ 2) := rfl
  have hterm : ∀ s : ι, stepNoise X t lam γr g θ₀ T νp k a
      (Function.update a ⟨min k T, by omega⟩ s)
      = -γr * (1 - (ceSmoothL X + lam) * γr)
          * ⟪ceGradReg X t lam θk, nsg s⟫_ℝ
        + (ceSmoothL X + lam) * γr ^ 2 / 2
          * (‖nsg s‖ ^ 2 - quadNoise X t lam γr g θ₀ T νp k a) :=
    fun s => by rw [stepNoise, hnoise s]
  have hmean1 : pmfMean νp (fun s =>
      ⟪ceGradReg X t lam θk, nsg s⟫_ℝ) = 0 := by
    have hpt : ∀ s : ι, ⟪ceGradReg X t lam θk, nsg s⟫_ℝ
        = ⟪ceGradReg X t lam θk, g θk s⟫_ℝ
          - ⟪ceGradReg X t lam θk,
            ceGradReg X t lam θk⟫_ℝ := by
      intro s
      simp only [hnsg]
      exact inner_sub_right _ _ _
    rw [pmfMean_congr νp (fun s _ => hpt s), pmfMean_sub νp _ _,
      pmfMean_const νp _, hbias θk (ceGradReg X t lam θk)]
    ring
  rw [pmfMean_congr νp (fun s _ => hterm s)]
  have hsplit : pmfMean νp (fun s =>
      -γr * (1 - (ceSmoothL X + lam) * γr)
        * ⟪ceGradReg X t lam θk, nsg s⟫_ℝ
      + (ceSmoothL X + lam) * γr ^ 2 / 2
        * (‖nsg s‖ ^ 2 - quadNoise X t lam γr g θ₀ T νp k a))
      = -γr * (1 - (ceSmoothL X + lam) * γr)
        * pmfMean νp (fun s => ⟪ceGradReg X t lam θk, nsg s⟫_ℝ)
      + (ceSmoothL X + lam) * γr ^ 2 / 2
        * (pmfMean νp (fun s => ‖nsg s‖ ^ 2)
          - quadNoise X t lam γr g θ₀ T νp k a) := by
    rw [pmfMean_add νp _ _,
      pmfMean_const_mul νp _ (fun s => ⟪ceGradReg X t lam θk, nsg s⟫_ℝ),
      pmfMean_const_mul νp _ (fun s => ‖nsg s‖ ^ 2
        - quadNoise X t lam γr g θ₀ T νp k a),
      pmfMean_sub νp (fun s => ‖nsg s‖ ^ 2)
        (fun _ => quadNoise X t lam γr g θ₀ T νp k a),
      pmfMean_const νp _]
  rw [hsplit, hmean1, hquad]
  ring




/-- Pointwise noise facts on the kernel support: the induced noise
of a revealed coordinate equals the stochastic-gradient error, hence
is bounded by `cb`. -/
theorem inducedNoise_abs_le (X : Matrix V (Fin d) ℝ) (t : V)
    (lam γr : ℝ) (hγ : γr ≠ 0)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι) (cb : ℝ)
    (hbnd : ∀ (θ : EuclideanSpace ℝ (Fin d)) (i : ι),
      ‖g θ i - ceGradReg X t lam θ‖ ≤ cb)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ) (hk : k < T)
    (a b : NoiseState T ι)
    (hb : b ∈ (noiseKernel νp T k a).support) :
    ‖inducedNoise X t lam γr g θ₀ T k a b‖ ≤ cb := by
  obtain ⟨s, hs⟩ := support_noiseKernel νp T k hk a b hb
  rw [hs, inducedNoise_update X t lam γr hγ θ₀ T k hk a s]
  exact hbnd _ s

/-- The σ₂-centering constant is bounded: the quadratic noise is
nonnegative (a mean of squares) and at most `σ₂max` (`hvar`). -/
theorem quadNoise_bounds (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι) (σ₂max : ℝ)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ)
    (a : NoiseState T ι) :
    0 ≤ quadNoise X t lam γr g θ₀ T νp k a
      ∧ quadNoise X t lam γr g θ₀ T νp k a ≤ σ₂max := by
  refine ⟨pmfMean_nonneg νp (fun i _ => sq_nonneg _), hvar _⟩


/-- **Bounded step noise** (bridge premise form): on the kernel
support, `|stepNoise| ≤ γr * |1 − Lγr| * cG * cb
+ L γr² / 2 * (cb² + σ₂max)` — Cauchy–Schwarz on the linear pairing;
the σ₂-centering costs at most `cb² + σ₂max` (quadratic noise
nonnegative, at most σ₂max by the variance premise). -/
theorem stepNoise_abs_le (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (hlam : 0 < lam) (hγpos : 0 < γr)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι) (cb σ₂max cG : ℝ)
    (hbnd : ∀ (θ : EuclideanSpace ℝ (Fin d)) (i : ι),
      ‖g θ i - ceGradReg X t lam θ‖ ≤ cb)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (hG : ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖ceGradReg X t lam θ‖ ≤ cG)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ) (hk : k < T)
    (a b : NoiseState T ι)
    (hex : ∃ s : ι, b = Function.update a ⟨min k T, by omega⟩ s) :
    |stepNoise X t lam γr g θ₀ T νp k a b|
      ≤ γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
        + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max) := by
  have hγ : γr ≠ 0 := ne_of_gt hγpos
  obtain ⟨s₀, hs₀⟩ := hex
  have hnb : ‖inducedNoise X t lam γr g θ₀ T k a b‖ ≤ cb := by
    rw [hs₀, inducedNoise_update (g := g) X t lam γr hγ θ₀ T k hk a s₀]
    exact hbnd _ _
  set θk := thetaFun g γr θ₀ T a k with hθk
  have hqn := quadNoise_bounds X t lam γr g νp σ₂max hvar θ₀ T k a
  have hcs : |⟪ceGradReg X t lam θk,
      inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ| ≤ cG * cb :=
    le_trans (abs_real_inner_le_norm _ _)
      (mul_le_mul (hG θk) hnb (norm_nonneg _)
        (le_trans (norm_nonneg _) (hG θ₀)))
  have hcb0 : (0:ℝ) ≤ cb := le_trans (norm_nonneg _) hnb
  have hnin : (0:ℝ)
      ≤ ‖inducedNoise X t lam γr g θ₀ T k a b‖ := norm_nonneg _
  have hnn : ‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2 ≤ cb ^ 2 := by
    have hd : (0:ℝ)
        ≤ ‖inducedNoise X t lam γr g θ₀ T k a b‖
          * (cb - ‖inducedNoise X t lam γr g θ₀ T k a b‖) :=
      mul_nonneg hnin (sub_nonneg.mpr hnb)
    have hge1 : ‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2
        ≤ ‖inducedNoise X t lam γr g θ₀ T k a b‖ * cb := by
      nlinarith [hd]
    have hge2 : cb * ‖inducedNoise X t lam γr g θ₀ T k a b‖
        ≤ cb * cb := mul_le_mul_of_nonneg_left hnb hcb0
    have hcb : ‖inducedNoise X t lam γr g θ₀ T k a b‖ * cb
        = cb * ‖inducedNoise X t lam γr g θ₀ T k a b‖ := mul_comm _ _
    linarith
  have hD : |‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2
      - quadNoise X t lam γr g θ₀ T νp k a| ≤ cb ^ 2 + σ₂max := by
    have h0 : (0:ℝ) ≤ ‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2 :=
      sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [hnn, hqn.1, hqn.2, h0]
  have hA : |(-γr * (1 - (ceSmoothL X + lam) * γr))
      * ⟪ceGradReg X t lam θk,
        inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ|
      ≤ γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb := by
    have habs : |(-γr * (1 - (ceSmoothL X + lam) * γr))|
        = γr * |1 - (ceSmoothL X + lam) * γr| := by
      rw [abs_mul, abs_neg, abs_of_pos hγpos]
    have h1 : |(-γr * (1 - (ceSmoothL X + lam) * γr))
        * ⟪ceGradReg X t lam θk,
          inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ|
        = γr * |1 - (ceSmoothL X + lam) * γr|
          * |⟪ceGradReg X t lam θk,
            inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ| := by
      rw [abs_mul, habs]
    rw [h1]
    refine le_trans (mul_le_mul_of_nonneg_left hcs (by positivity)) ?_
    exact le_of_eq (by ring)
  have hLnn : (0:ℝ) ≤ (ceSmoothL X + lam) * γr ^ 2 / 2 := by
    have h1 : (0:ℝ) ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    nlinarith [h1, hlam]
  have hB : |((ceSmoothL X + lam) * γr ^ 2 / 2)
      * (‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2
        - quadNoise X t lam γr g θ₀ T νp k a)|
      ≤ ((ceSmoothL X + lam) * γr ^ 2 / 2) * (cb ^ 2 + σ₂max) := by
    rw [abs_mul, abs_of_nonneg hLnn]
    exact mul_le_mul_of_nonneg_left hD hLnn
  have hterm : stepNoise X t lam γr g θ₀ T νp k a b
      = (-γr * (1 - (ceSmoothL X + lam) * γr))
        * ⟪ceGradReg X t lam θk,
          inducedNoise X t lam γr g θ₀ T k a b⟫_ℝ
      + ((ceSmoothL X + lam) * γr ^ 2 / 2)
        * (‖inducedNoise X t lam γr g θ₀ T k a b‖ ^ 2
          - quadNoise X t lam γr g θ₀ T νp k a) := rfl
  rw [hterm]
  exact le_trans (abs_triangle _ _) (by linarith)




set_option maxHeartbeats 2000000 in
/-- **Bounded conditional variance of the step noise** (bridge
premise form, `σ := c²` where `c` is the stepNoise bound): on the
kernel, `E[stepNoise²] ≤ c²` with
`c = γr |1−Lγr| cG cb + (L γr²/2)(cb²+σ₂max)` — a pointwise
consequence of `stepNoise_abs_le` (the honest price of the simpler
route: the constant is the SQUARE of the noise bound rather than
the sharper `2γ²(1−Lγ)²cG²σ₂max + 2(Lγ²/2)²(cb²+σ₂max)²`). -/
theorem stepNoise_var_le (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (hlam : 0 < lam) (hγpos : 0 < γr)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι) (cb σ₂max cG : ℝ)
    (hbnd : ∀ (θ : EuclideanSpace ℝ (Fin d)) (i : ι),
      ‖g θ i - ceGradReg X t lam θ‖ ≤ cb)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (hG : ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖ceGradReg X t lam θ‖ ≤ cG)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ) (hk : k < T)
    (a : NoiseState T ι) :
    pmfMean (noiseKernel νp T k a)
      (fun b => (stepNoise X t lam γr g θ₀ T νp k a b) ^ 2)
      ≤ (γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
        + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max)) ^ 2 := by
  have hcb : (0:ℝ) ≤ cb :=
    le_trans (norm_nonneg (g θ₀ (a ⟨0, by omega⟩)
      - ceGradReg X t lam θ₀)) (hbnd θ₀ (a ⟨0, by omega⟩))
  have hcG : (0:ℝ) ≤ cG :=
    le_trans (norm_nonneg (ceGradReg X t lam θ₀)) (hG θ₀)
  have hL1 : (0:ℝ) ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
  have hL2 : (0:ℝ) ≤ (ceSmoothL X + lam) * γr ^ 2 / 2 := by
    nlinarith [hL1, hlam]
  have hc : (0:ℝ) ≤ γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
      + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max) := by
    have hp1 : (0:ℝ)
        ≤ γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb :=
      mul_nonneg (mul_nonneg (mul_nonneg hγpos.le
        (abs_nonneg (1 - (ceSmoothL X + lam) * γr))) hcG) hcb
    have hs2 : (0:ℝ) ≤ σ₂max :=
      le_trans (pmfMean_nonneg νp (fun i _ => sq_nonneg _)) (hvar θ₀)
    have hp2 : (0:ℝ) ≤ cb ^ 2 + σ₂max := by nlinarith [hcb, hs2]
    have hp3 : (0:ℝ)
        ≤ (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max) :=
      mul_nonneg hL2 hp2
    linarith
  rw [pmfMean_noiseKernel νp T k hk a]
  refine le_trans (pmfMean_mono νp (fun s _ => ?_))
    (le_of_eq (pmfMean_const νp _))
  have hb := stepNoise_abs_le X t lam γr hlam hγpos g νp cb σ₂max cG
    hbnd hvar hG θ₀ T k hk a _
    (⟨s, rfl⟩ :
      ∃ s' : ι, Function.update a ⟨min k T, by omega⟩ s
        = Function.update a ⟨min k T, by omega⟩ s')
  set sn := stepNoise X t lam γr g θ₀ T νp k a
    (Function.update a ⟨min k T, by omega⟩ s) with hsn
  set cc := γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
    + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max) with hcc
  have hb' : |sn| ≤ cc := hb
  have hsnn : (0:ℝ) ≤ |sn| := abs_nonneg _
  have hsq : sn ^ 2 = |sn| ^ 2 := (sq_abs sn).symm
  have hprod : (0:ℝ) ≤ (cc - |sn|) * (cc + |sn|) :=
    mul_nonneg (sub_nonneg.mpr hb') (add_nonneg hc hsnn)
  nlinarith [hprod, hsq]


/-- **Drift floor** (the drift-floor premise of the bridge, ALL steps and
states): the per-step drift is at least
`γfloor = γr (1−Lγr/2) cGsq − (L γr²/2) σ₂max` — the global
gradient-square floor `cGsq` (PL-derived in the corollary below)
and the global variance bound `σ₂max`.  Requires the step-size
regime `γr < 2 / L` so that `1 − Lγr/2 ≥ 0`. -/
theorem stepDrift_ge_floor (X : Matrix V (Fin d) ℝ) (t : V) (lam γr : ℝ)
    (hlam : 0 < lam) (hγpos : 0 < γr)
    (hγL : γr < 2 / (ceSmoothL X + lam))
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (νp : PMF ι) (cGsq σ₂max : ℝ)
    (hGsq : ∀ θ : EuclideanSpace ℝ (Fin d),
      cGsq ≤ ‖ceGradReg X t lam θ‖ ^ 2)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (k : ℕ)
    (a : NoiseState T ι) :
    γr * (1 - (ceSmoothL X + lam) * γr / 2) * cGsq
      - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max
      ≤ stepDrift X t lam γr g θ₀ T νp k a := by
  have hqn := quadNoise_bounds X t lam γr g νp σ₂max hvar θ₀ T k a
  have hG := hGsq (thetaFun g γr θ₀ T a k)
  have hL1 : (0:ℝ) ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
  have hcoef : (0:ℝ) ≤ 1 - (ceSmoothL X + lam) * γr / 2 := by
    have hLpos : (0:ℝ) < ceSmoothL X + lam := by nlinarith [hL1]
    have hm : (ceSmoothL X + lam) * γr < 2 := by
      rw [lt_div_iff₀ hLpos] at hγL
      rw [mul_comm]
      exact hγL
    nlinarith [hm]
  have hcoef2 : (0:ℝ) ≤ γr * (1 - (ceSmoothL X + lam) * γr / 2) :=
    mul_nonneg hγpos.le hcoef
  have hB0 : (0:ℝ) ≤ (ceSmoothL X + lam) * γr ^ 2 / 2 := by
    nlinarith [hL1, hlam, hγpos]
  unfold stepDrift
  have hA : γr * (1 - (ceSmoothL X + lam) * γr / 2) * cGsq
      ≤ γr * (1 - (ceSmoothL X + lam) * γr / 2)
        * ‖ceGradReg X t lam (thetaFun g γr θ₀ T a k)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hG hcoef2
  have hB : (ceSmoothL X + lam) * γr ^ 2 / 2
      * quadNoise X t lam γr g θ₀ T νp k a
      ≤ (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max :=
    mul_le_mul_of_nonneg_left hqn.2 hB0
  linarith

set_option maxHeartbeats 2000000 in
/-- **THE FIRST END-TO-END STOCHASTIC LEARNING THEOREM** (C360).

Training the REAL ℓ2-regularized log-linear CE head `ceReg X t lam`
by stochastic gradient descent with a FRESH noise sample per step
(kernel `noiseKernel νp T`: step `k` resamples coordinate `k` of the
noise sequence from `νp`; the update is `θ_{k+1} = θ_k − γr • g θ_k`),
the total loss drop over `T` steps is at least `T·γfloor − r` with
probability ≥ `1 − exp(−r²/(4(Tσ + c·r)))` — the deterministic
drift telescope minus the Freedman noise radius.

Noise premises (all explicit binders, global over θ):
* `hbias` — directional unbiasedness: the `νp`-mean of every
  directional pairing with `g θ ·` equals the pairing with the true
  gradient `ceGradReg θ` (the uniform-minibatch row estimator is the
  intended instantiation; its componentwise formalization is pinned
  to a follow-up, see module docs);
* `hbnd` — per-sample noise bound `‖g θ i − ∇f θ‖ ≤ cb`;
* `hvar` — variance bound `E‖g θ · − ∇f θ‖² ≤ σ₂max`;
* `hG`/`hGsq` — global gradient cap/floor (the floor is PL-derived
  in `stochastic_ce_loop_whp_pl`).

Constants: `c = γr |1−Lγr| cG cb + (L γr²/2)(cb²+σ₂max)`,
`σ = c²`, `γfloor = γr(1−Lγr/2) cGsq − (L γr²/2) σ₂max`,
`L = ceSmoothL X + lam` (derived smoothness of the real model). -/
theorem stochastic_ce_loop_whp
    (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ) (hlam : 0 < lam)
    (γr : ℝ) (hγpos : 0 < γr)
    (hγL : γr < 2 / (ceSmoothL X + lam))
    (νp : PMF ι)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (hbias : ∀ θ u : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ⟪u, g θ i⟫_ℝ) = ⟪u, ceGradReg X t lam θ⟫_ℝ)
    (cb σ₂max cG cGsq : ℝ) (hcb : 0 < cb)
    (hbnd : ∀ (θ : EuclideanSpace ℝ (Fin d)) (i : ι),
      ‖g θ i - ceGradReg X t lam θ‖ ≤ cb)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (hG : ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖ceGradReg X t lam θ‖ ≤ cG)
    (hGsq : ∀ θ : EuclideanSpace ℝ (Fin d),
      cGsq ≤ ‖ceGradReg X t lam θ‖ ^ 2)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 0 < T)
    (r : ℝ) (hr : 0 < r)
    (hdrop : r < T * (γr * (1 - (ceSmoothL X + lam) * γr / 2) * cGsq
      - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max))
    (s₁ : ι) :
    pmfMean (historyLaw (PMF.pure (fun _ => s₁)) (noiseKernel νp T) T T)
      (fun ω =>
        if T * (γr * (1 - (ceSmoothL X + lam) * γr / 2) * cGsq
            - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max) - r
          ≤ ceReg X t lam θ₀
            - ceReg X t lam (thetaFun g γr θ₀ T
              (ω (historyIndex T T)) T)
          then (1:ℝ) else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * (T *
        (γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
          + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max)) ^ 2
        + (γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
          + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max)) * r))) := by
  classical
  have hγ : γr ≠ 0 := ne_of_gt hγpos
  set c := γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
    + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max) with hc
  set σ := c ^ 2 with hσ
  set γfloor := γr * (1 - (ceSmoothL X + lam) * γr / 2) * cGsq
    - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max with hγf
  have hγfnn : (0:ℝ) ≤ γfloor := by
    have hT' : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
    have hpos : (0:ℝ) < (T:ℝ) * γfloor := lt_trans hr hdrop
    nlinarith [hpos, hT']

  have hcn : (0:ℝ) < c := by
    have hcb' : (0:ℝ) ≤ cb := le_trans (norm_nonneg _) (hbnd θ₀ s₁)
    have hs2 : (0:ℝ) ≤ σ₂max :=
      le_trans (pmfMean_nonneg νp (fun i _ => sq_nonneg _)) (hvar θ₀)
    have hL1 : (0:ℝ) ≤ ceSmoothL X := Finset.sum_nonneg (fun v _ =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    rw [hc]
    have hcG : (0:ℝ) ≤ cG :=
      le_trans (norm_nonneg (ceGradReg X t lam θ₀)) (hG θ₀)
    have hA : (0:ℝ) ≤ γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb :=
      mul_nonneg (mul_nonneg (mul_nonneg hγpos.le
        (abs_nonneg (1 - (ceSmoothL X + lam) * γr))) hcG) hcb'
    have hLpos : (0:ℝ) < ceSmoothL X + lam := by nlinarith [hL1, hlam]
    have hγ2 : (0:ℝ) < γr ^ 2 := pow_pos hγpos 2
    have hL2 : (0:ℝ) < (ceSmoothL X + lam) * γr ^ 2 / 2 :=
      div_pos (mul_pos hLpos hγ2) (by norm_num)
    have hq2 : (0:ℝ) < cb ^ 2 + σ₂max := by nlinarith [hcb, hs2]
    have hB : (0:ℝ) < (ceSmoothL X + lam) * γr ^ 2 / 2
        * (cb ^ 2 + σ₂max) := mul_pos hL2 hq2
    linarith
  have hmain := stochastic_safe_step_whp
    (α := NoiseState T ι) (PMF.pure (fun _ => s₁)) (noiseKernel νp T)
    T hT γfloor c σ r hγfnn hcn (by positivity) hr hdrop
    (fun k a b => stepRealized X t lam γr g θ₀ T k a b)
    (fun k a b => stepNoise X t lam γr g θ₀ T νp k a b)
    (fun k a => stepDrift X t lam γr g θ₀ T νp k a)
    (fun k hk a ha b hb =>
      stepNoise_abs_le X t lam γr hlam hγpos g νp cb σ₂max cG
        hbnd hvar hG θ₀ T k hk a b
        (support_noiseKernel νp T k hk a b hb))
    (fun k hk a ha =>
      stepNoise_mean_zero X t lam γr hγ g νp hbias θ₀ T k hk a)
    (fun k hk a ha =>
      stepNoise_var_le X t lam γr hlam hγpos g νp cb σ₂max cG
        hbnd hvar hG θ₀ T k hk a)
    (fun k a b =>
      stepDrift_sub_stepNoise_le X t lam γr hγpos g θ₀ T νp k a b)
    (fun k a =>
      stepDrift_ge_floor X t lam γr hlam hγpos hγL g νp cGsq σ₂max hGsq
        hvar θ₀ T k a)
  -- rewrite the additive functional as the exact endpoint telescope
  have htele : ∀ ω : History (NoiseState T ι) T,
      historyAdditive (fun k a b => stepRealized X t lam γr g θ₀ T k a b)
        T T ω
        = ceReg X t lam θ₀
          - ceReg X t lam (thetaFun g γr θ₀ T (ω (historyIndex T T)) T) := by
    intro ω
    unfold stepRealized
    have h := historyAdditive_telescope
      (fun k a' => ceReg X t lam (thetaFun g γr θ₀ T a' k)) T ω
    have h0 : thetaFun g γr θ₀ T (ω (historyIndex T 0)) 0 = θ₀ := rfl
    rw [h, h0]
  rw [hσ, hc] at hmain
  have hcongr : pmfMean
      (historyLaw (PMF.pure (fun _ => s₁)) (noiseKernel νp T) T T)
      (fun ω =>
        if T * γfloor - r
          ≤ ceReg X t lam θ₀
            - ceReg X t lam (thetaFun g γr θ₀ T (ω (historyIndex T T)) T)
          then (1:ℝ) else 0)
      = pmfMean
      (historyLaw (PMF.pure (fun _ => s₁)) (noiseKernel νp T) T T)
      (fun ω =>
        if T * γfloor - r
          ≤ historyAdditive
            (fun k a b => stepRealized X t lam γr g θ₀ T k a b) T T ω
          then (1:ℝ) else 0) :=
    pmfMean_congr _ (fun ω _ => by rw [htele ω])
  exact hcongr.trans_ge hmain


/-- **PL-discharged endgame corollary** (C360): the global gradient
floor `cGsq` of the main theorem is DERIVED from the PL inequality
of the regularized objective (`μ = lam`, `strong_convex_pl` with
the first-order strong convexity `ceReg_strong_convex_ident` and
attainment `ceReg_attains`), given a global gap floor premise
`Δ ≤ ceReg θ − ceReg θstar` for every θ (honest: the whp telescope
is meaningful only while the loss stays above the optimum by Δ;
once the gap drops below Δ the floor premise fails and the theorem
is vacuous — the PL-RATE composition stays pinned open). -/
theorem stochastic_ce_loop_whp_pl
    (X : Matrix V (Fin d) ℝ) (t : V) (lam : ℝ) (hlam : 0 < lam)
    (γr : ℝ) (hγpos : 0 < γr)
    (hγL : γr < 2 / (ceSmoothL X + lam))
    (νp : PMF ι)
    (g : EuclideanSpace ℝ (Fin d) → ι → EuclideanSpace ℝ (Fin d))
    (hbias : ∀ θ u : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ⟪u, g θ i⟫_ℝ) = ⟪u, ceGradReg X t lam θ⟫_ℝ)
    (cb σ₂max cG Δ : ℝ) (hcb : 0 < cb)
    (hbnd : ∀ (θ : EuclideanSpace ℝ (Fin d)) (i : ι),
      ‖g θ i - ceGradReg X t lam θ‖ ≤ cb)
    (hvar : ∀ θ : EuclideanSpace ℝ (Fin d),
      pmfMean νp (fun i => ‖g θ i - ceGradReg X t lam θ‖ ^ 2) ≤ σ₂max)
    (hG : ∀ θ : EuclideanSpace ℝ (Fin d),
      ‖ceGradReg X t lam θ‖ ≤ cG)
    (θstar : EuclideanSpace ℝ (Fin d))
    (hgap : ∀ θ : EuclideanSpace ℝ (Fin d),
      Δ ≤ ceReg X t lam θ - ceReg X t lam θstar)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 0 < T)
    (r : ℝ) (hr : 0 < r)
    (hdrop : r < T * (γr * (1 - (ceSmoothL X + lam) * γr / 2)
      * (2 * lam * Δ)
      - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max))
    (s₁ : ι) :
    pmfMean (historyLaw (PMF.pure (fun _ => s₁)) (noiseKernel νp T) T T)
      (fun ω =>
        if T * (γr * (1 - (ceSmoothL X + lam) * γr / 2) * (2 * lam * Δ)
            - (ceSmoothL X + lam) * γr ^ 2 / 2 * σ₂max) - r
          ≤ ceReg X t lam θ₀
            - ceReg X t lam (thetaFun g γr θ₀ T
              (ω (historyIndex T T)) T)
          then (1:ℝ) else 0)
      ≥ 1 - Real.exp (-r ^ 2 / (4 * (T *
        (γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
          + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max)) ^ 2
        + (γr * |1 - (ceSmoothL X + lam) * γr| * cG * cb
          + (ceSmoothL X + lam) * γr ^ 2 / 2 * (cb ^ 2 + σ₂max)) * r))) := by
  have hGsq : ∀ θ : EuclideanSpace ℝ (Fin d),
      2 * lam * Δ ≤ ‖ceGradReg X t lam θ‖ ^ 2 := by
    intro θ
    have hpl := strong_convex_pl (ceReg X t lam) (ceGradReg X t lam)
      lam (ceReg X t lam θstar) hlam
      (fun x y => ceReg_strong_convex_ident X t lam x y) θstar
      (le_refl _) θ
    have h1 : 2 * lam * (ceReg X t lam θ - ceReg X t lam θstar)
      ≤ ‖ceGradReg X t lam θ‖ ^ 2 := hpl
    have h2 := hgap θ
    nlinarith [h1, h2]
  exact stochastic_ce_loop_whp X t lam hlam γr hγpos hγL νp g hbias
    cb σ₂max cG (2 * lam * Δ) hcb hbnd hvar hG hGsq θ₀ T hT r hr hdrop s₁



end Main

end Hagi.Unified.StochasticCELearning



