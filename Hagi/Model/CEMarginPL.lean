/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Core.Concat
import Hagi.Model.CEGlobalConvergence

/-!
# Margin-based PL for the unregularized cross-entropy

 `Hagi.Model.CEGlobalConvergence` discharges the PL premise of the CE
only through ℓ2 regularization (`ce_global_convergence_reg`, strong
convexity constant `λ`, weight decay).  This module replaces that
λ-crutch with data geometry: on a realizable 2-class problem with
margin, the UNREGULARIZED CE satisfies PL on a ball with an explicit
constant built from the margin coefficient and the radius.

Concrete case (KISS, every crux machine-checked): 2-class vocabulary
(`Bool`), one sample, target `false`, gap slope `a > 0` (the logit gap
is `a * θ`).  The loss is `scalarCE a θ = log (1 + exp (-(a*θ)))`,
bridged to the SSOT functional by `scalarCE_eq_ceOneHot`:
`Hagi.ceOneHot false (fun b => if b then 0 else a * θ) = scalarCE a θ`.

## The margin-PL constant

`muBall a B = a ^ 2 * exp (-(a * B)) / 8` — for `0 < a`, `0 ≤ B` and
every `θ` in the ball `|θ| ≤ B`:

`2 * muBall a B * scalarCE a θ ≤ (deriv (scalarCE a) θ) ^ 2`

(`margin_pl_ball`).  Route: `u = exp (-(a*θ))` lives in
`[exp (-(a*B)), exp (a*B)]`, hence `m * (1+u)^2 ≤ 4 * u` with
`m = exp (-(a*B))` (elementary: `u ≤ M`, `1 ≤ M*u`, `m*M = 1`),
combined with `log (1+u) ≤ u`.  In margin parametrization — margin
`γ = a * θstar` realized at `‖θstar‖ ≤ B`, so `γ ≤ a*B` — the
substitution `a = γ/B` gives `μ = (γ/B)^2 * exp (-γ) / 8`: the same
exponential-in-margin family as the classical bound.  The margin also
anchors a warm start (`margin_anchor`: `scalarCE a θstar ≤ exp (-γ)`).

## μ(γ,B) versus λ (weight decay)

`ce_global_convergence_reg` needs regularization `λ > 0` for strong
convexity, biasing the minimizer.  The margin route needs none: μ grows
with the realized margin (data separability), and the rate factor
`1 - μ/L = 1 - exp (-(a*B)) / 4` is data-geometric.  When the margin γ
is large, `exp (-γ)` dominates any practical fixed λ — margin beats
weight decay exactly when the data is well separable.

## Honest limitations (pinned)

* PL holds ONLY on the ball `|θ| ≤ B`.  Globally it is FALSE
  (loss ~ exp (-(a*θ)) but gradient² ~ exp (-2*(a*θ)) as θ → +∞, and
  the ratio gradient²/loss → 0 at both ends; cf. Ji–Telgarsky,
  "Risk and parameter convergence of logistic regression",
  arXiv:1803.07300 — gradient descent drifts on separable data).
* Confinement of the gradient-descent iterates to the ball is a
  PREMISE of the corollaries (`h_conf`), not a theorem: real
  confinement arguments need step-size conditions, out of scope.
* The smoothness constant is the MVT-route `L = a^2 / 2` (descent
  lemma with quadratic term `(a^2/4)*(y-x)^2`); the sharp `a^2/4`
  (Freund–Grigas–Mazumder conditioning, arXiv:1810.08727) needs an
  integral/convexity argument — a documented 2× slack in the rate
  constant only.
* The PL constant is explicit but not tight: the tight constant is
  `inf_{|θ|≤B} (f')²/(2*f)`; we trade tightness for the elementary
  closed form `a²·exp (-(a*B))/8` (honesty over tightness).
* `fstar = 0` is the UNattained infimum: the corollary bounds the loss
  (geometric decay of `scalarCE`), and says nothing about parameter
  convergence — consistent with the drift phenomenon above.

Reference search found: Karimi–Nutini–Schmidt 2016
(PL linear convergence, doi:10.1007/978-3-319-46128-1_50 — the PL
machinery this repo already carries); Ji–Telgarsky 2018 (global PL
falsity on separable data); Freund–Grigas–Mazumder 2018 (logistic
conditioning |f''| ≤ a²/4).  No Mathlib margin-PL API in the pinned
commit; the derivation is self-contained.

no reference: the explicit constant μ = a²·e^{−aB}/8 is derived here
from classical inequalities (`log (1+u) ≤ u`, AM-GM on `u`); no
formalization source found.

## the multiclass extension (V classes, explicit μ(a,B,V))

The scalar 2-class head above generalizes to a V-class gap head: correct logit `a·θ`, every wrong logit `0`, loss
`gapHead a θ = log (1 + c·e^{−aθ})` with `c = card V − 1` (bridged by
`gapHead_eq_ceOneHot`; `c = 0` degenerates to the constant zero loss).
The multiclass margin-PL constant is
`muBallV a B = a²·c·e^{−aB}/(2·(1+c·e^{aB})²)` — on the ball
`|θ| ≤ B` the PL inequality holds with this explicit constant
(`margin_pl_multiclass`); the V-dependence is polynomial (through
`c`), the margin decay exponential — same family .  The
curvature route is V-independent (`|sigmaV'| ≤ 1/4`, AM-GM on
`w = c·e^{−x}`), so smoothness stays `L = a²/2` and the corollary
`ce_global_convergence_multiclass` gives the rate
`(1 − muBallV/(a²/2))^T` with confinement pinned as a premise.

Honest scope pins: PL is proven for the GAP-HEAD logit
structure only; PL in parameter space for general `X·θ` heads
(needs rank/injectivity of `Xᵀ`) and confinement of iterates remain
open premises.  Two general logit-space margin lemmas carry the
premise-form margin `∀ v ≠ t, γ ≤ z t − z v`:
`ce_margin_le` (softmax-margin-to-loss) and `softDef_margin_lb`
(softmax-margin-to-probability, `1/(1+c·e^{−γ}) =
e^{γ}/(e^{γ}+c)`).  Probe evidence: numeric sweep (2·10⁵ points,
max(2μf − f'²) = −8.5e−19 ≤ 0).
-/

set_option relaxedAutoImplicit false

open Real

namespace Hagi.Model.CEMarginPL

/-! ## The scalar 2-class cross-entropy and its gradient -/

/-- The unregularized 2-class CE on the gap head: the correct logit is
`a * θ`, the other is `0`, so the loss is `log (1 + exp (-(a*θ)))`.
Equals `Hagi.ceOneHot false` on the 2-class 1-feature logits
(`scalarCE_eq_ceOneHot`). -/
noncomputable def scalarCE (a : ℝ) : ℝ → ℝ :=
  fun θ => Real.log (1 + Real.exp ((-(a * θ))))

/-- `rho x = sigmoid (-x) = (exp x + 1)⁻¹`, the residual probability of
the wrong class. -/
noncomputable def rho (x : ℝ) : ℝ := (Real.exp x + 1)⁻¹

/-- The margin (logit gap) realized by `θstar` on the gap head. -/
def logitGap (a θstar : ℝ) : ℝ := a * θstar

theorem rho_eq_div (x : ℝ) :
    rho x = Real.exp (-(x)) / (1 + Real.exp (-(x))) := by
  have hxs : Real.exp x * Real.exp (-(x)) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold rho
  rw [inv_eq_one_div, div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [hxs]

theorem hasDerivAt_rho (x : ℝ) :
    HasDerivAt rho (-Real.exp x / (Real.exp x + 1) ^ 2) x :=
  ((hasDerivAt_exp x).add_const 1).inv (by positivity)

theorem hasDerivAt_scalarCE (a θ : ℝ) :
    HasDerivAt (scalarCE a) (-(a * rho (a * θ))) θ := by
  have h0 : HasDerivAt (fun θ => -(a * θ)) (-a) θ := by
    have h := ((hasDerivAt_id θ).mul_const a).neg
    convert h using 1
    funext y
    simp [mul_comm]
    ring
  have h1 : HasDerivAt (fun θ => Real.exp (-(a * θ)))
      (Real.exp (-(a * θ)) * (-a)) θ := h0.exp
  have h2 : HasDerivAt (fun θ => 1 + Real.exp (-(a * θ)))
      (Real.exp (-(a * θ)) * (-a)) θ := by
    simpa [add_comm] using h1.add_const 1
  have h3 : HasDerivAt (scalarCE a)
      ((Real.exp (-(a * θ)) * (-a)) / (1 + Real.exp (-(a * θ)))) θ :=
    h2.log (by positivity)
  have hxs : Real.exp (a * θ) * Real.exp (-(a * θ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hrw1 : Real.exp (-(a * θ)) / (1 + Real.exp (-(a * θ)))
      = (Real.exp (a * θ) + 1)⁻¹ := by
    rw [← one_div, div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hxs]
  have hrw : (Real.exp (-(a * θ)) * (-a)) / (1 + Real.exp (-(a * θ)))
      = -(a * rho (a * θ)) := by
    rw [mul_comm (Real.exp (-(a * θ))) (-a), mul_div_assoc, hrw1]
    exact (neg_mul_eq_neg_mul a ((Real.exp (a * θ) + 1)⁻¹)).symm
  rw [hrw] at h3
  exact h3

theorem deriv_scalarCE (a θ : ℝ) :
    deriv (scalarCE a) θ = -(a * rho (a * θ)) :=
  (hasDerivAt_scalarCE a θ).deriv

theorem scalarCE_nonneg (a θ : ℝ) : 0 ≤ scalarCE a θ := by
  have hle : (1:ℝ) ≤ 1 + Real.exp (-(a * θ)) := by
    have := Real.exp_nonneg (-(a * θ))
    linarith
  have h1 : Real.log 1 ≤ Real.log (1 + Real.exp (-(a * θ))) :=
    Real.log_le_log (by norm_num) hle
  rw [Real.log_one] at h1
  exact h1

theorem scalarCE_eq_ceOneHot (a θ : ℝ) :
    Hagi.ceOneHot (false : Bool) (fun b => if b then 0 else a * θ)
      = scalarCE a θ := by
  have hsum : ∑ b : Bool, Real.exp ((fun b => if b then 0 else a * θ) b)
      = Real.exp (a * θ) + 1 := by
    simp
    ring
  have hxs : Real.exp (a * θ) * Real.exp (-(a * θ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsplit : Real.exp (a * θ) + 1
      = Real.exp (a * θ) * (1 + Real.exp (-(a * θ))) := by
    calc Real.exp (a * θ) + 1
        = Real.exp (a * θ) * Real.exp (-(a * θ)) + Real.exp (a * θ) := by
          rw [hxs]; ring
      _ = Real.exp (a * θ) * (1 + Real.exp (-(a * θ))) := by ring
  have hlm : Real.log (Real.exp (a * θ) * (1 + Real.exp (-(a * θ))))
      = Real.log (Real.exp (a * θ)) + Real.log (1 + Real.exp (-(a * θ))) :=
    Real.log_mul
      (ne_of_gt (show (0:ℝ) < Real.exp (a * θ) by positivity))
      (ne_of_gt (show (0:ℝ) < 1 + Real.exp (-(a * θ)) by positivity))
  show Real.log (∑ b : Bool, Real.exp ((fun b => if b then 0 else a * θ) b))
      - (fun b => if b then 0 else a * θ) false
      = Real.log (1 + Real.exp (-(a * θ)))
  simp only [ite_eq_right (Bool.false_ne_true)]
  rw [hsum, hsplit, hlm, Real.log_exp]
  ring

/-! ## Curvature: the sigmoid bound and the descent lemma -/

theorem abs_deriv_rho_le (x : ℝ) : |deriv rho x| ≤ 1 / 4 := by
  have hd : deriv rho x = -Real.exp x / (Real.exp x + 1) ^ 2 :=
    (hasDerivAt_rho x).deriv
  have hu : (0:ℝ) < Real.exp x := Real.exp_pos x
  have hsq : (Real.exp x + 1) ^ 2 - 4 * Real.exp x
      = (Real.exp x - 1) ^ 2 := by ring
  rw [hd, abs_div, abs_neg, abs_of_nonneg (Real.exp_nonneg x),
    abs_of_nonneg (sq_nonneg _),
    div_le_iff₀ (show (0:ℝ) < (Real.exp x + 1) ^ 2 by positivity)]
  have h4 : 4 * Real.exp x ≤ (Real.exp x + 1) ^ 2 := by nlinarith [hu, hsq]
  have hq : (0:ℝ) < 1 / 4 := by norm_num
  nlinarith [h4, hq]

theorem mvt_abs_le (g : ℝ → ℝ) (g' : ℝ → ℝ) (cst : ℝ) (hcst : 0 ≤ cst)
    (hcont : Continuous g)
    (hd : ∀ x, HasDerivAt g (g' x) x)
    (hb : ∀ x, |g' x| ≤ cst) (s t : ℝ) : |g s - g t| ≤ cst * |s - t| := by
  rcases lt_or_ge s t with h | h
  · obtain ⟨c, _, hcslope⟩ := exists_hasDerivAt_eq_slope g g' h
      hcont.continuousOn (fun x _ => hd x)
    have h1 : g t - g s = g' c * (t - s) := by
      rw [hcslope]; field_simp
    calc |g s - g t| = |g t - g s| := abs_sub_comm _ _
      _ = |g' c * (t - s)| := by rw [h1]
      _ = |g' c| * |t - s| := (abs_mul _ _)
      _ ≤ cst * |t - s| := mul_le_mul_of_nonneg_right (hb c) (abs_nonneg _)
      _ = cst * |s - t| := by rw [abs_sub_comm]
  · rcases eq_or_lt_of_le h with h | h
    · rw [h, sub_self, abs_zero]
      exact mul_nonneg hcst (abs_nonneg _)
    · obtain ⟨c, _, hcslope⟩ := exists_hasDerivAt_eq_slope g g' h
        hcont.continuousOn (fun x _ => hd x)
      have h1 : g s - g t = g' c * (s - t) := by
        rw [hcslope]; field_simp
      rw [h1, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb c) (abs_nonneg _)

theorem rho_lipschitz (s t : ℝ) : |rho s - rho t| ≤ |s - t| / 4 := by
  have hcont : Continuous rho := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ((hasDerivAt_rho p).differentiableAt.continuousAt)
  have h := mvt_abs_le rho (fun x => deriv rho x) (1/4)
    (by norm_num) hcont
    (fun x => ((hasDerivAt_rho x).differentiableAt).hasDerivAt)
    abs_deriv_rho_le s t
  calc |rho s - rho t| ≤ (1/4) * |s - t| := h
    _ = |s - t| / 4 := by ring

/-- The gradient of `scalarCE` is `(a^2/4)`-Lipschitz: the logistic
conditioning bound (Freund–Grigas–Mazumder 2018). -/
theorem scalarCE_grad_lip (a : ℝ) (p q : ℝ) :
    |deriv (scalarCE a) p - deriv (scalarCE a) q| ≤ (a ^ 2 / 4) * |p - q| := by
  rw [deriv_scalarCE, deriv_scalarCE]
  have hr := rho_lipschitz (a * p) (a * q)
  have hle : a ≤ |a| := le_abs_self a
  have hle2 : -a ≤ |a| := neg_le_abs a
  have h2 : |a| * |a| = a ^ 2 := by
    calc |a| * |a| = |a * a| := (abs_mul a a).symm
      _ = |a ^ 2| := by rw [sq]
      _ = a ^ 2 := abs_sq a
  have ham : |a * p - a * q| = |a| * |p - q| := by
    rw [← abs_mul, mul_sub]
  calc |-(a * rho (a * p)) - -(a * rho (a * q))|
      = |a| * |rho (a * p) - rho (a * q)| := by
        rw [show -(a * rho (a * p)) - -(a * rho (a * q))
            = -a * (rho (a * p) - rho (a * q)) by ring, abs_mul, abs_neg]
    _ ≤ |a| * (|a * p - a * q| / 4) :=
        mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    _ = |a| * (|a| * |p - q| / 4) := by rw [ham]
    _ = (|a| * |a|) * |p - q| / 4 := by ring
    _ = a ^ 2 / 4 * |p - q| := by rw [h2]; ring

/-- One-sided quadratic upper bound from a mean-value point. -/
theorem descent_tail (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (x y c : ℝ)
    (h1 : f y - f x = deriv f c * (y - x))
    (hlip : |deriv f c - deriv f x| ≤ L * |c - x|)
    (hcx : |c - x| ≤ |y - x|) :
    f y ≤ f x + deriv f x * (y - x) + L * (y - x) ^ 2 := by
  have hsplit : deriv f c * (y - x)
      = deriv f x * (y - x) + (deriv f c - deriv f x) * (y - x) := by ring
  have habs : (deriv f c - deriv f x) * (y - x)
      ≤ |deriv f c - deriv f x| * |y - x| := by
    have hh := le_abs_self ((deriv f c - deriv f x) * (y - x))
    rwa [abs_mul] at hh
  have h2 : |deriv f c - deriv f x| * |y - x| ≤ L * |c - x| * |y - x| :=
    mul_le_mul_of_nonneg_right hlip (abs_nonneg _)
  have hsq : |y - x| * |y - x| = (y - x) ^ 2 := by
    calc |y - x| * |y - x| = |(y - x) * (y - x)| := (abs_mul _ _).symm
      _ = |(y - x) ^ 2| := by rw [sq]
      _ = (y - x) ^ 2 := abs_of_nonneg (sq_nonneg (y - x))
  have h3 : L * |c - x| * |y - x| ≤ L * (y - x) ^ 2 := by
    calc L * |c - x| * |y - x| = L * (|c - x| * |y - x|) := by ring
      _ ≤ L * (|y - x| * |y - x|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcx (abs_nonneg _)) hL
      _ = L * (y - x) ^ 2 := by rw [hsq]
  have hfinal : f y
      = f x + deriv f x * (y - x) + (deriv f c - deriv f x) * (y - x) := by
    have hdecomp : f y = f x + (f y - f x) := by ring
    rw [hdecomp, h1, hsplit]
    ring
  rw [hfinal]
  linarith [habs, h2, h3]

/-- Descent lemma for the unregularized scalar CE, MVT route: the
quadratic term is `(a^2/4)*(y-x)^2`, i.e. smoothness constant
`L = a^2/2`.  The sharp `a^2/4` needs an integral argument — a
documented 2× slack. -/
theorem scalarCE_smooth (a x y : ℝ) :
    scalarCE a y ≤ scalarCE a x + deriv (scalarCE a) x * (y - x)
      + (a ^ 2 / 4) * (y - x) ^ 2 := by
  have hcont : Continuous (scalarCE a) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ((hasDerivAt_scalarCE a p).differentiableAt.continuousAt)
  have hdiff : ∀ p, HasDerivAt (scalarCE a) (deriv (scalarCE a) p) p :=
    fun p => ((hasDerivAt_scalarCE a p).differentiableAt).hasDerivAt
  have hlip := scalarCE_grad_lip a
  have hL : (0:ℝ) ≤ a ^ 2 / 4 := by positivity
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hcmem, hcslope⟩ := exists_hasDerivAt_eq_slope (scalarCE a)
      (deriv (scalarCE a)) h hcont.continuousOn (fun p _ => hdiff p)
    have h1 : scalarCE a y - scalarCE a x = deriv (scalarCE a) c * (y - x) := by
      rw [hcslope]; field_simp
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_nonneg (sub_nonneg.2 hcmem.1.le),
        abs_of_nonneg (sub_nonneg.2 h.le)]
      linarith [hcmem.2]
    exact descent_tail (scalarCE a) (a ^ 2 / 4) hL x y c h1 (hlip c x) hcx
  · rw [h, sub_self]
    have hthis : (0:ℝ) ≤ (a ^ 2 / 4) * (y - x) ^ 2 := by positivity
    linarith [hthis]
  · obtain ⟨c, hcmem, hcslope⟩ := exists_hasDerivAt_eq_slope (scalarCE a)
      (deriv (scalarCE a)) h hcont.continuousOn (fun p _ => hdiff p)
    have h1 : scalarCE a y - scalarCE a x = deriv (scalarCE a) c * (y - x) := by
      rw [hcslope]; field_simp; ring
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_nonpos (sub_nonpos.2 hcmem.2.le),
        abs_of_nonpos (sub_nonpos.2 h.le)]
      linarith [hcmem.1]
    exact descent_tail (scalarCE a) (a ^ 2 / 4) hL x y c h1 (hlip c x) hcx

/-! ## The margin-PL theorem on the ball -/

/-- The explicit margin-PL constant `μ(a,B) = a²·exp (-(a*B))/8`; in
margin parametrization `γ = a*θstar` with `|θstar| ≤ B`, `a = γ/B`
gives `μ = (γ/B)²·exp (-γ)/8`. -/
noncomputable def muBall (a B : ℝ) : ℝ := a ^ 2 * Real.exp (-(a * B)) / 8

/-- THE MARGIN-PL THEOREM: on the ball `|θ| ≤ B`, the unregularized
2-class CE satisfies the PL inequality in gradient-norm form with the
explicit constant `muBall a B`.  The margin enters through the ball:
`γ ≤ a*B` whenever the margin `γ = a*θstar` is realized at
`|θstar| ≤ B`, and `muBall` is decreasing in `a*B ≥ γ`. -/
theorem margin_pl_ball (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (θ : ℝ)
    (hθ : |θ| ≤ B) :
    2 * muBall a B * (scalarCE a θ - 0) ≤ (deriv (scalarCE a) θ) ^ 2 := by
  have hu : (0:ℝ) < Real.exp (-(a * θ)) := Real.exp_pos _
  set u : ℝ := Real.exp (-(a * θ)) with hudef
  set m : ℝ := Real.exp (-(a * B)) with hmdef
  have hM : (0:ℝ) < Real.exp (a * B) := Real.exp_pos _
  have hmM : m * Real.exp (a * B) = 1 := by
    rw [hmdef, ← Real.exp_add]
    simp
  have hθge : -B ≤ θ := (abs_le.1 hθ).1
  have hθle : θ ≤ B := (abs_le.1 hθ).2
  have hmle : m ≤ u := by
    have h1 : -(a * B) ≤ -(a * θ) := by
      rw [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left hθle ha.le
    exact (Real.exp_le_exp).2 h1
  have hule : u ≤ Real.exp (a * B) := by
    have h1 : -(a * θ) ≤ a * B := by nlinarith [hθge, ha]
    exact (Real.exp_le_exp).2 h1
  have hkey : m * (1 + u) ^ 2 ≤ 4 * u := by
    have hle1 : (1:ℝ) ≤ Real.exp (a * B) * u := by
      calc (1:ℝ) = m * Real.exp (a * B) := hmM.symm
        _ ≤ u * Real.exp (a * B) := by nlinarith [hmle, hmM, hM]
        _ = Real.exp (a * B) * u := by ring
    have hle2 : u ^ 2 ≤ Real.exp (a * B) * u := by nlinarith [hule, hu]
    have hm1 : m ≤ 1 := by
      have hle : m ≤ Real.exp (0 : ℝ) :=
        (Real.exp_le_exp).2 (by nlinarith [ha, hB])
      rw [Real.exp_zero] at hle
      exact hle
    nlinarith [hle1, hle2, hm1, hu]
  have hlog : Real.log (1 + u) ≤ u := by
    have hu1 : (1:ℝ) + u ≤ Real.exp u := by
      rw [add_comm]
      exact Real.add_one_le_exp u
    have h1 : Real.log (1 + u) ≤ Real.log (Real.exp u) :=
      Real.log_le_log (by linarith) hu1
    rw [Real.log_exp] at h1
    exact h1
  have hsc : scalarCE a θ = Real.log (1 + u) := rfl
  have hdu : deriv (scalarCE a) θ = -(a * u / (1 + u)) := by
    rw [deriv_scalarCE, rho_eq_div, mul_div_assoc]
  rw [hsc, hdu, muBall, ← hmdef]
  have hm2 : 2 * (a ^ 2 * m / 8) = a ^ 2 * m / 4 := by ring
  rw [hm2, sub_zero]
  have hs : (-(a * u / (1 + u))) ^ 2 = a ^ 2 * u ^ 2 / (1 + u) ^ 2 := by
    rw [neg_sq, div_pow, mul_pow]
  rw [hs]
  have s1 : (a ^ 2 * m / 4) * Real.log (1 + u) ≤ (a ^ 2 * m / 4) * u :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have s2 : (a ^ 2 * m / 4) * u ≤ a ^ 2 * u ^ 2 / (1 + u) ^ 2 := by
    rw [le_div_iff₀ (show (0:ℝ) < (1 + u) ^ 2 by positivity)]
    have hA : a ^ 2 * u * (m * (1 + u) ^ 2) ≤ a ^ 2 * u * (4 * u) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have hE : (a ^ 2 * m / 4) * u * (1 + u) ^ 2
        = a ^ 2 * u * (m * (1 + u) ^ 2) / 4 := by field_simp
    have hF : a ^ 2 * u * (4 * u) / 4 = a ^ 2 * u ^ 2 := by field_simp
    rw [hE]
    calc a ^ 2 * u * (m * (1 + u) ^ 2) / 4
        ≤ a ^ 2 * u * (4 * u) / 4 := by nlinarith [hA]
      _ = a ^ 2 * u ^ 2 := hF
  linarith [s1, s2]

/-- A realizable margin `γ ≤ a * θstar` anchors a warm start: the loss
at `θstar` is at most `exp (-γ)` (the infimum 0 itself is unattained). -/
theorem margin_anchor (a θstar γ : ℝ) (_ha : 0 < a) (hgap : γ ≤ a * θstar) :
    scalarCE a θstar ≤ Real.exp (-γ) := by
  have hu : (0:ℝ) < Real.exp (-(a * θstar)) := Real.exp_pos _
  have hlog : scalarCE a θstar ≤ Real.exp (-(a * θstar)) := by
    have hu1 : (1:ℝ) + Real.exp (-(a * θstar))
        ≤ Real.exp (Real.exp (-(a * θstar))) := by
      rw [add_comm]
      exact Real.add_one_le_exp _
    have h1 : Real.log (1 + Real.exp (-(a * θstar)))
        ≤ Real.log (Real.exp (Real.exp (-(a * θstar)))) :=
      Real.log_le_log (by positivity) hu1
    rw [Real.log_exp] at h1
    exact h1
  have hmono : Real.exp (-(a * θstar)) ≤ Real.exp (-γ) :=
    (Real.exp_le_exp).2 (by nlinarith [hgap])
  linarith [hlog, hmono]

/-! ## The convergence corollaries -/

open scoped InnerProductSpace in
/-- Pointwise-PL one-step contraction: `pl_descent_step` with the PL
premise required only AT the step point (the ball-restricted PL of
`margin_pl_ball` is exactly of this shape). -/
theorem pl_descent_step_at {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L μ fstar : ℝ) (θ : E) (hL : 0 < L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_pl : 2 * μ * (f θ - fstar) ≤ ‖grad θ‖ ^ 2)
    (_h_floor : fstar ≤ f θ) :
    f (CEGlobalConvergence.plStep grad L θ) - fstar
      ≤ (1 - μ / L) * (f θ - fstar) := by
  rw [CEGlobalConvergence.plStep]
  have hstep := h_smooth θ (θ - (1 / L) • grad θ)
  have hin : ⟪grad θ, θ - (1 / L) • grad θ - θ⟫_ℝ
      = -(1 / L) * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hin] at hstep
  have hcoef : L / 2 * ((1 / L) ^ 2 * ‖grad θ‖ ^ 2)
      = ‖grad θ‖ ^ 2 / (2 * L) := by field_simp
  have hnorm : ‖θ - (1 / L) • grad θ - θ‖ ^ 2
      = (1 / L) ^ 2 * ‖grad θ‖ ^ 2 := by
    rw [show θ - (1 / L) • grad θ - θ = -(1 / L) • grad θ by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    ring
  rw [hnorm, hcoef] at hstep
  have hXY : f θ + -(1 / L) * ‖grad θ‖ ^ 2 + ‖grad θ‖ ^ 2 / (2 * L)
      = f θ - ‖grad θ‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hXY] at hstep
  have hd : (1 - μ / L) * (f θ - fstar)
      = (f θ - fstar) - μ * (f θ - fstar) / L := by ring
  rw [hd]
  have hmu : μ * (f θ - fstar) / L ≤ ‖grad θ‖ ^ 2 / (2 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h_pl, hL]
  linarith

open scoped InnerProductSpace in
/-- Conditional convergence form for general heads: PL restricted to a
ball (the margin-transfer binder — discharged per head, e.g. by
`margin_pl_ball` for the scalar gap head), global smoothness, the
floor, and CONFINEMENT of the gradient-descent iterates to the ball
(honest pin: confinement is not proven, it is a premise) yield the
geometric rate `(1 - μ/L)^T`. -/
theorem margin_pl_convergence {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L μ fstar B : ℝ) (hL : 0 < L) (hμL : μ ≤ L)
    (h_smooth : ∀ x y : E, f y ≤ f x + ⟪grad x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (h_floor : ∀ x : E, fstar ≤ f x)
    (h_pl_ball : ∀ x : E, ‖x‖ ≤ B → 2 * μ * (f x - fstar) ≤ ‖grad x‖ ^ 2)
    (θ₀ : E) (T : ℕ)
    (h_conf : ∀ t ≤ T, ‖(CEGlobalConvergence.plStep grad L)^[t] θ₀‖ ≤ B) :
    f ((CEGlobalConvergence.plStep grad L)^[T] θ₀) - fstar
      ≤ (1 - μ / L) ^ T * (f θ₀ - fstar) := by
  induction T with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ T ih =>
    have ih := ih (fun t ht => h_conf t (Nat.le_trans ht (Nat.le_succ T)))
    have hstep := pl_descent_step_at f grad L μ fstar
      ((CEGlobalConvergence.plStep grad L)^[T] θ₀) hL h_smooth
      (h_pl_ball _ (h_conf T (Nat.le_succ T))) (h_floor _)
    have hnn : 0 ≤ 1 - μ / L := by
      rw [sub_nonneg, div_le_one hL]
      linarith
    rw [Function.iterate_succ_apply', pow_succ]
    calc f (CEGlobalConvergence.plStep grad L
        ((CEGlobalConvergence.plStep grad L)^[T] θ₀)) - fstar
        ≤ (1 - μ / L) * (f ((CEGlobalConvergence.plStep grad L)^[T] θ₀) - fstar) := hstep
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ T * (f θ₀ - fstar)) :=
          mul_le_mul_of_nonneg_left ih hnn
      _ = (1 - μ / L) ^ T * (1 - μ / L) * (f θ₀ - fstar) := by ring

/-- The gradient map of the scalar CE as `plStep` expects it. -/
noncomputable def scalarCEGrad (a : ℝ) : ℝ → ℝ := fun θ => deriv (scalarCE a) θ

open scoped InnerProductSpace in
/-- Smoothness of the scalar CE in inner-product form (on `ℝ` the inner
product is multiplication, the norm the absolute value). -/
theorem scalarCE_smooth_ip (a x y : ℝ) :
    scalarCE a y ≤ scalarCE a x + ⟪scalarCEGrad a x, y - x⟫_ℝ
      + (a ^ 2 / 2) / 2 * ‖y - x‖ ^ 2 := by
  have h := scalarCE_smooth a x y
  have hinner : ⟪scalarCEGrad a x, y - x⟫_ℝ = deriv (scalarCE a) x * (y - x) := by
    simp [scalarCEGrad]
    ring
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hinner, hnorm]
  have hcoef : (a ^ 2 / 2) / 2 = a ^ 2 / 4 := by ring
  rw [hcoef]
  exact h

open scoped InnerProductSpace in
/-- THE MARGIN COROLLARY (unregularized): gradient descent on the
unregularized 2-class CE, with PL discharged by the margin geometry
(`margin_pl_ball`) and the MVT smoothness `L = a^2/2`, drives the loss
to zero geometrically at rate `1 - muBall a B / (a^2/2)
= 1 - exp (-(a*B)) / 4`, PROVIDED the iterates stay confined to the
ball (premise `h_conf` — the honest pin).  The floor `fstar = 0` is the
unattained infimum; the rate bounds the loss, not the parameter. -/
theorem ce_global_convergence_margin (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (θ₀ : ℝ) (T : ℕ)
    (h_conf : ∀ t ≤ T,
      |(CEGlobalConvergence.plStep (scalarCEGrad a) (a ^ 2 / 2))^[t] θ₀| ≤ B) :
    scalarCE a ((CEGlobalConvergence.plStep (scalarCEGrad a) (a ^ 2 / 2))^[T] θ₀) - 0
      ≤ (1 - muBall a B / (a ^ 2 / 2)) ^ T * (scalarCE a θ₀ - 0) := by
  have hL : (0:ℝ) < a ^ 2 / 2 := by positivity
  have hμL : muBall a B ≤ a ^ 2 / 2 := by
    have h1 : muBall a B = a ^ 2 * Real.exp (-(a * B)) / 8 := rfl
    have h2 : (0:ℝ) < a ^ 2 := by positivity
    have h3 : Real.exp (-(a * B)) ≤ 1 := by
      have := (Real.exp_le_exp).2 (show -(a * B) ≤ (0:ℝ) by nlinarith [hB, ha])
      simpa using this
    have : a ^ 2 * Real.exp (-(a * B)) / 8 ≤ a ^ 2 / 2 := by
      nlinarith [h2, h3]
    rw [h1]
    linarith
  exact margin_pl_convergence (scalarCE a) (scalarCEGrad a) (a ^ 2 / 2)
    (muBall a B) 0 B hL hμL (scalarCE_smooth_ip a)
    (fun x => scalarCE_nonneg a x)
    (fun x hx => by
      have hb := margin_pl_ball a B ha hB x hx
      show 2 * muBall a B * (scalarCE a x - 0) ≤ |deriv (scalarCE a) x| ^ 2
      rw [sq_abs]
      exact hb) θ₀ T h_conf


/-! ## The multiclass gap head: margin PL with explicit μ(a,B,V) -/

/-- `(Fintype.card V : ℝ) ≥ 1` for a nonempty vocabulary. -/
theorem cardV_pos {V : Type} [Fintype V] [Nonempty V] :
    (1:ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := Fintype.card_pos_iff.2 (inferInstance : Nonempty V)
  exact_mod_cast h

/-- The wrong-class count as a real coefficient `c = card V − 1 ≥ 0`
(the number of incorrect classes; `c = 0` exactly for a singleton
vocabulary). -/
theorem gapHeadCard_nonneg {V : Type} [Fintype V] [Nonempty V] :
    (0:ℝ) ≤ (Fintype.card V : ℝ) - 1 :=
  by linarith [cardV_pos (V := V)]

/-- The V-class gap head: the correct logit is `a * θ`, every wrong
logit is `0`, so `ceOneHot t` on these logits is
`log (1 + c·exp (-(a*θ)))` with `c = card V − 1`
(`gapHead_eq_ceOneHot`).  Generalizes the Bool gap head
(`scalarCE`) from two classes to `V` classes; the V-dependence of
every downstream constant runs through `c`. -/
noncomputable def gapHead {V : Type} [Fintype V] (a θ : ℝ) : ℝ :=
  Real.log (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θ)))

/-- The wrong-class probability mass: `sigmaV x = c·e^{−x}/(1+c·e^{−x})`,
the total softmax mass on the incorrect classes of the gap head.  The
V-class analog of `rho`. -/
noncomputable def sigmaV {V : Type} [Fintype V] (x : ℝ) : ℝ :=
  ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))
    / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)))

/-- THE BRIDGE: `ceOneHot` on the V-class gap logits (correct logit
`a*θ`, wrong logits `0`) is exactly `gapHead`. -/
theorem gapHead_eq_ceOneHot {V : Type} [Fintype V] [Nonempty V]
    [DecidableEq V] (t : V) (a θ : ℝ) :
    Hagi.ceOneHot t (fun v => if v = t then a * θ else 0)
      = gapHead (V := V) a θ := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hsum : ∑ v, Real.exp ((fun v => if v = t then a * θ else 0) v)
      = Real.exp (a * θ) + ((Fintype.card V : ℝ) - 1) := by
    have hsplit : ∀ v : V, Real.exp ((fun v => if v = t then a * θ else 0) v)
        = 1 + (if v = t then Real.exp (a * θ) - 1 else 0) := by
      intro v
      by_cases h : v = t <;> simp [h]
    rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_add_distrib,
      Finset.sum_const, Finset.sum_ite_eq' Finset.univ t
        (fun _ => Real.exp (a * θ) - 1)]
    simp
    ring
  have hxs : Real.exp (a * θ) * Real.exp (-(a * θ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsplit : Real.exp (a * θ) + ((Fintype.card V : ℝ) - 1)
      = Real.exp (a * θ) * (1 + ((Fintype.card V : ℝ) - 1)
          * Real.exp (-(a * θ))) := by
    nlinarith [hxs]
  show Real.log (∑ v, Real.exp ((fun v => if v = t then a * θ else 0) v))
    - (fun v => if v = t then a * θ else 0) t = _
  simp only []
  rw [hsum, hsplit,
    Real.log_mul (by positivity)
      (by have hu := Real.exp_pos (-(a * θ)); nlinarith [hcnn, hu]),
    Real.log_exp]
  simp only [ite_true]
  unfold gapHead
  ring

/-- The derivative of the wrong-class mass: `sigmaV' x
= −c·e^{−x}/(1+c·e^{−x})²`. -/
theorem hasDerivAt_sigmaV {V : Type} [Fintype V] [Nonempty V] (x : ℝ) :
    HasDerivAt (sigmaV (V := V))
      (-(((Fintype.card V : ℝ) - 1) * Real.exp (-(x))
        / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))) ^ 2)) x := by
  have h1 : HasDerivAt (fun y => Real.exp (-(y)))
      (Real.exp (-(x)) * (-1)) x := ((hasDerivAt_id x).neg).exp
  have h2 : HasDerivAt (fun y => ((Fintype.card V : ℝ) - 1)
      * Real.exp (-(y)))
      (((Fintype.card V : ℝ) - 1) * (Real.exp (-(x)) * (-1))) x :=
    h1.const_mul _
  have h3 : HasDerivAt (fun y => 1 + ((Fintype.card V : ℝ) - 1)
      * Real.exp (-(y)))
      (((Fintype.card V : ℝ) - 1) * (Real.exp (-(x)) * (-1))) x := by
    have h := h2.add_const 1
    convert h using 1
    · funext y
      ring_nf
  have hpos : (0:ℝ) < 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)) := by
    have hcnn := gapHeadCard_nonneg (V := V)
    have hu := Real.exp_pos (-(x))
    nlinarith [hcnn, hu]
  have hne : 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)) ≠ 0 := by
    have hcnn := gapHeadCard_nonneg (V := V)
    have hu := Real.exp_pos (-(x))
    nlinarith [hcnn, hu]
  have h5 : HasDerivAt (sigmaV (V := V))
      (-(((Fintype.card V : ℝ) - 1) * Real.exp (-(x))
        / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))) ^ 2)) x := by
    unfold sigmaV
    have hdiv := h2.div h3 hne
    convert hdiv using 1
    field_simp
    ring
  exact h5

/-- The derivative of the gap head: `deriv (gapHead a) θ
= -(a * sigmaV (a * θ))`, the V-class analog of `deriv_scalarCE`
(the wrong-class mass replaces the single wrong-class probability). -/
theorem hasDerivAt_gapHead {V : Type} [Fintype V] [Nonempty V] (a θ : ℝ) :
    HasDerivAt (gapHead (V := V) a) (-(a * sigmaV (V := V) (a * θ))) θ := by
  have h1 : HasDerivAt (fun y => -(a * y)) (-a) θ := by
    have h := ((hasDerivAt_id θ).mul_const a).neg
    convert h using 1
    funext y
    simp [mul_comm]
    ring
  have h2 : HasDerivAt (fun y => Real.exp (-(a * y)))
      (Real.exp (-(a * θ)) * (-a)) θ := h1.exp
  have h3 : HasDerivAt (fun y => 1 + ((Fintype.card V : ℝ) - 1)
      * Real.exp (-(a * y)))
      (((Fintype.card V : ℝ) - 1) * (Real.exp (-(a * θ)) * (-a))) θ := by
    have h : HasDerivAt (fun y => ((Fintype.card V : ℝ) - 1)
        * Real.exp (-(a * y)) + 1)
        (((Fintype.card V : ℝ) - 1) * (Real.exp (-(a * θ)) * (-a))) θ :=
      (h2.const_mul _).add_const 1
    convert h using 1
    · funext y
      ring_nf
  have hcnn := gapHeadCard_nonneg (V := V)
  have hu := Real.exp_pos (-(a * θ))
  have hne : 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θ)) ≠ 0 := by
    nlinarith [hcnn, hu]
  have h4 : HasDerivAt (gapHead (V := V) a)
      ((((Fintype.card V : ℝ) - 1) * (Real.exp (-(a * θ)) * (-a)))
        / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θ)))) θ :=
    h3.log hne
  convert h4 using 1
  · unfold sigmaV
    field_simp

theorem deriv_gapHead {V : Type} [Fintype V] [Nonempty V] (a θ : ℝ) :
    deriv (gapHead (V := V) a) θ = -(a * sigmaV (V := V) (a * θ)) :=
  (hasDerivAt_gapHead a θ).deriv

/-- The gap head is nonnegative (a log of at least one). -/
theorem gapHead_nonneg {V : Type} [Fintype V] [Nonempty V] (a θ : ℝ) :
    0 ≤ gapHead (V := V) a θ := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hle : (1:ℝ) ≤ 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θ)) := by
    have hu := Real.exp_pos (-(a * θ))
    nlinarith [hcnn, hu]
  have h1 : Real.log 1 ≤ Real.log
      (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θ))) :=
    Real.log_le_log (by norm_num) hle
  rw [Real.log_one] at h1
  exact h1

/-- THE MULTICLASS MARGIN-PL CONSTANT:
`muBallV a B = a²·c·e^{−aB}/(2·(1+c·e^{aB})²)` with `c = card V − 1`.
In margin parametrization `γ = a*θstar` realized at `|θstar| ≤ B`
(so `γ ≤ a*B`), substituting `a = γ/B` gives a constant decaying
exponentially in `γ` with the V-polynomial factor `c`: margin beats
the V-count exactly when the data is well separable. -/
noncomputable def muBallV {V : Type} [Fintype V] (a B : ℝ) : ℝ :=
  a ^ 2 * (((Fintype.card V : ℝ) - 1) * Real.exp (-(a * B)))
    / (2 * (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (a * B)) ^ 2)

/-- THE MULTICLASS MARGIN-PL THEOREM: on the ball `|θ| ≤ B`, the
unregularized V-class gap-head CE satisfies the PL inequality in
gradient-norm form with the explicit constant `muBallV a B`.  Route:
`u = e^{−aθ} ∈ [m, M]`, `m = e^{−aB}`, `M = e^{aB}`, and the key
`m·(1+c·u)² ≤ u·(1+c·M)²` (from `m ≤ u ≤ M` and `c ≥ 0`), combined
with `log (1+w) ≤ w` for `w = c·u`. -/
theorem margin_pl_multiclass {V : Type} [Fintype V] [Nonempty V]
    (a B : ℝ) (ha : 0 < a) (_hB : 0 ≤ B) (θ : ℝ) (hθ : |θ| ≤ B) :
    2 * muBallV (V := V) a B * (gapHead (V := V) a θ - 0)
      ≤ (deriv (gapHead (V := V) a)) θ ^ 2 := by
  have hcnn := gapHeadCard_nonneg (V := V)
  set c : ℝ := ((Fintype.card V : ℝ) - 1) with hc
  set u : ℝ := Real.exp (-(a * θ)) with hu
  set m : ℝ := Real.exp (-(a * B)) with hm
  set M : ℝ := Real.exp (a * B) with hM
  have hθge : -B ≤ θ := (abs_le.1 hθ).1
  have hθle : θ ≤ B := (abs_le.1 hθ).2
  have hmle : m ≤ u := by
    have h1 : -(a * B) ≤ -(a * θ) := by
      rw [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left hθle ha.le
    exact (Real.exp_le_exp).2 h1
  have hule : u ≤ M := by
    have h1 : -(a * θ) ≤ a * B := by nlinarith [hθge, ha]
    exact (Real.exp_le_exp).2 h1
  have hlog : Real.log (1 + c * u) ≤ c * u := by
    have hu1 : (1:ℝ) + c * u ≤ Real.exp (c * u) := by
      rw [add_comm]
      exact Real.add_one_le_exp (c * u)
    have h1 : Real.log (1 + c * u) ≤ Real.log (Real.exp (c * u)) :=
      Real.log_le_log (by
        have hupos : (0:ℝ) < u := Real.exp_pos (-(a * θ))
        nlinarith [hcnn, hupos]) hu1
    rw [Real.log_exp] at h1
    exact h1
  have hdu : deriv (gapHead (V := V) a) θ
      = -(a * (c * u / (1 + c * u))) := by
    rw [deriv_gapHead, sigmaV, ← hu, ← hc]
  have hf : gapHead (V := V) a θ = Real.log (1 + c * u) := rfl
  have hposcu : (0:ℝ) < 1 + c * u := by
    have hupos : (0:ℝ) < u := Real.exp_pos (-(a * θ))
    nlinarith [hcnn, hupos]
  have hkey : m * (1 + c * u) ^ 2 ≤ u * (1 + c * M) ^ 2 := by
    have hcum : c * u ≤ c * M := mul_le_mul_of_nonneg_left hule hcnn
    have hposM' : (0:ℝ) < 1 + c * M := by
      have hMpos : (0:ℝ) < M := Real.exp_pos (a * B)
      nlinarith [hcnn, hMpos]
    have h1 : -(1 + c * M) ≤ 1 + c * u := by
      have hMpos : (0:ℝ) < M := Real.exp_pos (a * B)
      nlinarith [hposM', hposcu]
    have h2 : 1 + c * u ≤ 1 + c * M := by linarith [hcum]
    have hsq : (1 + c * u) ^ 2 ≤ (1 + c * M) ^ 2 :=
      sq_le_sq' h1 h2
    have hnn : (0:ℝ) ≤ (1 + c * u) ^ 2 := sq_nonneg _
    have hu_nn : (0:ℝ) ≤ u := le_of_lt (Real.exp_pos (-(a * θ)))
    calc m * (1 + c * u) ^ 2 ≤ u * (1 + c * u) ^ 2 :=
          mul_le_mul_of_nonneg_right hmle hnn
      _ ≤ u * (1 + c * M) ^ 2 := by nlinarith [hsq, hu_nn]
  have h2mu : 2 * muBallV (V := V) a B
      = a ^ 2 * (c * m) / (1 + c * M) ^ 2 := by
    simp only [muBallV, hm, hM, hc]
    field_simp
  have hcunn : (0:ℝ) ≤ c * u := by
    have hupos : (0:ℝ) < u := Real.exp_pos (-(a * θ))
    nlinarith [hcnn, hupos]
  rw [hf, h2mu, sub_zero, hdu]
  have hs : (-(a * (c * u / (1 + c * u)))) ^ 2
      = a ^ 2 * (c * u) ^ 2 / (1 + c * u) ^ 2 := by
    rw [neg_sq, mul_pow, div_pow]
    ring
  rw [hs]
  have hposM : (0:ℝ) < 1 + c * M := by
    have hMpos : (0:ℝ) < M := Real.exp_pos (a * B)
    nlinarith [hcnn, hMpos]
  have s1 : a ^ 2 * (c * m) / (1 + c * M) ^ 2 * Real.log (1 + c * u)
      ≤ a ^ 2 * (c * m) / (1 + c * M) ^ 2 * (c * u) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have s2 : a ^ 2 * (c * m) / (1 + c * M) ^ 2 * (c * u)
      ≤ a ^ 2 * (c * u) ^ 2 / (1 + c * u) ^ 2 := by
    have hupos : (0:ℝ) < u := Real.exp_pos (-(a * θ))
    rcases eq_or_lt_of_le hcunn with h0 | hpos
    · rw [← h0]
      simp
    · have hcpos : (0:ℝ) < c := by nlinarith [hpos, hupos]
      have hp : (0:ℝ) < a ^ 2 * c * u := by positivity
      have hmul : a ^ 2 * c * u * (m * (1 + c * u) ^ 2)
          ≤ a ^ 2 * c * u * (u * (1 + c * M) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey hp.le
      have hstep : c * (a ^ 2 * c * u * (m * (1 + c * u) ^ 2))
          ≤ c * (a ^ 2 * c * u * (u * (1 + c * M) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmul hcnn
      rw [div_mul_eq_mul_div, div_le_div_iff₀
        (show (0:ℝ) < (1 + c * M) ^ 2 by positivity)
        (show (0:ℝ) < (1 + c * u) ^ 2 by positivity)]
      have hL : a ^ 2 * (c * m) * (c * u) * (1 + c * u) ^ 2
          = c * (a ^ 2 * c * u * (m * (1 + c * u) ^ 2)) := by ring
      have hR : a ^ 2 * (c * u) ^ 2 * (1 + c * M) ^ 2
          = c * (a ^ 2 * c * u * (u * (1 + c * M) ^ 2)) := by ring
      rw [hL, hR]
      exact hstep
  linarith [s1, s2]


/-- The curvature bound `|sigmaV'| ≤ 1/4`: the V-class analog of
`abs_deriv_rho_le`.  With `w = c·e^{−x} ≥ 0`, the derivative is
`−w/(1+w)²` and `(1+w)² ≥ 4w` (AM-GM, i.e. `(1−w)² ≥ 0`); the
bound is V-INDEPENDENT — the worst case is the binary split of the
wrong mass. -/
theorem abs_deriv_sigmaV_le {V : Type} [Fintype V] [Nonempty V] (x : ℝ) :
    |deriv (sigmaV (V := V)) x| ≤ 1 / 4 := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hu : (0:ℝ) < Real.exp (-(x)) := Real.exp_pos _
  have hw : (0:ℝ) ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)) := by
    nlinarith [hcnn, hu]
  have hd : deriv (sigmaV (V := V)) x
      = -(((Fintype.card V : ℝ) - 1) * Real.exp (-(x))
        / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))) ^ 2) :=
    (hasDerivAt_sigmaV x).deriv
  have hpos : (0:ℝ) < 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)) := by
    nlinarith [hw]
  have h4 : 4 * ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))
      ≤ (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-(x))) ^ 2 := by
    nlinarith [hw, sq_nonneg
      (1 - ((Fintype.card V : ℝ) - 1) * Real.exp (-(x)))]
  rw [hd, abs_neg, abs_div, abs_of_nonneg hw,
    abs_of_nonneg (sq_nonneg _)]
  rw [div_le_iff₀ (show (0:ℝ) < (1 + ((Fintype.card V : ℝ) - 1)
      * Real.exp (-(x))) ^ 2 by positivity)]
  have hq : (0:ℝ) < 1 / 4 := by norm_num
  nlinarith [h4, hq, hpos]

theorem sigmaV_lipschitz {V : Type} [Fintype V] [Nonempty V] (s t : ℝ) :
    |sigmaV (V := V) s - sigmaV (V := V) t| ≤ |s - t| / 4 := by
  have hcont : Continuous (sigmaV (V := V)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ((hasDerivAt_sigmaV p).differentiableAt.continuousAt)
  have h := mvt_abs_le (sigmaV (V := V)) (fun x => deriv (sigmaV (V := V)) x)
    (1/4) (by norm_num) hcont
    (fun x => ((hasDerivAt_sigmaV x).differentiableAt).hasDerivAt)
    abs_deriv_sigmaV_le s t
  calc |sigmaV (V := V) s - sigmaV (V := V) t| ≤ (1/4) * |s - t| := h
    _ = |s - t| / 4 := by ring

/-- The gradient of the V-class gap head is `(a^2/4)`-Lipschitz — the
logistic conditioning bound, V-independent exactly as in the 2-class
case (`scalarCE_grad_lip`). -/
theorem gapHead_grad_lip {V : Type} [Fintype V] [Nonempty V] (a : ℝ)
    (p q : ℝ) :
    |deriv (gapHead (V := V) a) p - deriv (gapHead (V := V) a) q|
      ≤ (a ^ 2 / 4) * |p - q| := by
  rw [deriv_gapHead, deriv_gapHead]
  have hr := sigmaV_lipschitz (V := V) (a * p) (a * q)
  have hle : a ≤ |a| := le_abs_self a
  have h2 : |a| * |a| = a ^ 2 := by
    calc |a| * |a| = |a * a| := (abs_mul a a).symm
      _ = |a ^ 2| := by rw [sq]
      _ = a ^ 2 := abs_sq a
  have ham : |a * p - a * q| = |a| * |p - q| := by
    rw [← abs_mul, mul_sub]
  calc |-(a * sigmaV (V := V) (a * p)) - -(a * sigmaV (V := V) (a * q))|
      = |a| * |sigmaV (V := V) (a * p) - sigmaV (V := V) (a * q)| := by
        rw [show -(a * sigmaV (V := V) (a * p)) - -(a * sigmaV (V := V) (a * q))
            = -a * (sigmaV (V := V) (a * p) - sigmaV (V := V) (a * q)) by ring,
          abs_mul, abs_neg]
    _ ≤ |a| * (|a * p - a * q| / 4) :=
        mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    _ = |a| * (|a| * |p - q| / 4) := by rw [ham]
    _ = (|a| * |a|) * |p - q| / 4 := by ring
    _ = a ^ 2 / 4 * |p - q| := by rw [h2]; ring

/-- Descent lemma for the V-class gap head, MVT route: smoothness
constant `L = a^2/2` (same documented 2× slack as the 2-class
`scalarCE_smooth`). -/
theorem gapHead_smooth {V : Type} [Fintype V] [Nonempty V] (a x y : ℝ) :
    gapHead (V := V) a y ≤ gapHead (V := V) a x
      + deriv (gapHead (V := V) a) x * (y - x)
      + (a ^ 2 / 4) * (y - x) ^ 2 := by
  have hcont : Continuous (gapHead (V := V) a) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact ((hasDerivAt_gapHead a p).differentiableAt.continuousAt)
  have hdiff : ∀ p, HasDerivAt (gapHead (V := V) a)
      (deriv (gapHead (V := V) a) p) p :=
    fun p => ((hasDerivAt_gapHead a p).differentiableAt).hasDerivAt
  have hlip := gapHead_grad_lip (V := V) a
  have hL : (0:ℝ) ≤ a ^ 2 / 4 := by positivity
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hcmem, hcslope⟩ := exists_hasDerivAt_eq_slope
      (gapHead (V := V) a) (deriv (gapHead (V := V) a)) h
      hcont.continuousOn (fun p _ => hdiff p)
    have h1 : gapHead (V := V) a y - gapHead (V := V) a x
        = deriv (gapHead (V := V) a) c * (y - x) := by
      rw [hcslope]
      field_simp
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_nonneg (sub_nonneg.2 hcmem.1.le),
        abs_of_nonneg (sub_nonneg.2 h.le)]
      linarith [hcmem.2]
    exact descent_tail (gapHead (V := V) a) (a ^ 2 / 4) hL x y c h1
      (hlip c x) hcx
  · rw [h, sub_self]
    have hthis : (0:ℝ) ≤ (a ^ 2 / 4) * (y - x) ^ 2 := by positivity
    linarith [hthis]
  · obtain ⟨c, hcmem, hcslope⟩ := exists_hasDerivAt_eq_slope
      (gapHead (V := V) a) (deriv (gapHead (V := V) a)) h
      hcont.continuousOn (fun p _ => hdiff p)
    have h1 : gapHead (V := V) a y - gapHead (V := V) a x
        = deriv (gapHead (V := V) a) c * (y - x) := by
      rw [hcslope]
      field_simp
      ring
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_nonpos (sub_nonpos.2 hcmem.2.le),
        abs_of_nonpos (sub_nonpos.2 h.le)]
      linarith [hcmem.1]
    exact descent_tail (gapHead (V := V) a) (a ^ 2 / 4) hL x y c h1
      (hlip c x) hcx

/-- The gradient map of the V-class gap head as `plStep` expects it. -/
noncomputable def gapHeadGrad {V : Type} [Fintype V] [Nonempty V]
    (a : ℝ) : ℝ → ℝ := fun θ => deriv (gapHead (V := V) a) θ

open scoped InnerProductSpace in
/-- Smoothness of the V-class gap head in inner-product form (on `ℝ`
the inner product is multiplication, the norm the absolute value):
`L = a^2/2`. -/
theorem gapHead_smooth_ip {V : Type} [Fintype V] [Nonempty V] (a x y : ℝ) :
    gapHead (V := V) a y ≤ gapHead (V := V) a x
      + ⟪gapHeadGrad (V := V) a x, y - x⟫_ℝ
      + (a ^ 2 / 2) / 2 * ‖y - x‖ ^ 2 := by
  have h := gapHead_smooth (V := V) a x y
  have hinner : ⟪gapHeadGrad (V := V) a x, y - x⟫_ℝ
      = deriv (gapHead (V := V) a) x * (y - x) := by
    simp [gapHeadGrad]
    ring
  have hnorm : ‖y - x‖ ^ 2 = (y - x) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hinner, hnorm]
  have hcoef : (a ^ 2 / 2) / 2 = a ^ 2 / 4 := by ring
  rw [hcoef]
  exact h

/-- The rate condition `muBallV ≤ L = a^2/2`: the margin-PL constant
fits under the smoothness constant. -/
theorem muBallV_le {V : Type} [Fintype V] [Nonempty V] (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) :
    muBallV (V := V) a B ≤ a ^ 2 / 2 := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hM : (0:ℝ) < Real.exp (a * B) := Real.exp_pos _
  have hmM : Real.exp (-(a * B)) ≤ Real.exp (a * B) := by
    have h1 : -(a * B) ≤ a * B := by nlinarith [ha, hB]
    exact (Real.exp_le_exp).2 h1
  have hkey : ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * B))
      ≤ (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (a * B)) ^ 2 := by
    have hcm : ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * B))
        ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (a * B) := by
      nlinarith [hcnn, hmM]
    nlinarith [hcm, sq_nonneg
      (1 - ((Fintype.card V : ℝ) - 1) * Real.exp (a * B))]
  have hpos : (0:ℝ)
      < 2 * (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (a * B)) ^ 2 := by
    positivity
  have h2 : (0:ℝ) < a ^ 2 := by positivity
  unfold muBallV
  rw [div_le_iff₀ hpos]
  nlinarith [hkey, h2, hpos]

open scoped InnerProductSpace in
/-- THE MULTICLASS MARGIN COROLLARY (unregularized): gradient descent
on the unregularized V-class gap-head CE (`ceOneHot t (gap logits)`
by `gapHead_eq_ceOneHot`), with PL discharged by the multiclass margin
geometry (`margin_pl_multiclass`) and smoothness `L = a^2/2`, drives
the loss to zero geometrically at rate `1 − muBallV a B / (a^2/2)`,
PROVIDED the iterates stay confined to the ball (premise `h_conf` —
the honest pin, same as the 2-class `ce_global_convergence_margin`).
The floor `fstar = 0` is the unattained infimum; the rate bounds the
loss, not the parameter. -/
theorem ce_global_convergence_multiclass {V : Type} [Fintype V]
    [Nonempty V] (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (θ₀ : ℝ) (T : ℕ)
    (h_conf : ∀ t ≤ T,
      |(CEGlobalConvergence.plStep (gapHeadGrad (V := V) a)
          (a ^ 2 / 2))^[t] θ₀| ≤ B) :
    gapHead (V := V) a
        ((CEGlobalConvergence.plStep (gapHeadGrad (V := V) a)
          (a ^ 2 / 2))^[T] θ₀) - 0
      ≤ (1 - muBallV (V := V) a B / (a ^ 2 / 2)) ^ T
        * (gapHead (V := V) a θ₀ - 0) := by
  have hL : (0:ℝ) < a ^ 2 / 2 := by positivity
  have hμL := muBallV_le (V := V) a B ha hB
  exact margin_pl_convergence (gapHead (V := V) a)
    (gapHeadGrad (V := V) a) (a ^ 2 / 2) (muBallV (V := V) a B) 0 B
    hL hμL (gapHead_smooth_ip (V := V) a) (fun x => gapHead_nonneg (V := V) a x)
    (fun x hx => by
      have hb := margin_pl_multiclass (V := V) a B ha hB x hx
      show 2 * muBallV (V := V) a B * (gapHead (V := V) a x - 0)
        ≤ |deriv (gapHead (V := V) a) x| ^ 2
      rw [sq_abs]
      exact hb) θ₀ T h_conf

/-! ### Logit-space margin lemmas (premise-form margin) -/

/-- SOFTMAX-MARGIN-TO-LOSS: if every wrong logit trails the correct
one by at least `γ` (the premise-form margin), the V-class
cross-entropy is at most `log (1 + c·e^{−γ})` with `c = card V − 1`:
the log-sum-exp of the gaps is dominated by the correct term plus the
wrong mass.  General logit vector — no gap-head structure needed. -/
theorem ce_margin_le {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (t : V) (z : V → ℝ) (γ : ℝ) (hγ : ∀ v, v ≠ t → γ ≤ z t - z v) :
    Hagi.ceOneHot t z
      ≤ Real.log (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ)) := by
  have hcard : ∑ v, (if v = t then (1:ℝ) else Real.exp (-γ))
      = 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ) := by
    have hsplit2 : ∀ v : V, (if v = t then (1:ℝ) else Real.exp (-γ))
        = Real.exp (-γ) + (if v = t then 1 - Real.exp (-γ) else 0) := by
      intro v
      by_cases h : v = t <;> simp [h]
    rw [Finset.sum_congr rfl (fun v _ => hsplit2 v), Finset.sum_add_distrib,
      Finset.sum_const, Finset.sum_ite_eq' Finset.univ t
        (fun _ => 1 - Real.exp (-γ))]
    simp
    ring
  have hsplit : ∀ v : V, Real.exp (z v - z t)
      ≤ (if v = t then (1:ℝ) else Real.exp (-γ)) := by
    intro v
    by_cases h : v = t
    · subst h
      simp
    · have hg := hγ v h
      have hle : z v - z t ≤ -γ := by linarith
      rw [ite_eq_right h]
      exact (Real.exp_le_exp).2 hle
  have hsum : ∑ v, Real.exp (z v - z t)
      ≤ 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ) := by
    have hsumle := Finset.sum_le_sum (s := Finset.univ)
      (fun v _ => hsplit v)
    linarith [hsumle, hcard]
  have hpos : (0:ℝ) < ∑ v, Real.exp (z v - z t) := by
    have h0 : (0:ℝ) < Real.exp (z t - z t) := by
      rw [sub_self]
      exact Real.exp_pos _
    have hmem : Real.exp (z t - z t) ≤ ∑ v, Real.exp (z v - z t) :=
      Finset.single_le_sum (fun v _ => Real.exp_nonneg _)
        (Finset.mem_univ t)
    linarith
  have hshift : Hagi.ceOneHot t z
      = Real.log (∑ v, Real.exp (z v - z t)) := by
    unfold Hagi.ceOneHot Hagi.lse
    have hfac : ∑ v, Real.exp (z v)
        = Real.exp (z t) * ∑ v, Real.exp (z v - z t) := by
      have hterm : ∀ v : V, Real.exp (z v)
          = Real.exp (z t) * Real.exp (z v - z t) := by
        intro v
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => hterm v)
    rw [hfac, Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  rw [hshift]
  exact Real.log_le_log hpos (by linarith [hsum])

/-- SOFTMAX-MARGIN-TO-PROBABILITY: under the same premise-form
margin, the correct-class softmax probability is at least
`1/(1+c·e^{−γ}) = e^{γ}/(e^{γ}+c)` — the multiclass margin
domination bound, `c = card V − 1`. -/
theorem softDef_margin_lb {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (t : V) (z : V → ℝ) (γ : ℝ) (hγ : ∀ v, v ≠ t → γ ≤ z t - z v) :
    1 / (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ))
      ≤ Hagi.Prelude.softDef z t := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hposg : (0:ℝ) < Real.exp (-γ) := Real.exp_pos _
  have hden : (0:ℝ)
      < 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ) := by
    nlinarith [hcnn, hposg]
  have hsum : ∑ v, Real.exp (z v)
      ≤ Real.exp (z t) * (1 + ((Fintype.card V : ℝ) - 1)
          * Real.exp (-γ)) := by
    have hcard : ∑ v, (if v = t then (1:ℝ) else Real.exp (-γ))
        = 1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ) := by
      have hsplit2 : ∀ v : V, (if v = t then (1:ℝ) else Real.exp (-γ))
          = Real.exp (-γ) + (if v = t then 1 - Real.exp (-γ) else 0) := by
        intro v
        by_cases h : v = t <;> simp [h]
      rw [Finset.sum_congr rfl (fun v _ => hsplit2 v), Finset.sum_add_distrib,
        Finset.sum_const, Finset.sum_ite_eq' Finset.univ t
          (fun _ => 1 - Real.exp (-γ))]
      simp
      ring
    have hg : ∀ v : V, Real.exp (z v)
        ≤ Real.exp (z t) * (if v = t then (1:ℝ) else Real.exp (-γ)) := by
      intro v
      by_cases h : v = t
      · subst h
        simp [mul_one]
      · have hle : z v - z t ≤ -γ := by
          have := hγ v h
          linarith
        have hexp := (Real.exp_le_exp).2 hle
        rw [ite_eq_right h]
        calc Real.exp (z v) = Real.exp (z t) * Real.exp (z v - z t) := by
              rw [← Real.exp_add]
              congr 1
              ring
          _ ≤ Real.exp (z t) * Real.exp (-γ) :=
              mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
    calc ∑ v, Real.exp (z v)
        ≤ ∑ v, Real.exp (z t) * (if v = t then (1:ℝ) else Real.exp (-γ)) :=
          Finset.sum_le_sum (s := Finset.univ) (fun v _ => hg v)
      _ = Real.exp (z t) * ∑ v, (if v = t then (1:ℝ) else Real.exp (-γ)) :=
          (Finset.mul_sum _ _ _).symm
      _ = Real.exp (z t) * (1 + ((Fintype.card V : ℝ) - 1)
          * Real.exp (-γ)) := by rw [hcard]
  have hSt : (0:ℝ) < ∑ v, Real.exp (z v) :=
    Finset.sum_pos (fun v _ => Real.exp_pos _) Finset.univ_nonempty
  unfold Hagi.Prelude.softDef
  rw [div_le_div_iff₀ hden hSt]
  linarith [hsum]

/-- The multiclass warm-start anchor: a realized margin `γ ≤ a*θstar`
bounds the gap-head loss by `log (1+c·e^{−γ})` (which is in turn at
most `c·e^{−γ}` by `log (1+w) ≤ w`, not stated here) — the margin
anchor of V-class form. -/
theorem margin_anchor_multiclass {V : Type} [Fintype V] [Nonempty V]
    (a θstar γ : ℝ) (hgap : γ ≤ a * θstar) :
    gapHead (V := V) a θstar
      ≤ Real.log (1 + ((Fintype.card V : ℝ) - 1) * Real.exp (-γ)) := by
  have hcnn := gapHeadCard_nonneg (V := V)
  have hmono : ((Fintype.card V : ℝ) - 1) * Real.exp (-(a * θstar))
      ≤ ((Fintype.card V : ℝ) - 1) * Real.exp (-γ) := by
    have h1 : -(a * θstar) ≤ -γ := by linarith
    exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp).2 h1) hcnn
  exact Real.log_le_log (by
    have hcnn' := gapHeadCard_nonneg (V := V)
    have hpos := Real.exp_pos (-(a * θstar))
    nlinarith [hcnn', hpos]) (by linarith [hmono])

end Hagi.Model.CEMarginPL
