/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Core.Concat
import Hagi.Model.CEGlobalConvergence

/-!
# Margin-based PL for the unregularized cross-entropy

C373 research queue #3.  `Hagi.Model.CEGlobalConvergence` pinned the
PL premise of the unregularized CE open: the regularized route
(`ce_global_convergence_reg`, C358) discharges PL through the ℓ2
strong convexity constant `λ` (weight decay).  This module replaces
that λ-crutch with data geometry: on a realizable 2-class problem with
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

Reference search (research notes, `.tmp/C376/research.md`, via
ask.sciencemadereadable.com) found: Karimi–Nutini–Schmidt 2016
(PL linear convergence, doi:10.1007/978-3-319-46128-1_50 — the PL
machinery this repo already carries); Ji–Telgarsky 2018 (global PL
falsity on separable data); Freund–Grigas–Mazumder 2018 (logistic
conditioning |f''| ≤ a²/4).  No Mathlib margin-PL API in the pinned
commit; the derivation is self-contained.

no reference: the explicit constant μ = a²·e^{−aB}/8 is derived here
from classical inequalities (`log (1+u) ≤ u`, AM-GM on `u`); no
formalization source found.
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

end Hagi.Model.CEMarginPL
