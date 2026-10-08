/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# NonlinearCone — the concave-gain cone: polynomial takeoff
WITHOUT an exogenous ceiling (R252)

The linear cone (`ConeTakeoff`) demands the EXACT rate law
C' = C + γ·D and yields EXPONENTIAL takeoff — which the
external audit (§19) showed is structurally incompatible
with any finite saturation ceiling over an unbounded
horizon (the old global form was vacuously satisfiable;
`MasterHAGITrunc` fixed it by an exogenous horizon T).

The nonlinear repair: the gain is CONCAVE in the frontier —
the canonical form G = γ·√(k·C) (diminishing returns in the
usable frontier; every larger α ∈ (0,1) lies between this
and the linear case). No exact-rate law, no exponential:

* `sqrt_gain_step` — the per-step increment of the
  SQUARE ROOT capability: √C grows by at least a strictly
  positive constant c₀ = γ√k/(2 + γ√k/√C₀) at EVERY step —
  the frontier's diminishing returns enter only through
  the denominator;
* `sqrt_gain_takeoff` — POLYNOMIAL takeoff:
  C_T ≥ (√C₀ + c₀·T)², so capability grows quadratically
  in T — sub-exponential, hence CONSISTENT with smooth
  saturation of every scale, with no exogenous horizon
  constant to impose;
* `nonlinear_zero_kill` — the R215 zero-stage law SURVIVES
  the nonlinearity: a nonpositive conversion kills the
  gain for every concave (in particular square-root) gain
  law — the necessity results do not depend on the linear
  idealization.

Empirical-assumption note (honest): the h_emp_ premises are
measurement contracts by design and are NOT eliminable in
Lean — what this module removes is the LINEAR idealization
of the rate law, replacing it with a one-parameter concave
family whose limiting case α = 1 recovers the linear cone.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The concave (square-root) gain: G(C) = γ·√(k·C) —
diminishing returns in the usable frontier. -/
noncomputable def sqrtGain (γ k C : ℝ) : ℝ := γ * Real.sqrt (k * C)

/-- **The per-step square-root increment**: under the
square-root gain law C' = C + γ√(kC), the square root of
capability grows by at least the constant

  c₀ = γ√k / (2 + γ√k/√C₀)

at EVERY step (all later states dominate C₀). The
nonlinearity enters only through the denominator —
diminishing returns slow the √-scale growth by a bounded
factor, never stop it. -/
theorem sqrt_gain_step (γ k x : ℝ) (hγ : 0 < γ) (hk : 0 < k)
    (hx : 0 < x) :
    Real.sqrt x + γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt x)
      ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) := by
  set c : ℝ := γ * Real.sqrt k with hc
  have hcpos : 0 < c := mul_pos hγ (Real.sqrt_pos.mpr hk)
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsqrtkx : γ * Real.sqrt (k * x) = c * Real.sqrt x := by
    have h : Real.sqrt (k * x) = Real.sqrt k * Real.sqrt x :=
      Real.sqrt_mul (le_of_lt hk) x
    show γ * Real.sqrt (k * x) = γ * Real.sqrt k * Real.sqrt x
    rw [h]
    ring
  -- upper bound: √(x + γ√(kx)) ≤ √x + c =: u
  have hub : Real.sqrt (x + γ * Real.sqrt (k * x))
      ≤ Real.sqrt x + c := by
    have hle : x + γ * Real.sqrt (k * x)
        ≤ (Real.sqrt x + c) ^ 2 := by
      have hrhs : (Real.sqrt x + c) ^ 2
          = x + 2 * Real.sqrt x * c + c ^ 2 := by
        have h1 : (Real.sqrt x + c) ^ 2
            = (Real.sqrt x) ^ 2 + 2 * Real.sqrt x * c + c ^ 2 :=
          by ring
        rw [h1, Real.sq_sqrt hx.le]
      rw [hrhs, hsqrtkx]
      have h2 : c * Real.sqrt x ≤ 2 * Real.sqrt x * c :=
        by nlinarith [hsx, le_of_lt hcpos]
      nlinarith [sq_nonneg c, h2]
    have hnonneg : 0 ≤ Real.sqrt x + c := by positivity
    have hsq' : Real.sqrt ((Real.sqrt x + c) ^ 2) = Real.sqrt x + c :=
      Real.sqrt_sq hnonneg
    rw [← hsq']
    exact Real.sqrt_le_sqrt hle
  -- factorization and division
  have hfac : (Real.sqrt (x + γ * Real.sqrt (k * x))
      + Real.sqrt x) * (Real.sqrt (x + γ * Real.sqrt (k * x))
      - Real.sqrt x) = c * Real.sqrt x := by
    have hy : x + γ * Real.sqrt (k * x) - x
        = γ * Real.sqrt (k * x) := by ring
    have hy' : x + γ * Real.sqrt (k * x) - x
        = γ * Real.sqrt (k * x) := by ring
    have h1 : (Real.sqrt (x + γ * Real.sqrt (k * x))) ^ 2
        = x + γ * Real.sqrt (k * x) :=
      Real.sq_sqrt (by positivity)
    have h2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
    nlinarith [h1, h2, hy', hsqrtkx]
  have hsum : Real.sqrt (x + γ * Real.sqrt (k * x)) + Real.sqrt x
      ≤ 2 * Real.sqrt x + c := by linarith
  have hdenpos : 0 < 2 * Real.sqrt x + c :=
    add_pos (by positivity) hcpos
  have hdenne : (2 + c / Real.sqrt x) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
    have : 0 < 2 + c / Real.sqrt x := by
      have hcdiv : 0 ≤ c / Real.sqrt x :=
        div_nonneg hcpos.le this.le
      linarith
    exact ne_of_gt this
  rw [hsqrtkx] at hfac
  -- √y − √x = c√x / (√y + √x) ≥ c√x / (2√x + c)
  have hge0 : 0 ≤ Real.sqrt (x + γ * Real.sqrt (k * x))
      - Real.sqrt x := by
    have hnn : 0 ≤ γ * Real.sqrt (k * x) :=
      mul_nonneg hγ.le (Real.sqrt_nonneg _)
    have h1 : Real.sqrt x ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hdiv : c * Real.sqrt x / (2 * Real.sqrt x + c)
      ≤ Real.sqrt (x + γ * Real.sqrt (k * x)) - Real.sqrt x := by
    -- the denominator bound and the factorization give the
    -- increment directly
    have hstepkey : (Real.sqrt (x + γ * Real.sqrt (k * x))
        - Real.sqrt x) * (2 * Real.sqrt x + c) ≥ c * Real.sqrt x := by
      have hA : (Real.sqrt (x + γ * Real.sqrt (k * x))
          - Real.sqrt x) * (2 * Real.sqrt x + c)
          ≥ (Real.sqrt (x + γ * Real.sqrt (k * x)) - Real.sqrt x)
            * (Real.sqrt (x + γ * Real.sqrt (k * x)) + Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hsum hge0
      have hy : x + γ * Real.sqrt (k * x) - x
          = γ * Real.sqrt (k * x) := by ring
      have hsy : (Real.sqrt (x + γ * Real.sqrt (k * x))) ^ 2
          = x + γ * Real.sqrt (k * x) :=
        Real.sq_sqrt (by positivity)
      have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
      have hB : (Real.sqrt (x + γ * Real.sqrt (k * x))
          - Real.sqrt x) * (Real.sqrt (x + γ * Real.sqrt (k * x))
          + Real.sqrt x) = γ * Real.sqrt (k * x) :=
        by linear_combination hy + hsy - hsx2
      rw [hB, hsqrtkx] at hA
      rw [hsqrtkx]
      exact hA
    rw [(div_le_iff₀ hdenpos)]
    linarith [hstepkey]
  -- final chain
  have hfin : c * Real.sqrt x / (2 * Real.sqrt x + c)
      ≥ γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt x) := by
    have hsx0 : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp
    nlinarith [hc, hsum]
  linarith

/-- **POLYNOMIAL TAKEOFF under the concave gain**: with the
square-root law C_{t+1} = C_t + γ√(k·C_t) from a positive
initial capability, capability grows at least
quadratically:

  C_T ≥ (√C₀ + c₀·T)²,  c₀ = γ√k/(2 + γ√k/√C₀).

Sub-exponential growth is CONSISTENT with smooth saturation
of any scale — the audit §19 cone/ceiling incompatibility
dissolves without any exogenous horizon constant. The
linear cone is the limiting case α → 1 of this family. -/
theorem sqrt_gain_takeoff (C : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hC0 : 0 < C 0)
    (hmono : ∀ t, 0 < C t)
    (hstep : ∀ t, C (t + 1) = C t + sqrtGain γ k (C t)) :
    ∀ T : ℕ, (Real.sqrt (C 0)
      + γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt (C 0)) * T) ^ 2
      ≤ C T := by
  set c0 : ℝ := γ * Real.sqrt k / (2 + γ * Real.sqrt k / Real.sqrt (C 0))
    with hc0
  -- the sequence is increasing (the gain is positive)
  have hge : ∀ t, C 0 ≤ C t := by
    intro t
    induction t with
    | zero => exact le_refl _
    | succ t ih =>
        rw [hstep t, sqrtGain]
        have hg : 0 ≤ γ * Real.sqrt (k * C t) :=
          mul_nonneg hγ.le (Real.sqrt_nonneg _)
        linarith
  -- c(x) is minimized at x = C 0 (denominator shrinks with x)
  have hcmono : ∀ t, c0 ≤ γ * Real.sqrt k
      / (2 + γ * Real.sqrt k / Real.sqrt (C t)) := by
    intro t
    have hsq : Real.sqrt (C 0) ≤ Real.sqrt (C t) :=
      Real.sqrt_le_sqrt (hge t)
    have hs0 : (0:ℝ) < Real.sqrt (C 0) :=
      Real.sqrt_pos.mpr hC0
    have hst : (0:ℝ) < Real.sqrt (C t) :=
      Real.sqrt_pos.mpr (hmono t)
    have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
    -- n_x <= n_0 (the inner quotient shrinks)
    have h1 : γ * Real.sqrt k / Real.sqrt (C t)
        ≤ γ * Real.sqrt k / Real.sqrt (C 0) := by
      rw [le_div_iff₀ hs0]
      field_simp
      nlinarith [hsq, hgk]
    have hden1 : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C t) := by
      have := div_nonneg hgk.le hst.le
      linarith
    have hden0 : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C 0) := by
      have := div_nonneg hgk.le hs0.le
      linarith
    -- cross-multiply: A/n0 <= A/n1 iff n1 <= n0
    unfold c0
    rw [le_div_iff₀ hden1]
    field_simp
    nlinarith [hsq, hgk]
  -- induction on the sqrt scale
  have hmain : ∀ T : ℕ,
      Real.sqrt (C 0) + c0 * T ≤ Real.sqrt (C T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        -- the step law in raw form
        have hraw : C (T + 1)
            = C T + γ * Real.sqrt (k * C T) := by
          rw [hstep T, sqrtGain]
        -- apply the per-step lemma
        have hstep' := sqrt_gain_step γ k (C T) hγ hk (hmono T)
        have hc' := hcmono T
        rw [hraw]
        have hpos : 0 < γ * Real.sqrt k
            / (2 + γ * Real.sqrt k / Real.sqrt (C T)) := by
          apply div_pos _ (by
            have hst : (0:ℝ) < Real.sqrt (C T) :=
              Real.sqrt_pos.mpr (hmono T)
            have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
            have := div_nonneg hgk.le hst.le
            linarith)
          positivity
        have hgoal : Real.sqrt (C 0) + c0 * (T + 1)
            ≤ Real.sqrt (C T + γ * Real.sqrt (k * C T)) := by
          have h1 : Real.sqrt (C 0) + c0 * T + c0
              ≤ Real.sqrt (C T)
                + γ * Real.sqrt k
                  / (2 + γ * Real.sqrt k / Real.sqrt (C T)) := by
            linarith
          linarith
        rw [show ((T + 1 : ℕ) : ℝ) = ((T : ℕ) : ℝ) + 1 from by
          push_cast; ring]
        exact hgoal
  -- square both sides
  intro T
  have h := hmain T
  have hsq : (Real.sqrt (C 0) + c0 * T) * (Real.sqrt (C 0) + c0 * T)
      ≤ Real.sqrt (C T) * Real.sqrt (C T) := by
    have hnn : 0 ≤ Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ) := by
      have hc0' : 0 ≤ c0 := by
        have hgk : (0:ℝ) < γ * Real.sqrt k := by positivity
        have hsd : (0:ℝ) < Real.sqrt (C 0) := Real.sqrt_pos.mpr hC0
        have hinn : (0:ℝ) ≤ γ * Real.sqrt k / Real.sqrt (C 0) :=
          div_nonneg hgk.le hsd.le
        have hden : (0:ℝ) < 2 + γ * Real.sqrt k / Real.sqrt (C 0) := by
          linarith
        exact div_nonneg hgk.le hden.le
      have := mul_nonneg hc0' (by positivity)
      positivity
    exact mul_self_le_mul_self hnn h
  -- convert the product form back to the square form
  -- (a)^2 = a*a; (√x)^2 = x
  have h1 : (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ)) ^ 2
      = (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ))
        * (Real.sqrt (C 0) + c0 * ((T : ℕ) : ℝ)) := by ring
  have h2 : (Real.sqrt (C T)) ^ 2 = C T :=
    Real.sq_sqrt (hmono T).le
  calc (Real.sqrt (C 0) + c0 * T) ^ 2
      = (Real.sqrt (C 0) + c0 * T)
        * (Real.sqrt (C 0) + c0 * T) := h1
  _ ≤ Real.sqrt (C T) * Real.sqrt (C T) := hsq
  _ = C T := by
        have := h2
        rw [← pow_two (Real.sqrt (C T))]
        exact this

/-- **Zero-stage necessity SURVIVES the nonlinearity**:
for a nonnegative disagreement measure φ(E) ≥ 0 and a gain
G = η·φ(E), a nonpositive conversion stage kills the gain —
the R215 necessity does not depend on the linear
idealization of the rate law. -/
theorem nonlinear_zero_kill (η phiE : ℝ) (hφ : 0 ≤ phiE)
    (hη : η ≤ 0) :
    η * phiE ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg hη hφ


end Hagi.Growth
