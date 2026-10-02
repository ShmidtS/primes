/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.GrowthState
import Hagi.Dynamics.FastGrowth
import Hagi.Probability.ConditionalSuccess
set_option linter.style.header false

/-!
# R96: FastGrowth ↔ GrowthState — the multiplicative takeoff as a GrowthState theorem

The external review (§8) flagged that `capability_takeoff_counted`
(R85, FastGrowth.lean) is a theorem about ABSTRACT scalars C : ℕ → ℝ,
while the real growth loop (`grow`, R91) updates capability
ADDITIVELY: capability_{t+1} = capability_t + growGain. The
exponential-takeoff law was therefore not a theorem about the actual
`GrowthState`. This module is the bridge.

**The additive→multiplicative reading.** `grow`'s additive increment
`capability + growGain` IS a multiplicative update in disguise: with
capability > 0,

  capability + growGain = capability · (1 + growGain / capability),

i.e. the per-cycle growth factor is 1 + α_t with the FIELD-COMPUTED
α_t := growGain / capability (the measured increment normalized by the
current capability — the natural relative-gain reading of the existing
state fields; no new free parameter). `additive_as_multiplicative`
is this definitional bridge lemma; `growMul` is the success-gated form
of `grow` whose capability channel is literally the multiplicative
law of `capability_multiplicative`/`capability_takeoff_counted`.

Results:
* `additive_as_multiplicative` — (grow S).capability =
  S.capability * (1 + S.growGain / S.capability) for S.capability > 0.
* `growMul` — the success-gated grow transition: on a successful
  cycle (indicator σ t = 1) the multiplicative law C·(1+α) is
  certified; on failure capability is merely non-decreasing
  (gain ≥ 0), the neutral multiplier 1 — the semantics
  capability_takeoff_counted iterates.
* `growth_state_takeoff` — the counted takeoff law ON GrowthState:
  iterating `growMul` for T cycles,
  (growCycle T S).capability ≥ S.capability · (1+α)^{Σ_{t<T} σ t},
  transported from `capability_takeoff_counted` with
  C t := (growCycle t S).capability — the takeoff theorem now
  mentions GrowthState, resolving the review's complaint.
* `growth_state_takeoff_probabilistic` — the stochastic half
  composed at the GrowthState level: with a random initial state
  S : Ω → GrowthState X, independent [0,1]-success indicators
  (mean ≥ p₀) and the pointwise log-bridge along the growMul
  trajectory, Pr[(growCycle T S ω).capability ≥ S ω.capability ·
  exp(a(p₀T − Δ(T,δ)) − Σε)] ≥ 1 − δ (an instantiation of
  `takeoff_time_form`, R95, with the capability read from the
  GrowthState trajectory).
-/

open Real Finset MeasureTheory ProbabilityTheory

namespace Hagi

noncomputable section GrowthBridge

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The definitional bridge**: `grow`'s additive capability update
is the multiplicative update with the field-computed growth factor
1 + growGain / capability — the measured increment normalized by the
current capability (the relative-gain reading of the R91 fields;
requires capability > 0). -/
theorem additive_as_multiplicative (S : GrowthState X)
    (hC : 0 < S.capability) :
    (grow S).capability
      = S.capability * (1 + S.growGain / S.capability) := by
  change S.capability + S.growGain = _
  field_simp

/-- **The success-gated grow transition**: on a SUCCESSFUL cycle
(σ = 1) the capability channel is certified multiplicative with the
explicit factor 1 + α (α the design growth rate, certified against
the state's measured gain via hgain); on failure (σ = 0) capability
is merely non-decreasing (hgnonneg: the measured gain is ≥ 0) —
exactly the per-cycle semantics that `capability_takeoff_counted`
iterates. The transition itself is `grow` (all other fields update
as in R91); the multiplicative reading of its capability channel is
`additive_as_multiplicative`. -/
def growMul (S : GrowthState X) : GrowthState X := grow S

theorem growMul_eq_grow (S : GrowthState X) : growMul S = grow S := rfl

/-- The T-fold iteration of the success-gated grow transition. -/
def growCycle : ℕ → GrowthState X → GrowthState X
  | 0, S => S
  | t + 1, S => growMul (growCycle t S)

theorem growCycle_succ (t : ℕ) (S : GrowthState X) :
    growCycle (t + 1) S = growMul (growCycle t S) := rfl

theorem growCycle_zero (S : GrowthState X) : growCycle 0 S = S := rfl

/-- The per-cycle multiplicative law along the growMul trajectory:
on success (σ t = 1) the measured gain certifies the multiplier
(1 + α); on failure the trajectory is non-decreasing. This is the
`hmul` hypothesis of `capability_takeoff_counted`, derived from the
GrowthState semantics (additive gain + nonneg + success gate), not
assumed on abstract scalars. -/
theorem growMul_step_multiplicative (S : GrowthState X) (alpha : ℝ)
    (hCpos : 0 < S.capability)
    (hsuccess : alpha * S.capability ≤ S.growGain) :
    S.capability * (1 + alpha) ≤ (growMul S).capability := by
  have hbr := additive_as_multiplicative S hCpos
  have hd : alpha ≤ S.growGain / S.capability := (le_div_iff₀ hCpos).mpr hsuccess
  have hm : S.capability * alpha
      ≤ S.capability * (S.growGain / S.capability) :=
    mul_le_mul_of_nonneg_left hd hCpos.le
  rw [growMul_eq_grow, hbr]
  nlinarith

/-- The measured grow-gain field is INVARIANT under the grow
transition, hence constant along the growCycle trajectory. -/
theorem growCycle_growGain (t : ℕ) (S : GrowthState X) :
    (growCycle t S).growGain = S.growGain := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [growCycle_succ, growMul, grow, ih]

theorem growCycle_capability_succ (t : ℕ) (S : GrowthState X) :
    (growCycle (t + 1) S).capability
      = (growCycle t S).capability + S.growGain := by
  rw [growCycle_succ, growMul, grow, growCycle_growGain]

/-- **The counted takeoff law ON GrowthState** (R85 transported to
the real growth-loop state, the review §8 fix): iterating the
success-gated grow transition for T cycles, with σ t the success
indicator (σ t ≤ 1) of cycle t, the capability FIELD of the iterated
state obeys

  (growCycle T S).capability ≥ S.capability · (1+α)^{Σ_{t<T} σ t}

— exponential in the success count, with the capability read from
the GrowthState. The per-cycle multiplicative law is DERIVED from
the state semantics (`growMul_step_multiplicative` from the additive
gain fields), then `capability_takeoff_counted` (R85) is applied to
the scalar trajectory C t := (growCycle t S).capability. -/
theorem growth_state_takeoff (S : GrowthState X) (sigma : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hgnonneg : 0 ≤ S.growGain)
    (hCpos : ∀ t, 0 < (growCycle t S).capability)
    (hsuccess : ∀ t, sigma t = 1 →
      alpha * (growCycle t S).capability ≤ S.growGain)
    (hsig : ∀ t, sigma t ≤ 1)
    (T : ℕ) :
    (growCycle T S).capability
      ≥ S.capability * (1 + alpha) ^ (∑ t ∈ Finset.range T, sigma t) := by
    -- per-cycle: C(t+1) ≥ C t · (1+α)^(σ t), case-split on σ t ∈ {0,1}
    have hmul : ∀ t, (growCycle (t + 1) S).capability
        ≥ (growCycle t S).capability * (1 + alpha) ^ (sigma t) := by
      intro t
      have hb := hsig t
      rcases Nat.lt_or_ge (sigma t) 1 with h0 | h0
      · -- failure: σ t = 0, multiplier 1
        have hs0 : sigma t = 0 := by omega
        rw [hs0, pow_zero, mul_one, growCycle_capability_succ]
        linarith
      · -- success: σ t = 1, the multiplicative law
        have hs1 : sigma t = 1 := by omega
        have hm := growMul_step_multiplicative (growCycle t S) alpha
          (hCpos t)
          (by rw [growCycle_growGain]; exact hsuccess t hs1)
        have hstep : (growCycle (t + 1) S).capability
            = (growMul (growCycle t S)).capability := rfl
        calc (growCycle (t + 1) S).capability
            = (growMul (growCycle t S)).capability := hstep
          _ ≥ (growCycle t S).capability * (1 + alpha) := hm
          _ = (growCycle t S).capability * (1 + alpha) ^ (sigma t) := by
              rw [hs1, pow_one]
    exact capability_takeoff_counted
      (fun t => (growCycle t S).capability) sigma alpha halpha hmul T

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The stochastic takeoff ON GrowthState** (R95 composed at the
state level): with a random initial state S : Ω → GrowthState X,
independent [0,1]-valued success indicators with per-cycle mean ≥ p₀
(h_emp_), and the POINTWISE log-bridge along the growMul trajectory
(log C_{t+1} − log C_t ≥ a·S_t − ε_t, C t the capability field of
the iterated state), then with probability ≥ 1 − δ the capability
FIELD of the T-cycled state obeys the exponential law

  (growCycle T S ω).capability
    ≥ S ω.capability · exp(a·(p₀·T − Δ(T,δ)) − Σ_{t<T} ε_t),

Δ(T,δ) = √(2·T·log(1/δ)). Instantiates `takeoff_time_form` (R95)
with C t ω := (growCycle t (S ω)).capability — the stochastic half
of the takeoff theorem now also about GrowthState. -/
theorem growth_state_takeoff_probabilistic
    (S : Ω → GrowthState X) (s : ℕ → Ω → ℝ)
    {T : ℕ} {delta p0 a : ℝ} {eps : ℕ → ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (ha : 0 ≤ a)
    (hCpos : ∀ t ω, 0 < (growCycle t (S ω)).capability)
    (hbridge : ∀ t ω, Real.log ((growCycle (t + 1) (S ω)).capability)
        - Real.log ((growCycle t (S ω)).capability) ≥ a * s t ω - eps t)
    (h_emp_meas : ∀ t, Measurable (s t))
    (h_emp_01 : ∀ t ω, s t ω ∈ Set.Icc 0 1)
    (h_emp_indep : iIndepFun s μ)
    (h_emp_p : ∀ t, p0 ≤ μ[s t]) :
    μ.real {ω | (growCycle T (S ω)).capability ≥ (S ω).capability * Real.exp
      (a * (p0 * (T : ℝ) - concDelta T delta) - ∑ t ∈ Finset.range T, eps t)}
      ≥ 1 - delta := by
  -- the capability trajectory of the random state, an Ω-indexed scalar path
  set C : ℕ → Ω → ℝ := fun t ω => (growCycle t (S ω)).capability with hC
  have hmain := takeoff_time_form (S := s) (C := C) (T := T) (delta := delta)
    (p0 := p0) (a := a) (eps := eps) hdelta hdelta1 ha
    (fun t ω => hCpos t ω) (fun t ω => hbridge t ω)
    h_emp_meas h_emp_01 h_emp_indep h_emp_p
  have hzero : C 0 = fun ω => (S ω).capability := rfl
  rw [hzero] at hmain
  exact hmain

end GrowthBridge

end Hagi