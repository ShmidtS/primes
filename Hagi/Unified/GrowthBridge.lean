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

/-- **The closed form of the capability channel** (R102): the
additive law iterated — `growCycle t S` has capability exactly
`C₀ + t·G` with G the INVARIANT gain (`growCycle_growGain`).
This exact formula is the basis of `growth_state_takeoff_window`. -/
theorem growCycle_capability (t : ℕ) (S : GrowthState X) :
    (growCycle t S).capability = S.capability + (t : ℝ) * S.growGain := by
  induction t with
  | zero => rw [growCycle_zero]; ring
  | succ t ih => rw [growCycle_capability_succ, ih]; push_cast; ring

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
the scalar trajectory C t := (growCycle t S).capability.
See `growth_state_takeoff_window` (R102) for the honest
companion: with a FIXED gain the certified exponential
takeoff is BOUNDED — read that window theorem before
reading unbounded exponential growth into this law. -/
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

/-- **The certified-takeoff WINDOW (R102; the external audit's
vacuity finding converted into a theorem)**. With the gain
field G = growGain INVARIANT under grow (`growCycle_growGain`)
and the success gate α·C_t ≤ G (the `hsuccess` hypothesis of
`growth_state_takeoff`, evaluated along the exact additive
trajectory C_t = C₀ + t·G of `growCycle_capability`), the
certified exponential takeoff CANNOT run forever:

- every successful cycle's time index obeys
  t ≤ 1/α − C₀/G, so the success count over any horizon T is
  at most 1/α + 1 − C₀/G (an ABSOLUTE window, independent of
  T);
- hence the certified multiplicative factor
  (1+α)^(Σσ) ≤ exp(1 + α − α·C₀/G) ≤ e·e^α — bounded by a
  CONSTANT, however long the loop runs.

The audit's suggested e^{G/C₀} form is NOT provable in this
generality (for G/C₀ small the constant e·e^α bound is
larger than e^{G/C₀}); the window above is the honest tight
form. Consequence, stated plainly: with a FIXED gain the
certified takeoff is a bounded transient; SUSTAINED takeoff
requires a capability-dependent gain G_t ≥ α·C_t at every
cycle — the open bridge (a gain-growth law tied to the
capability field), not a theorem of the current state
model. The hypothesis `hgate0 : α·C₀ ≤ G` is the t = 0
instance of the gate: without it no cycle can ever succeed
(the window is then empty and the takeoff count is 0). -/
theorem growth_state_takeoff_window (S : GrowthState X) (sigma : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hG : 0 < S.growGain)
    (hgate0 : alpha * S.capability ≤ S.growGain)
    (hgate : ∀ t, sigma t = 1 →
      alpha * (growCycle t S).capability ≤ S.growGain)
    (hsig : ∀ t, sigma t ≤ 1)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, sigma t : ℝ)
      ≤ 1 / alpha + 1 - S.capability / S.growGain
    ∧ (1 + alpha) ^ (∑ t ∈ Finset.range T, sigma t)
      ≤ Real.exp (1 + alpha - alpha * S.capability / S.growGain) := by
  -- the exact additive trajectory: C_t = C₀ + t·G
  have hadd : ∀ t : ℕ, (growCycle t S).capability
      = S.capability + (t : ℝ) * S.growGain := fun t =>
    growCycle_capability t S
  -- every success time obeys the gate in its additive form:
  -- α·(C₀ + t·G) ≤ G  ⟺  t ≤ 1/α − C₀/G
  have hpos : 0 < alpha * S.growGain := mul_pos halpha hG
  have htime : ∀ t : ℕ, sigma t = 1 →
      (t : ℝ) ≤ 1 / alpha - S.capability / S.growGain := by
    intro t hs
    have hg := hgate t hs
    rw [hadd] at hg
    have hkey : (t : ℝ) * (alpha * S.growGain)
        ≤ S.growGain - alpha * S.capability := by
      have e : (t : ℝ) * (alpha * S.growGain)
          = alpha * ((t : ℝ) * S.growGain) := by ring
      rw [e]
      linarith
    rw [show 1 / alpha - S.capability / S.growGain
        = (S.growGain - alpha * S.capability) / (alpha * S.growGain) from by
      field_simp]
    exact (le_div_iff₀ hpos).mpr hkey
  -- the success count is the number of admissible times, and
  -- every admissible time is below ⌊window⌋ in ℕ
  set tmax : ℝ := 1 / alpha - S.capability / S.growGain with htmax
  have htmax_nonneg : 0 ≤ tmax := by
    have h1 : S.capability * alpha ≤ S.growGain := by
      rw [mul_comm]
      exact hgate0
    have h2 : S.capability / S.growGain ≤ 1 / alpha := by
      rw [div_le_iff₀ hG, div_mul_eq_mul_div, one_mul, le_div_iff₀ halpha]
      exact h1
    rw [htmax]
    linarith
  have hcount : (∑ t ∈ Finset.range T, sigma t : ℝ) ≤ tmax + 1 := by
    have hle : ∀ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ (if (t : ℝ) ≤ tmax then 1 else 0) := by
      intro t ht
      rcases Nat.lt_or_ge (sigma t) 1 with h0 | h0
      · have hs0 : sigma t = 0 := by omega
        rw [hs0, Nat.cast_zero]
        split_ifs <;> norm_num
      · have hb := hsig t
        have hs1 : sigma t = 1 := by omega
        have h4 := htime t hs1
        have h5 : (t : ℝ) ≤ tmax := by rw [htmax]; exact h4
        simp [hs1, h5]
    have hsum : ∑ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ ∑ t ∈ Finset.range T, (if (t : ℝ) ≤ tmax then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun t ht => hle t ht
    have hfil : ∑ t ∈ Finset.range T, (if (t : ℝ) ≤ tmax then (1 : ℝ) else 0)
        = (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ) := by
      rw [← Finset.sum_filter (p := fun t : ℕ => (t : ℝ) ≤ tmax)]
      simp
    -- the integer ceiling of the window: every admissible t < K + 1
    have hfloornn : (0 : ℤ) ≤ ⌊tmax⌋ := Int.floor_nonneg.mpr htmax_nonneg
    set K : ℕ := Int.toNat ⌊tmax⌋ with hK
    have hKz : (K : ℤ) = ⌊tmax⌋ := Int.toNat_of_nonneg hfloornn
    have hlt : tmax < (K : ℝ) + 1 := by
      have h6 : tmax < (⌊tmax⌋ : ℝ) + 1 := by
        have := Int.lt_floor_add_one tmax
        exact_mod_cast this
      have h7 : ((K : ℤ) : ℝ) = (⌊tmax⌋ : ℝ) := by rw [hKz]
      have h8 : (K : ℝ) + 1 = ((K : ℤ) : ℝ) + 1 := by push_cast; ring
      rw [h8, h7]
      exact h6
    have hsub : (Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)
        ⊆ Finset.range (K + 1) := by
      intro t ht
      simp only [Finset.mem_filter] at ht
      refine Finset.mem_range.mpr ?_
      have h9 : (t : ℝ) < (K : ℝ) + 1 := lt_of_le_of_lt ht.2 hlt
      exact_mod_cast h9
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have hKle : (K : ℝ) ≤ tmax := by
      have h10 : (⌊tmax⌋ : ℝ) ≤ tmax := Int.floor_le tmax
      have h11 : (K : ℝ) ≤ (⌊tmax⌋ : ℝ) := by
        have h12 : (K : ℤ) ≤ ⌊tmax⌋ := by rw [hKz]
        exact_mod_cast h12
      linarith
    have hcardR : ((K + 1 : ℕ) : ℝ) ≤ tmax + 1 := by
      push_cast
      linarith
    have hsumR : ∑ t ∈ Finset.range T, (sigma t : ℝ)
        ≤ (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ) := by
      rw [← hfil]
      exact hsum
    have hcR : (((Finset.range T).filter (fun t : ℕ => (t : ℝ) ≤ tmax)).card : ℝ)
        ≤ ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    linarith
  refine ⟨by
    have hc1 := hcount
    rw [htmax] at hc1
    linarith, ?_⟩
  -- (2): (1+α)^N ≤ e^{αN} (add_one_le_exp iterated), αN ≤ α·window
  have hpow : ∀ n : ℕ, (1 + alpha) ^ n ≤ Real.exp (alpha * (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : 1 + alpha ≤ Real.exp alpha := by
          have := Real.add_one_le_exp alpha
          linarith
        have hnn : 0 ≤ 1 + alpha := by linarith
        have hnnn : 0 ≤ (1 + alpha) ^ n := pow_nonneg hnn n
        rw [pow_succ]
        calc (1 + alpha) ^ n * (1 + alpha)
            ≤ Real.exp (alpha * (n : ℝ)) * (1 + alpha) :=
                mul_le_mul_of_nonneg_right ih hnn
          _ ≤ Real.exp (alpha * (n : ℝ)) * Real.exp alpha :=
                mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
          _ = Real.exp (alpha * ((n + 1 : ℕ) : ℝ)) := by
              have he : Real.exp (alpha * (n : ℝ)) * Real.exp alpha
                  = Real.exp (alpha * (n : ℝ) + alpha) :=
                (Real.exp_add _ _).symm
              rw [he]
              congr 1
              push_cast
              ring
  have hN := hpow (∑ t ∈ Finset.range T, sigma t)
  have hNle : alpha * ((∑ t ∈ Finset.range T, sigma t : ℕ) : ℝ)
      ≤ 1 + alpha - alpha * S.capability / S.growGain := by
    have hc2 : ((∑ t ∈ Finset.range T, sigma t : ℕ) : ℝ) ≤ tmax + 1 := by
      push_cast
      exact hcount
    rw [htmax] at hc2
    have hEq : alpha * (1 / alpha - S.capability / S.growGain + 1)
        = 1 + alpha - alpha * S.capability / S.growGain := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_left hc2 halpha.le
    rw [hEq] at hmul
    exact hmul
  exact le_trans hN (Real.exp_le_exp.mpr hNle)

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