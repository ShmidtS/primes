/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.GrowthState
import Hagi.Dynamics.FastGrowth
import Hagi.Probability.ConditionalSuccess
set_option linter.style.header false

/-!
# FastGrowth ↔ GrowthState — the takeoff laws on the growth state

The bridge from the additive `grow` update to multiplicative
takeoff: `additive_as_multiplicative` reads the additive
capability increment as the factor `1 + growGain / capability`;
`growMul`/`growCycle` iterate the transition; `growCycle_capability`
gives the exact closed form `C₀ + t·G` (G invariant).

* `growth_state_takeoff`: with success indicators `sigma t ≤ 1`
  and per-cycle gate `alpha * C_t ≤ G` on successes,
  `(growCycle T S).capability ≥ S.capability * (1+alpha) ^ Σσ`.
* `growth_state_takeoff_window`: with a fixed gain, the success
  count and the certified factor are bounded by constants
  (`Σσ ≤ 1/alpha + 1 − C₀/G`, factor ≤ exp(1 + alpha −
  alpha·C₀/G)); sustained takeoff needs a capability-dependent
  gain and is not claimed here.
* `growth_state_takeoff_probabilistic`: with h_emp_ independent
  [0,1]-success indicators (mean ≥ p0) and a pointwise log-bridge,
  Pr[(growCycle T S ω).capability ≥ S ω.capability *
  exp(a·(p0·T − Δ(T,δ)) − Σε)] ≥ 1 − δ.
-/

open Real Finset MeasureTheory ProbabilityTheory

namespace Hagi.Unified

noncomputable section GrowthBridge

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- For `0 < S.capability`:
`(grow S).capability = S.capability * (1 + S.growGain / S.capability)`. -/
theorem additive_as_multiplicative (S : GrowthState X)
    (hC : 0 < S.capability) :
    (grow S).capability
      = S.capability * (1 + S.growGain / S.capability) := by
  change S.capability + S.growGain = _
  field_simp

/-- The grow transition, to be read through
`growMul_step_multiplicative`: on a certified-success cycle the
capability multiplier is `1 + alpha`; otherwise capability is
non-decreasing. -/
def growMul (S : GrowthState X) : GrowthState X := grow S

theorem growMul_eq_grow (S : GrowthState X) : growMul S = grow S := rfl

/-- The T-fold iteration of the success-gated grow transition. -/
def growCycle : ℕ → GrowthState X → GrowthState X
  | 0, S => S
  | t + 1, S => growMul (growCycle t S)

theorem growCycle_succ (t : ℕ) (S : GrowthState X) :
    growCycle (t + 1) S = growMul (growCycle t S) := rfl

theorem growCycle_zero (S : GrowthState X) : growCycle 0 S = S := rfl

/-- If `0 < S.capability` and `alpha * S.capability ≤ S.growGain`,
then `S.capability * (1 + alpha) ≤ (growMul S).capability`. -/
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

/-- `(growCycle t S).capability = S.capability + t * S.growGain`
(the gain field is invariant under `grow`). -/
theorem growCycle_capability (t : ℕ) (S : GrowthState X) :
    (growCycle t S).capability = S.capability + (t : ℝ) * S.growGain := by
  induction t with
  | zero => rw [growCycle_zero]; ring
  | succ t ih => rw [growCycle_capability_succ, ih]; push_cast; ring

/-- With `0 < alpha`, `sigma t ≤ 1`, positive capability along the
trajectory, and the success gate `alpha * C_t ≤ S.growGain` on
every successful cycle:
`(growCycle T S).capability ≥ S.capability * (1 + alpha) ^ Σσ`.
See `growth_state_takeoff_window`: with a fixed gain the
certified takeoff is bounded. -/
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

/-- With `0 < alpha`, `0 < S.growGain`, the t = 0 gate
`alpha * C₀ ≤ G`, and the gate `alpha * C_t ≤ G` on every
successful cycle (evaluated along the exact trajectory
`C_t = C₀ + t·G`): the success count obeys
`Σσ ≤ 1/alpha + 1 − C₀/G` and the certified factor obeys
`(1+alpha) ^ Σσ ≤ exp(1 + alpha − alpha·C₀/G)`. With a fixed
gain the certified takeoff is a bounded transient; sustained
takeoff would need a capability-dependent gain and is not
claimed. -/
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

/-- With h_emp_ measurable independent [0,1]-valued indicators
`s t` (mean ≥ p0), positive capability along every trajectory, and
the pointwise log-bridge `log C_{t+1} − log C_t ≥ a·s t − eps t`,
the event
`(growCycle T S ω).capability ≥ S ω.capability *
exp(a·(p0·T − concDelta T delta) − Σ eps t)` has probability
≥ `1 − delta` (instantiates `takeoff_time_form`). -/
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

end Hagi.Unified
namespace Hagi
export Hagi.Unified (additive_as_multiplicative growMul growMul_eq_grow growCycle growCycle_succ growCycle_zero growMul_step_multiplicative growCycle_growGain growCycle_capability_succ growCycle_capability growth_state_takeoff growth_state_takeoff_window growth_state_takeoff_probabilistic)
end Hagi
