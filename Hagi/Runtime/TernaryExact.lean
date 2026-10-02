/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.Ternary
import Hagi.Energy.QuantBridge
set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# R103: the ternary saturation bridge — the actual quantizer's
global error, honestly

The external audit (§5) found the gap in the R70 chain
(`Hagi.Energy.QuantBridge`): `quant_energy_bridge` ASSUMES
`∀ i, |w i − q i| ≤ s/2` — per-coordinate rounding error ≤ half
step. The ACTUAL ternary quantizer
(`Hagi.Energy.Ternary.roundTern`: nearest-grid rounding on
`{-1, 0, +1}·s`, which SATURATES — a coordinate with
`|w i| > 3s/2` clips to `±s`) does not guarantee this: a
saturated coordinate's error is its distance to the clipped
endpoint `|w i| − s`, not `≤ s/2`.

This module closes the gap by splitting the error budget:

* **in-range** coordinates (`|w i| ≤ 3s/2`): rounding error
  `≤ s/2` (`qTern_error_in`, from `roundTern_error_scaled`) —
  the part the old bridge assumed for ALL coordinates;
* **out-of-range** coordinates: error exactly `|w i| − s`
  (`qTern_error_out`) — the explicit saturation tail
  `satTail s w = Σ_out (|w i| − s)²`.

`ternary_split_bound` is the exact decomposition of the total
squared quantization error into these two named parts;
`quant_energy_bridge_saturation` is the honest global energy
bound `ΔE ≤ κ·(√n·s/2 + √satTail)` with NO in-range assumption;
`no_saturation_recover` shows that when the tail vanishes the
old R70 hypothesis is DERIVED, not assumed.

**Runtime mapping.** `satTail` is the pre-quantization
diagnostic: per tensor, measure `Σ overshoot² = Σ (|w| − s)²`
over coordinates outside `3s/2` (computable from a checkpoint);
compare `κ·√satTail` against the cost of a rescale/clip policy
(widen s, clip, or split the group) and pick the cheaper side.
-/

namespace Hagi

open Finset Real
open scoped Classical

/-! ## The actual (saturating) quantizer and the range split -/

/-- The ACTUAL ternary quantizer of the format: nearest-grid
rounding on `{-1, 0, +1}` with per-group scale `s`, saturated —
`qTern s x = s · roundTern (x / s)`, so any `x` with
`|x| > 3s/2` clips to `±s`. -/
noncomputable def qTern (s x : ℝ) : ℝ := s * ((roundTern (x / s) : ℝ))

/-- A coordinate is **in range** for the ternary grid at scale
`s` when nearest-grid rounding covers it: `|x| ≤ 3s/2` (within
half a step of the endpoint level `s`). -/
def ternInRange (s x : ℝ) : Prop := |x| ≤ 3 * s / 2

/-- **The saturation tail** — the measured saturation mass of a
weight vector: the sum of squared overshoots
`Σ_{|w i| > 3s/2} (|w i| − s)²` over the out-of-range
coordinates. Computable from a checkpoint (see the module
docstring: the pre-quantization diagnostic). -/
noncomputable def satTail (s : ℝ) {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)), (|w i| - s) ^ 2

/-! ## Pointwise error: in-range vs saturated -/

/-- **In-range coordinates** keep the half-step guarantee: for
`|x| ≤ 3s/2` the saturating quantizer's error is at most `s/2`
(this is `roundTern_error_scaled` restated for `qTern`). -/
theorem qTern_error_in (s x : ℝ) (hs : 0 < s) (hx : ternInRange s x) :
    |x - qTern s x| ≤ s / 2 :=
  roundTern_error_scaled s x hs hx

/-- **Saturated coordinates have EXACTLY the clipped distance as
error**: for `|x| > 3s/2` the quantizer returns the endpoint
`±s`, so the error is `|x| − s` — the overshoot, not `≤ s/2`.
This is the point the audit flagged: the R70 hypothesis fails
precisely here. -/
theorem qTern_error_out (s x : ℝ) (hs : 0 < s) (hx : ¬ ternInRange s x) :
    |x - qTern s x| = |x| - s := by
  have hout : 3 * s / 2 < |x| := not_le.mp hx
  simp only [qTern, roundTern]
  rcases lt_or_ge x 0 with hx0 | hx0
  · -- x < 0: clips to −s
    have hxlt : x < -3 * s / 2 := by
      rw [abs_of_neg hx0] at hout; linarith
    have hsx : x / s < -1 / 2 := by
      rw [div_lt_iff₀ hs]; linarith
    rw [if_neg (by linarith : ¬ (1 / 2 < x / s)), if_pos hsx]
    push_cast
    rw [show x - s * (-1 : ℝ) = x + s by ring,
      show |x| = -x from abs_of_neg hx0,
      abs_of_neg (by linarith : x + s < 0)]
    ring
  · -- 0 ≤ x, in fact x > 3s/2 > 0: clips to +s
    have hxgt : 3 * s / 2 < x := by
      rw [abs_of_nonneg hx0] at hout; linarith
    have hxpos : 0 < x := by linarith
    have hsx : 1 / 2 < x / s := by
      rw [lt_div_iff₀ hs]; linarith
    rw [if_pos hsx]
    push_cast
    rw [show x - s * (1 : ℝ) = x - s by ring,
      show |x| = x from abs_of_pos hxpos,
      abs_of_nonneg (by linarith : 0 ≤ x - s)]

/-! ## The exact split of the total squared error -/

/-- **`ternary_split_bound`** — the exact decomposition of the
total squared quantization error of the ACTUAL quantizer into
its two named parts: the in-range (rounding) part and the
saturation tail. No inequality, no assumption on the weights:
`‖w − Q(w)‖² = Σ_in (w i − Q i)² + satTail s w`. -/
theorem ternary_split_bound (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i, (w i - qTern s (w i)) ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
        + satTail s w := by
  have h1 : ∀ i : Fin n, (if ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
        + (if ¬ ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
      = (w i - qTern s (w i)) ^ 2 := by
    intro i
    by_cases h : ternInRange s (w i)
    · simp [h]
    · simp [h]
  have h2 : ∑ i, (w i - qTern s (w i)) ^ 2
      = ∑ i, (if ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
        + ∑ i, (if ¬ ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (h1 i).symm
  rw [h2, ← Finset.sum_filter, ← Finset.sum_filter]
  -- the saturated terms are exactly the overshoots (qTern_error_out)
  have hout : ∀ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)),
      (w i - qTern s (w i)) ^ 2 = (|w i| - s) ^ 2 := by
    intro i hi
    rw [← sq_abs (w i - qTern s (w i)),
      qTern_error_out s (w i) hs (Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hout]
  unfold satTail
  rfl

/-- The in-range part is at most `n_in · (s/2)²`: each
in-range coordinate contributes a half-step rounding square. -/
theorem ternary_inrange_bound (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
      ≤ (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2 := by
  have hsq : ∀ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
      (w i - qTern s (w i)) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i hi
    have hin : ternInRange s (w i) := (Finset.mem_filter.mp hi).2
    have hle := qTern_error_in s (w i) hs hin
    rw [abs_le] at hle
    nlinarith [hle.1, hle.2]
  calc ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
      ≤ ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (s / 2) ^ 2 := Finset.sum_le_sum hsq
    _ = (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_filter, nsmul_eq_mul]

/-- **The budget form of the split**: the total squared error of
the actual quantizer is at most `n·(s/2)² + satTail` — the
in-range rounding budget plus the EXPLICIT saturation tail
(in-range count bounded by the full `n`, so the bound is
computable without the split). -/
theorem ternary_split_le (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i, (w i - qTern s (w i)) ^ 2 ≤ (n : ℝ) * (s / 2) ^ 2 + satTail s w := by
  have hsplit := ternary_split_bound s hs w
  have hin := ternary_inrange_bound s hs w
  have hcard : (Finset.univ.filter (fun i => ternInRange s (w i))).card ≤ n := by
    calc (Finset.univ.filter (fun i => ternInRange s (w i))).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by simp
  have hcard' : ((Finset.univ.filter (fun i => ternInRange s (w i))).card : ℝ)
      ≤ (n : ℝ) := by exact_mod_cast hcard
  have hmul : (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2
      ≤ (n : ℝ) * (s / 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hcard' (sq_nonneg (s / 2))
  have hin' : ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2 ≤ (n : ℝ) * (s / 2) ^ 2 :=
    le_trans hin hmul
  linarith

/-- The saturation tail is nonnegative (a sum of squares). -/
theorem satTail_nonneg (s : ℝ) {n : ℕ} (w : Fin n → ℝ) :
    0 ≤ satTail s w := by
  unfold satTail
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Helper: `√` is subadditive on `ℝ≥0` (Mathlib's current
`Real.sqrt_add` family lacks the plain two-term form). -/
private theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have e1 := Real.sq_sqrt ha
    have e2 := Real.sq_sqrt hb
    nlinarith [h1]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = |Real.sqrt a + Real.sqrt b| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt a + Real.sqrt b :=
        abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! ## The honest global energy bridge -/

/-- **`quant_energy_bridge_saturation`** — the audit-§5 fix: the
global replacement for `QuantBridge.quant_energy_bridge`'s
hypothesis `∀ i, |w i − q i| ≤ s/2`, with NO assumption that the
coordinates are in range. The energy cost of quantizing `n`
weights with the ACTUAL saturating ternary quantizer at scale
`s`, under the measured κ-Lipschitz constant of the energy in
the weight Euclidean norm, is at most

  ΔE ≤ κ·(√n·s/2 + √(satTail s w))

— the old `κ√n·s/2` plus the honest, measurable saturation term
`√(Σ_out (|w i| − s)²)`, computable from a checkpoint as the sum
of squared overshoots. -/
theorem quant_energy_bridge_saturation {n : ℕ} (w : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 < s) (hkappa : 0 ≤ kappa)
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)) :
    dE ≤ kappa * (Real.sqrt (n : ℝ) * s / 2 + Real.sqrt (satTail s w)) := by
  have hle := ternary_split_le s hs w
  have hnn : 0 ≤ (n : ℝ) * (s / 2) ^ 2 := by positivity
  have htail := satTail_nonneg s w
  have h1 : Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)
      ≤ Real.sqrt ((n : ℝ) * (s / 2) ^ 2 + satTail s w) :=
    Real.sqrt_le_sqrt hle
  have h2 := sqrt_add_le ((n : ℝ) * (s / 2) ^ 2) (satTail s w) hnn htail
  have h3 : Real.sqrt ((n : ℝ) * (s / 2) ^ 2)
      = Real.sqrt (n : ℝ) * (s / 2) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < s / 2)]
  rw [h3] at h2
  have h4 : dE ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)
      + Real.sqrt (satTail s w)) :=
    le_trans h_emp_lip (mul_le_mul_of_nonneg_left (le_trans h1 h2) hkappa)
  linarith

/-! ## Recovery of the old bridge when nothing saturates -/

/-- **`no_saturation_recover`** — the audit's gap closes
exactly: if ALL coordinates are in range (`|w i| ≤ 3s/2`, i.e.
the saturation tail vanishes: no coordinate overshoots the
grid), the old R70 hypothesis `∀ i, |w i − q i| ≤ s/2` is
DERIVED (`qTern_error_in` holds for every `i` — not assumed),
and the old bridge's conclusion `ΔE ≤ κ·√n·s/2` follows from
the saturation bridge with `√satTail = 0`. The half-step
hypothesis of `Hagi.Energy.QuantBridge` is now a corollary of
the actual quantizer's geometry, not an external assumption. -/
theorem no_saturation_recover {n : ℕ} (w : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 < s) (hkappa : 0 ≤ kappa)
    (hall : ∀ i, ternInRange s (w i))
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)) :
    dE ≤ kappa * Real.sqrt (n : ℝ) * s / 2
      ∧ ∀ i, |w i - qTern s (w i)| ≤ s / 2 := by
  refine ⟨?_, fun i => qTern_error_in s (w i) hs (hall i)⟩
  -- the tail is empty: no coordinate is out of range
  have hempty : satTail s w = 0 := by
    unfold satTail
    rw [Finset.sum_eq_zero]
    intro i hi
    exact absurd (hall i) (Finset.mem_filter.mp hi).2
  have h0 : Real.sqrt (satTail s w) = 0 := by rw [hempty]; norm_num
  have hmain := quant_energy_bridge_saturation w s kappa dE hs hkappa h_emp_lip
  rw [h0] at hmain
  have heq : kappa * Real.sqrt (n : ℝ) * s / 2
      = kappa * (Real.sqrt (n : ℝ) * s / 2 + 0) := by ring
  rw [heq]
  exact hmain

end Hagi
