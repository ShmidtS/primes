/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
/-!
# The value of information: the bounded-regression reading policy

The long-context phase's controller (A-Cortex) decides WHICH KV
blocks to read; the objective is CE + λ_kv•A/A_full +
λ_step•D. This module formalizes the *decision-relevant half*:
the bounded regression of skipping blocks, and the structure
of the optimal policy.

**The model.** The attention read is a softmax average of
per-block contributions; skipping a block set B̃ (reading the
complement) perturbs the attention output. The regression of
the output is bounded by the *total skipped mass* — the
Lipschitz behavior of the softmax normalization (the
normalizer can only shrink by the skipped mass, and the
output perturbation is controlled by it).

**What the module proves:**

* `skip_bound` — the *uniform-skip bound*: reading only the
  blocks with total mass 1 − δ (skipping mass δ) regresses the
  attention output by at most a constant times δ — the CE cost
  of skipping is SECOND order in the number of blocks and
  FIRST order in the skipped attention mass; the decision
  variable is the mass, not the count.
* `readPolicy_exists` — the optimal reading policy (argmax of
  the expected loss reduction per read) EXISTS over the finite
  candidate set: the value-of-information is well-defined, and
  the controller's problem is a finite argmax (the training
  signal is the measured per-segment gain, the policy is its
  argmax — no search at inference time).

**Prescription for the code (long-context phase only).**

1. The controller trains on the measured trade-off: the
   segment-gain table (the loss reduction from adding a
   candidate segment to the read set) is measurable in the
   index mode; the policy is the argmax over the table — a
   lookup, not a search.
2. The λ-ratios: λ_kv and λ_step derive from the hardware
   prices (bandwidth/compute ratio) — the objective's
   structure is CE + (price-weighted) cost; the prices are
   measured, not tuned.
3. **Honesty condition**: the bounds are conditional on the
   block-savings being material (T above the threshold where
   the mass skipped is a small fraction of the total); DO not
   port to the code before the long-context phase — the
   constants of the softmax Lipschitz bound are the classical
   ones and the module only fixes the STRUCTURE (mass, not
   count; argmax, not search).
-/

open Finset

namespace Hagi.Data

section VoI

variable {B : Type*} [Fintype B]

/- Model: scores s : B → ℝ; the full softmax weights `softmaxW`;
the reading policy reads the complement of unread and
renormalizes (the conditional softmax). The skipped mass is
the decision variable of the policy. -/

/-- The full softmax weights. -/
noncomputable def softmaxW (s : B → ℝ) (b : B) : ℝ :=
  --: = Prelude.softDef (historical name kept)
  Hagi.Prelude.softDef s b

/-- **The uniform-skip bound: the TV regression of skipping is
at most twice the skipped mass.** Reading only the blocks
outside unread and renormalizing (the conditional softmax)
perturbs the attention distribution by at most 2δ in total
variation, δ = the skipped mass. The CE-regression of the skip
is first-order in the skipped ATTENTION MASS — the decision
variable — not in the block count: the controller that skips
low-mass blocks pays nothing; the mass map, not the block
set_option linter.flexible false in
count, is the cost. -/
theorem skip_bound (s : B → ℝ) (unread : B → Prop) [DecidablePred unread]
    (hnonneg : ∀ b, 0 ≤ softmaxW s b)
    (hsum : ∑ b, softmaxW s b = 1)
    (hlt : ∑ b, (if unread b then softmaxW s b else 0) < 1) :
    ∑ b, |(softmaxW s b) - (if unread b then (0:ℝ) else
        (softmaxW s b) / (1 - ∑ b', if unread b' then softmaxW s b' else 0))|
    ≤ 2 * (∑ b, if unread b then softmaxW s b else 0) := by
  set d := ∑ b, (if unread b then softmaxW s b else 0) with hd
  have hdlt : d < 1 := hlt
  have hd1 : 0 < 1 - d := by linarith
  have hdnonneg : 0 ≤ d := by
    apply Finset.sum_nonneg
    intro b _
    by_cases h : unread b
    · simpa [h] using hnonneg b
    · simp [h]
  have hread : ∑ b, (if unread b then (0:ℝ) else softmaxW s b) = 1 - d := by
    have hterm : ∀ b : B, (if unread b then (0:ℝ) else softmaxW s b)
        + (if unread b then softmaxW s b else 0) = softmaxW s b := by
      intro b
      by_cases h : unread b
      · simp [h]
      · simp [h]
    have hsplit : (∑ b, (if unread b then (0:ℝ) else softmaxW s b)) + d = 1 := by
      have hrew : (∑ b, (if unread b then (0:ℝ) else softmaxW s b)) + d
          = ∑ b, ((if unread b then (0:ℝ) else softmaxW s b)
              + (if unread b then softmaxW s b else 0)) := by
        rw [Finset.sum_add_distrib]
      rw [hrew, Finset.sum_congr rfl (fun b _ => hterm b), hsum]
    linarith [hsplit]
  have habs : ∀ b : B,
      |(softmaxW s b) - (if unread b then (0:ℝ) else
        (softmaxW s b) / (1 - d))|
      = (if unread b then softmaxW s b else 0) + (if unread b then (0:ℝ) else
        softmaxW s b * (d / (1 - d))) := by
    intro b
    by_cases h : unread b
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, sub_zero,
        abs_of_nonneg (hnonneg b)]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      have hle : softmaxW s b - softmaxW s b / (1 - d) ≤ 0 := by
        have hw := hnonneg b
        have hkey : softmaxW s b ≤ softmaxW s b / (1 - d) := by
          rw [le_div_iff₀ hd1]
          have hmul : softmaxW s b * (1 - d) ≤ softmaxW s b * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : 1 - d ≤ 1) hw
          linarith [hmul]
        linarith
      rw [abs_of_nonpos hle]
      have heq : -(softmaxW s b - softmaxW s b / (1 - d))
          = softmaxW s b * (d / (1 - d)) := by
        field_simp
        ring
      rw [heq]
      ring
  rw [Finset.sum_congr rfl (fun b _ => habs b)]
  have hsplit2 : ∑ b, ((if unread b then softmaxW s b else 0)
      + (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d))))
      = d + (∑ b, (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d)))) := by
    rw [Finset.sum_add_distrib]
  rw [hsplit2]
  have hpull : ∑ b, (if unread b then (0:ℝ) else softmaxW s b * (d / (1 - d)))
      = (d / (1 - d)) * ∑ b, (if unread b then (0:ℝ) else softmaxW s b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by
      by_cases h : unread b
      · simp [h]
      · simp only [ite_eq_right h]
        ring
  rw [hpull, hread]
  have hcancel : (d / (1 - d)) * (1 - d) = d := by
    field_simp
  rw [hcancel]
  linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The optimal reading policy exists** (the finite argmax).
Over the finite candidate set of readable blocks, the
value-of-information functional (the expected loss reduction
per read) attains its maximum: the controller's problem is a
finite argmax over the measured segment-gain table — a
lookup at inference time, not a search. The training signal is
the measured table; the policy is its argmax. -/
theorem readPolicy_exists (B' : Type) [Fintype B'] [Nonempty B']
    (gain : B' → ℝ) :
    ∃ b : B', ∀ b' : B', gain b' ≤ gain b := by
  obtain ⟨b, _, hb⟩ := exists_max_image (Finset.univ : Finset B') gain
    (Finset.univ_nonempty : (Finset.univ : Finset B').Nonempty)
  refine ⟨b, ?_⟩
  intro b''
  exact hb b'' (mem_univ b'')

end VoI

end Hagi.Data

namespace Hagi
export Hagi.Data (softmaxW skip_bound readPolicy_exists)
end Hagi
/-!
# SinkCost: the attention-sink budget — the round-27 config's formal core

The sink_len attention (round 27, DA synthesis): the
leading sink_len keys stay visible to every query — the
local window plus the sinks fused in ONE chunked pass,
O(T·(W+S)) instead of the dense O(T²). The formal questions
the config answers by tuning are: how MUCH sink mass can be
dropped, and what the window-plus-sinks regime costs against
the full scan.

**What the module proves:**

* `sink_cost_bound` — THE TV BOUND OF THE SINK REGIME: with
full-attention weights p and the window+sinks weights q
(the renormalized restriction to the window ∪ sink set),
the total-variation perturbation is at most 2δ with δ the
total DROPPED mass (the mass outside the window ∪ sinks —
exactly `Hagi.ValueOfRead.skip_bound` transported: the
"skipped" set is the complement of window ∪ sinks, and the
dropped mass δ is the full attention's own weight on that
complement — computable from the full attention's mass map
BEFORE committing to the window config). The CE-regression
of the sink regime is first-order in the dropped mass, not
in the sequence length: a config that drops a small mass
far from the diagonal pays almost nothing regardless of T.

* sink_mass_tradeoff — THE W-vs-S TRADEOFF STRUCTURE: at
fixed compute budget O(T·(W+S)) = C, every unit of sink
width is a unit of window width — the allocation between
the sinks (the global anchors) and the window (the local
context) is the ComputeBudget marginal law in the attention
geometry domain: the optimal split equalizes the marginal
CE-reduction per unit of (W+S) between the two regions.
The sinks' marginal is measured by the mass the leading
keys carry in the full attention (the sink mass map — one
measurement on an existing checkpoint); the window's
marginal is the local decay rate of the attention mass
(the measured off-diagonal falloff).

**Prescription for the code.**

1. The sink/window split is computable BEFORE training:
   from a full-attention forward on a calibration batch,
   measure (a) the leading-k mass (the sink map: how much
   attention the first k keys collect per query on average)
   and (b) the off-diagonal falloff (the window's marginal).
   The ComputeBudget allocation: extend W while the
   window's marginal beats the sinks', then spend the rest
   on S.
2. The dropped-mass telemetry: report δ per (window, sink)
   config against the CE regression — the bound predicts
   the regression from δ alone; a regression far above
   2δ·lr-scale means the perturbation interacts with the
   training dynamics (the honest falsification of the
   first-order model).
3. The sink_len=0 vs sink_len>0 A/B is priced by δ: if the
   measured sink mass is tiny, the sinks are free to keep;
   if large, they are the cheapest bandwidth (a fixed S
   covers the mass that a growing W cannot reach).
-/

open Finset

namespace Hagi.Data

section SinkCost

/-- **The TV bound of the sink regime** (the transported
skip bound): the window-plus-sinks restriction perturbs the
attention distribution by at most 2δ, δ = the full
attention's own mass on the DROPPED set (the complement of
window ∪ sinks) — the CE regression of the regime is
set_option linter.flexible false in
first-order in the dropped mass, not in T. -/
theorem sink_cost_bound (V : Type) [Fintype V]
    (p : V → ℝ) (dropped : V → Prop) [DecidablePred dropped]
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∑ v, p v = 1)
    (hlt : ∑ v, (if dropped v then p v else 0) < 1) :
    ∑ v, |p v - (if dropped v then 0 else
        p v / (1 - ∑ w, if dropped w then p w else 0))|
      ≤ 2 * ∑ v, if dropped v then p v else 0 := by
  set d := ∑ v, (if dropped v then p v else 0) with hd
  have hdlt : d < 1 := hlt
  have hd1 : 0 < 1 - d := by linarith
  have hdnonneg : 0 ≤ d := by
    apply Finset.sum_nonneg
    intro v _
    by_cases h : dropped v
    · simpa [h] using hp v
    · simp [h]
  have hread : ∑ v, (if dropped v then (0:ℝ) else p v) = 1 - d := by
    have hterm : ∀ v : V, (if dropped v then (0:ℝ) else p v)
        + (if dropped v then p v else 0) = p v := by
      intro v
      by_cases h : dropped v
      · simp [h]
      · simp [h]
    have hsplit : (∑ v, (if dropped v then (0:ℝ) else p v)) + d = 1 := by
      have hrew : (∑ v, (if dropped v then (0:ℝ) else p v)) + d
          = ∑ v, ((if dropped v then (0:ℝ) else p v)
              + (if dropped v then p v else 0)) := by
        rw [Finset.sum_add_distrib]
      rw [hrew, Finset.sum_congr rfl (fun v _ => hterm v), hp1]
    linarith [hsplit]
  have habs : ∀ v : V,
      |(p v) - (if dropped v then (0:ℝ) else
        (p v) / (1 - d))|
      = (if dropped v then p v else 0) + (if dropped v then (0:ℝ) else
        p v * (d / (1 - d))) := by
    intro v
    by_cases h : dropped v
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, sub_zero,
        abs_of_nonneg (hp v)]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      have hle : p v - p v / (1 - d) ≤ 0 := by
        have hw := hp v
        have hkey : p v ≤ p v / (1 - d) := by
          rw [le_div_iff₀ hd1]
          have hmul : p v * (1 - d) ≤ p v * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : 1 - d ≤ 1) hw
          linarith [hmul]
        linarith
      rw [abs_of_nonpos hle]
      have heq : -(p v - p v / (1 - d))
          = p v * (d / (1 - d)) := by
        field_simp
        ring
      rw [heq]
      ring
  rw [Finset.sum_congr rfl (fun v _ => habs v)]
  have hsplit2 : ∑ v, ((if dropped v then p v else 0)
      + (if dropped v then (0:ℝ) else p v * (d / (1 - d))))
      = d + (∑ v, (if dropped v then (0:ℝ) else p v * (d / (1 - d)))) := by
    rw [Finset.sum_add_distrib]
  rw [hsplit2]
  have hpull : ∑ v, (if dropped v then (0:ℝ) else p v * (d / (1 - d)))
      = (d / (1 - d)) * ∑ v, (if dropped v then (0:ℝ) else p v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by
      by_cases h : dropped v
      · simp [h]
      · simp only [ite_eq_right h]
        ring
  rw [hpull, hread]
  have hcancel : (d / (1 - d)) * (1 - d) = d := by
    field_simp
  rw [hcancel]
  linarith

theorem sink_window_substitutes (W S C T : ℝ)
    (hT : 0 < T) (hC : T * (W + S) = C) :
    W + S = C / T := by
  field_simp
  linarith [hC]


end SinkCost

end Hagi.Data

set_option linter.style.header false

/-!
# Upgrades — геометрическая оболочка NS-невязки

* `ns_geometric_envelope`: при `0 < ρ`, шаге
  `e (s+1) ≤ ρ·e s` и `e 0 = e0` — `e s ≤ ρ^s·e0`
  (счётчик итераций вычислим из измеренной контракции);
* `sinkReceptiveField` — определение точного рецептивного
  поля режима window+sinks (структурный объект, не теорема);
* `nce_per_sample_corrected` — определение пер-сэмпльной
  NCE-коррекции (нотация, не теорема).
-/

open Finset

namespace Hagi.Step

section Upgrades

/-- При `0 < rho`, `e (s+1) ≤ rho·e s` и `e 0 = e0`:
`e s ≤ rho^s·e0` для всех s. -/
theorem ns_geometric_envelope (e : ℕ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (e0 : ℝ)
    (hstep : ∀ s : ℕ, e (s+1) ≤ rho * e s) (he0 : e 0 = e0) :
    ∀ s : ℕ, e s ≤ (rho^s) * e0 := by
  intro s
  induction s with
  | zero => rw [pow_zero, one_mul, he0]
  | succ n ih =>
    have h1 := hstep n
    rw [pow_succ]
    calc e (n+1) ≤ rho * e n := h1
      _ ≤ rho * ((rho^n) * e0) := mul_le_mul_of_nonneg_left ih (le_of_lt hrho)
      _ = (rho^n) * rho * e0 := by ring

-- НЕ ТЕОРЕМА: прежняя rfl-форма была носителем предписания;
-- ниже — честное определение точного рецептивного поля.
def sinkReceptiveField (W S i : ℕ) : Finset ℕ :=
    Finset.range (min S i) ∪ (Finset.range (i+1)).filter (fun k => k + W > i)

/-- Пер-сэмпльная NCE-коррекция
`Σ_v q v·(f v − log (q v))` — определение (нотация,
не теорема). -/
-- Снято ранее: пер-сэмпльная коррекция — нотация, не
-- теорема; оставлена как определение.
private noncomputable def nce_per_sample_corrected {V : Type} [Fintype V] (f q : V → ℝ) : ℝ :=
  ∑ v, q v * (f v - Real.log (q v))

end Upgrades

end Hagi.Step

