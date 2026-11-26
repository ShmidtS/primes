/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.GPM
import Hagi.Spectral.RankGrowth
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Continual — the GPM continual-learning canon (→)

One line of development, one canonical module. Each concept is
described ONCE here; the four sections keep their historical
namespaces so every fully-qualified name is stable.

* Exact GPM zero forgetting: a step whose rows are orthogonal
  to every old-task input leaves the old-task bench loss
  EXACTLY invariant — the projector mathematics lives in
  `Hagi.Step.GPM` (`gpm_zero_forgetting`); here only the
  per-point-to-sum bench glue and the naive-step negative.
* Multi-task accumulation (3+ tasks): chaining the exact
  invariance phase by phase gives zero forgetting on EVERY
  past task; the rank track cites
  `Hagi.Spectral.rank_orthogonal_growth`.
* Relaxed projection (the honest trade-off): on an ABSTRACT
  projection `P` (no spectral construction enters any proof),
  rank-truncated GPM bounds forgetting by the tail energy
  leakage `sigmaTail P x = ‖x − P·x‖`; `P = 1` recovers exact
  zero forgetting, `P = 0` is unbounded. A-GEM conditional
  projection on gradient conflict. The trade-off theorem:
  forgetting AND progress are controlled by the SAME tail.
* Hybrid mechanism selection: a deterministic case-on-state
  selector (span fullness, conflict sign) whose soundness is
  the disjunction of the three mechanism guarantees.

Limits (bench-side, not theorems): `P` is built by exact
rational Gram–Schmidt (`Q = I − Σ u uᵀ/(u·u)`); SVD is never
constructed (irrational in general); the tail budget is
compared in SQUARES (`sigmaTail²` is a sum of squares of
rationals — exact Fraction arithmetic); the truncation-rank
rule is minimal `k` with `max_old sigmaTail² ≤ ε²`.

Layer decision: Theory (7) — consumes `Hagi.Step.GPM` (layer 5)
and cites `Hagi.Spectral.RankGrowth`; the bench modes
`continual` / `gpm2` / `hybrid-continual` of
`scripts/bench_bridge.py` consume this module.
-/

/-! ## Exact GPM bench bridge — `Hagi.Theory.ContinualBench` -/

open scoped Matrix

namespace Hagi.Theory.ContinualBench

variable {n K : ℕ}

/-- The continual bench loss on one task: sum of squared errors
of the scalar linear head `W` over the task inputs `xs` and
targets `ys` (the bench uses the mean; the sum scales by a
positive constant and the invariance statement is identical). -/
def gpmBenchLoss (W : Matrix (Fin 1) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (ys : Fin K → ℝ) : ℝ :=
  ∑ k, ((W *ᵥ xs k) 0 - ys k) ^ 2

/-- **gpm_bench_bridge**: a GPM step (each row of `ΔW`
orthogonal to every task-A input, `gpmOrth`) leaves the bench
loss on task A EXACTLY invariant — `gpm_zero_forgetting` applied
per point of the bench structure. This is the machine-checked
statement behind the bench telemetry line `loss_A before/after
GPM phase` being equal Fractions. -/
theorem gpm_bench_bridge (W ΔW : Matrix (Fin 1) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (ys : Fin K → ℝ)
    (horth : Hagi.Step.gpmOrth ΔW xs) :
    gpmBenchLoss (W + ΔW) xs ys = gpmBenchLoss W xs ys := by
  unfold gpmBenchLoss
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hagi.Step.gpm_zero_forgetting W ΔW xs horth k]

/-- **naive_step_can_forget**: the mini-negative — without
the GPM orthogonality the task-A output is NOT preserved: an
explicit `W`, `ΔW` and task-A input where `gpmOrth` fails and the
head output on the old input moves (`1 ≠ 0`, machine-checked).
The naive bench path has no preservation guarantee; its actual
forgetting is measured, not certified away. -/
theorem naive_step_can_forget :
    ∃ (W ΔW : Matrix (Fin 1) (Fin 2) ℝ)
      (xs : Fin 1 → (Fin 2 → ℝ)),
      ¬ Hagi.Step.gpmOrth ΔW xs
        ∧ (W + ΔW) *ᵥ xs 0 ≠ W *ᵥ xs 0 := by
  refine ⟨Matrix.of (fun _ _ => (0 : ℝ)),
    Matrix.of fun _ j => if j = 0 then 1 else 0,
    fun _ j => if j = 0 then 1 else 0, ?_, ?_⟩
  · intro h
    have h0 := h 0 0
    norm_num [dotProduct, Matrix.of_apply] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [Matrix.add_mulVec, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Fin.sum_univ_two, Pi.add_apply,
      Matrix.zero_apply, Pi.zero_apply] at h0

end Hagi.Theory.ContinualBench

/-! ## Multi-task accumulation — `Hagi.Theory.ContinualMulti`

Zero forgetting across the whole task sequence, chained from the
 bridge; rank track via `Hagi.Spectral.rank_orthogonal_growth`. -/

open scoped Matrix

namespace Hagi.Theory.ContinualMulti

variable {n K : ℕ}

/-- **gpm_multi_step_invariant**: if the step `dW t` of
phase `t+1` is GPM-orthogonal to every input of every task `s ≤ t`
(orthogonality to the ACCUMULATED span of tasks `1..t`), then the
bench loss on each past task is exactly invariant under the step. -/
theorem gpm_multi_step_invariant
    (dW : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (xs : ℕ → Fin K → (Fin n → ℝ))
    (ys : ℕ → Fin K → ℝ)
    (W : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (hchain : ∀ t, W (t+1) = W t + dW t)
    (horth : ∀ t s, s ≤ t → Hagi.Step.gpmOrth (dW t) (xs s)) :
    ∀ t s, s ≤ t →
      Hagi.Theory.ContinualBench.gpmBenchLoss (W (t+1)) (xs s) (ys s)
        = Hagi.Theory.ContinualBench.gpmBenchLoss (W t) (xs s) (ys s) := by
  intro t s hs
  rw [hchain t]
  exact Hagi.Theory.ContinualBench.gpm_bench_bridge (W t) (dW t)
    (xs s) (ys s) (horth t s hs)

/-- **gpm_multi_zero_forgetting (main)**: with each phase
step orthogonal to all inputs of all past tasks (GPM on the
accumulated subspace), the bench loss of task `s` at ANY later
phase end `t ≥ s+1` equals its value right after phase `s` —
zero forgetting across the whole multi-task sequence, chained
from `gpm_zero_forgetting` step by step (induction on `t`).
Rank track: the accumulated Gram-Schmidt basis grows per task by
its number of linearly independent new directions —
`Hagi.Spectral.rank_orthogonal_growth` (k new orthogonal
independent rows ⇒ rank grows by exactly k). -/
theorem gpm_multi_zero_forgetting
    (dW : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (xs : ℕ → Fin K → (Fin n → ℝ))
    (ys : ℕ → Fin K → ℝ)
    (W : ℕ → Matrix (Fin 1) (Fin n) ℝ)
    (hchain : ∀ t, W (t+1) = W t + dW t)
    (horth : ∀ t s, s ≤ t → Hagi.Step.gpmOrth (dW t) (xs s)) :
    ∀ t s, s < t →
      Hagi.Theory.ContinualBench.gpmBenchLoss (W t) (xs s) (ys s)
        = Hagi.Theory.ContinualBench.gpmBenchLoss (W (s+1)) (xs s)
            (ys s) := by
  intro t
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
      intro s hs
      by_cases h : s = t
      · subst h; rfl
      · have hst : s ≤ t := by omega
        rw [hchain t]
        rw [Hagi.Theory.ContinualBench.gpm_bench_bridge (W t) (dW t)
          (xs s) (ys s) (horth t s hst)]
        exact ih s (by omega)

end Hagi.Theory.ContinualMulti

/-! ## Relaxed projection: rank-trunc / A-Gem trade-off — `Hagi.Theory.GPMRelaxed`

See the module header for the canon; the exact-GPM degenerate case
and the all-HOLD phenomenon are the two faces of the tail. -/

open scoped Matrix

namespace Hagi.Theory.GPMRelaxed

variable {m n K : ℕ}

/-- Euclidean norm on `Fin n → ℝ` via `dotProduct`
(noncomputable: `Real.sqrt`; the bench compares SQUARES,
which are rational). -/
noncomputable def nrm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- Tail energy leakage of projection `P` on input `x`:
`sigmaTail P x = ‖x − P·x‖`. At `P = 1` it is zero (exact
GPM); at `P = 0` it is `‖x‖` (no projection). -/
noncomputable def sigmaTail {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ := nrm (x - P *ᵥ x)

/-- Relaxed GPM orthogonality: each row of the step `ΔW` is
orthogonal to the PROJECTED old inputs `P *ᵥ xs k` (top-k
subspace version of `Hagi.Step.gpmOrth`). -/
def gpmOrthP (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ) :
    Prop := ∀ i k, ΔW i ⬝ᵥ (P *ᵥ xs k) = 0

/-- Cauchy–Schwarz for `dotProduct` (corpus pattern,
`Hagi/Step/Joint.lean`). -/
theorem cs_abs {n : ℕ} (v w : Fin n → ℝ) :
    |v ⬝ᵥ w| ≤ nrm v * nrm w := by
  have hcauchy : (v ⬝ᵥ w)^2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
    have hconv : (∑ i, v i ^ 2) = ∑ i, v i * v i :=
      Finset.sum_congr rfl fun i _ => pow_two (v i)
    have hconv2 : (∑ i, w i ^ 2) = ∑ i, w i * w i :=
      Finset.sum_congr rfl fun i _ => pow_two (w i)
    rw [hconv, hconv2] at h
    exact h
  have hsq : |v ⬝ᵥ w| * |v ⬝ᵥ w| ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
    rw [abs_mul_abs_self (v ⬝ᵥ w), ← pow_two (v ⬝ᵥ w)]
    exact hcauchy
  have h4 : Real.sqrt (|v ⬝ᵥ w| * |v ⬝ᵥ w|)
      ≤ Real.sqrt ((v ⬝ᵥ v) * (w ⬝ᵥ w)) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul_self (abs_nonneg (v ⬝ᵥ w))] at h4
  rw [Real.sqrt_mul (by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)] at h4
  exact h4

/-- Pure linear algebra: any residual `r ⬝ᵥ x` equals the dot
product with the tail `x − P·x` up to the projected part. No
projection property of `P` is used. -/
theorem dot_split {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (r x : Fin n → ℝ) :
    r ⬝ᵥ x = r ⬝ᵥ (P *ᵥ x) + r ⬝ᵥ (x - P *ᵥ x) := by
  rw [dotProduct_sub]
  ring

/-- **rank_trunc_forgetting_bound**: a rank-truncated
GPM step (rows orthogonal to the projected old inputs,
`gpmOrthP`) changes the response on old input `xs k` by at
most `‖row‖ · sigmaTail` — the forgetting budget is the tail
energy leakage, NOT zero (honest trade-off: at `P = 1` the
tail vanishes and so does forgetting). -/
theorem rank_trunc_forgetting_bound
    (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (horth : gpmOrthP ΔW xs P) (i : Fin m) (k : Fin K) :
    |ΔW i ⬝ᵥ xs k| ≤ nrm (ΔW i) * sigmaTail P (xs k) := by
  have hsplit : ΔW i ⬝ᵥ xs k = ΔW i ⬝ᵥ (xs k - P *ᵥ xs k) := by
    have h := dot_split P (ΔW i) (xs k)
    rw [horth i k, zero_add] at h
    exact h
  rw [hsplit]
  exact cs_abs _ _

/-- **rank_trunc_output_bound**: the per-row output
change on an old input under a rank-truncated GPM step is
bounded by `‖row‖ · sigmaTail` (the matrix form of
`rank_trunc_forgetting_bound`; via `mulVec_eq_dotProduct`). -/
theorem rank_trunc_output_bound
    (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (horth : gpmOrthP ΔW xs P) (i : Fin m) (k : Fin K) :
    |((W + ΔW) *ᵥ xs k) i - (W *ᵥ xs k) i|
      ≤ nrm (ΔW i) * sigmaTail P (xs k) := by
  have hsplit : ((W + ΔW) *ᵥ xs k) i - (W *ᵥ xs k) i
      = ΔW i ⬝ᵥ xs k := by
    rw [Matrix.add_mulVec, Pi.add_apply, Hagi.Step.mulVec_eq_dotProduct,
      Hagi.Step.mulVec_eq_dotProduct]
    ring
  rw [hsplit]
  exact rank_trunc_forgetting_bound ΔW xs P horth i k

/-- **sigmaTail_one_zero**: at the full projection
`P = 1` the tail energy leakage is exactly zero. -/
theorem sigmaTail_one_zero {n : ℕ} (x : Fin n → ℝ) :
    sigmaTail (1 : Matrix (Fin n) (Fin n) ℝ) x = 0 := by
  unfold sigmaTail nrm
  rw [Matrix.one_mulVec, sub_self]
  simp

/-- **gpm_full_zero**: at the full projection `P = 1`
the relaxed condition `gpmOrthP` degenerates to exact
`gpmOrth`, so the instance `k = full` of the truncation family
recovers the exact zero-forgetting theory
(`Hagi.Step.gpm_zero_forgetting`). Generalization is strict:
`rank_trunc_forgetting_bound` at `P = 1` gives a zero bound
via `sigmaTail_one_zero`. -/
theorem gpm_full_zero (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (horth : gpmOrthP ΔW xs (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Hagi.Step.gpmOrth ΔW xs := by
  intro i k
  have h := horth i k
  rwa [Matrix.one_mulVec] at h

/-- **rank_zero_unbounded**: the k = 0 negative —
WITHOUT projection (P = 0) forgetting is unbounded: for every
budget `C > 0` there is an old input and a unit-norm step row
achieving response change exactly `C`. The qualitative
negative `naive_step_can_forget` is the special case `C = 1`;
here the magnitude is arbitrary (unit step, scaled input). -/
theorem rank_zero_unbounded (C : ℝ) (hC : 0 < C) :
    ∃ (xs : Fin 1 → (Fin 2 → ℝ)) (ΔW : Matrix (Fin 1) (Fin 2) ℝ),
      gpmOrthP ΔW xs (0 : Matrix (Fin 2) (Fin 2) ℝ)
        ∧ |ΔW 0 ⬝ᵥ xs 0| = C ∧ nrm (ΔW 0) = 1 := by
  refine ⟨fun _ j => if j = 0 then C else 0,
    Matrix.of fun _ j => if j = 0 then 1 else 0, ?_, ?_, ?_⟩
  · intro i k
    rw [Matrix.zero_mulVec]
    simp [dotProduct]
  · norm_num [dotProduct, Matrix.of_apply, Fin.sum_univ_two]
    linarith
  · simp [nrm, dotProduct, Matrix.of_apply, Real.sqrt_one]

/-- **agemStep (def)**: the A-GEM conditional projection —
the step is FREE when the current gradient does not conflict
with the old gradient (`0 ≤ g ⬝ᵥ g_old`; first-order old-loss
change `−η·⟨g, g_old⟩ ≤ 0`), and is orthogonalized onto
`g_old^⊥` (one Gram–Schmidt iteration) on conflict. -/
noncomputable def agemStep {n : ℕ} (g g_old : Fin n → ℝ) : Fin n → ℝ :=
  if 0 ≤ g ⬝ᵥ g_old then g
  else g - (g ⬝ᵥ g_old / (g_old ⬝ᵥ g_old)) • g_old

/-- **agem_step_nonneg_interf**: the applied A-GEM rule
ALWAYS has non-negative first-order old-interference: in the
free branch by hypothesis, in the conflict branch exactly zero
(orthogonalized). Together with the free-branch reading this
is the conditional-projection guarantee: interference is never
positive first order. -/
theorem agem_step_nonneg_interf {n : ℕ} (g g_old : Fin n → ℝ)
    (hne : g_old ⬝ᵥ g_old ≠ 0) :
    0 ≤ agemStep g g_old ⬝ᵥ g_old := by
  unfold agemStep
  split
  · assumption
  · rename_i hneg
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    linarith

/-- **gpm_tradeoff**: the honest trade-off — under ONE
relaxed-orthogonality hypothesis (rows orthogonal to the
projected old inputs, and to the projected new input), BOTH
sides of the continual compromise are controlled by the SAME
tail mechanism: forgetting on each old input AND progress on
the new input are each at most `‖row‖ · sigmaTail` on the
respective input. Shrinking the tail (larger truncation rank)
shrinks forgetting but equally shrinks admissible progress;
the ε² compromise is exact, not asymptotic. -/
theorem gpm_tradeoff (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (x_new : Fin n → ℝ) (i : Fin m)
    (horth : gpmOrthP ΔW xs P)
    (hnew : ΔW i ⬝ᵥ (P *ᵥ x_new) = 0) :
    (∀ k : Fin K, |ΔW i ⬝ᵥ xs k| ≤ nrm (ΔW i) * sigmaTail P (xs k))
      ∧ |ΔW i ⬝ᵥ x_new| ≤ nrm (ΔW i) * sigmaTail P x_new := by
  constructor
  · intro k
    exact rank_trunc_forgetting_bound ΔW xs P horth i k
  · have hsplit : ΔW i ⬝ᵥ x_new = ΔW i ⬝ᵥ (x_new - P *ᵥ x_new) := by
      have h := dot_split P (ΔW i) x_new
      rw [hnew, zero_add] at h
      exact h
    rw [hsplit]
    exact cs_abs _ _

/-- **gpm_hold_when_covered**: the machine-checked form
of the all-HOLD phenomenon — when the projection covers
the new input (`sigmaTail P x_new = 0`, span reached the new
directions), EVERY admissible step has exactly zero progress
on it: no step is both admissible and useful, so the method
HOLDs. Zero forgetting at full coverage and zero progress at
new-input coverage are the two faces of the same tail. -/
theorem gpm_hold_when_covered (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) (P : Matrix (Fin n) (Fin n) ℝ)
    (x_new : Fin n → ℝ) (i : Fin m)
    (horth : gpmOrthP ΔW xs P)
    (hnew : ΔW i ⬝ᵥ (P *ᵥ x_new) = 0)
    (hcover : sigmaTail P x_new = 0) :
    ΔW i ⬝ᵥ x_new = 0 := by
  have hbound := (gpm_tradeoff ΔW xs P x_new i horth hnew).2
  rw [hcover, mul_zero] at hbound
  exact le_antisymm (abs_le.mp hbound).2 (abs_le.mp hbound).1

end Hagi.Theory.GPMRelaxed

/-! ## Hybrid mechanism selection — `Hagi.Theory.HybridContinual`

Deterministic selection over the three mechanisms (full-GPM /
A-GEM free / rank-trunc); each branch keeps THAT mechanism's
guarantee — see the section above. -/

namespace Hagi.Theory.HybridContinual

open scoped Matrix
open Hagi.Theory.GPMRelaxed

/-- The three continual mechanisms of the decision table:
full-GPM (exact projection, zero forgetting), A-GEM free step
(no conflict), rank-trunc relaxed GPM (per-point forgetting
bound). -/
inductive HybridMech : Type
  | fullGPM | agemFree | rankTrunc

/-- **hybridSelect (def)**: the deterministic per-step
mechanism selector on the two MEASURED predicates
decision table — span fullness (`spanFree = rank(span A ∪ B) <
dim`, an exact rational Gram-Schmidt fact) and the conflict sign
`⟨g, g_old⟩`. No randomness, no thresholds beyond the measured
numbers themselves. -/
noncomputable def hybridSelect {n : ℕ} (spanFree : Bool)
    (g g_old : Fin n → ℝ) : HybridMech :=
  if spanFree then HybridMech.fullGPM
  else if 0 ≤ g ⬝ᵥ g_old then HybridMech.agemFree
  else HybridMech.rankTrunc

/-- **hybridStep (def)**: the step direction of each
mechanism. `P` is the orthogonal projector onto the relevant old
subspace (full span of the old task for full-GPM, the kept
top-k directions for rank-trunc); the free A-GEM branch takes
the raw gradient. -/
noncomputable def hybridStep {n : ℕ} (m : HybridMech)
    (g _g_old : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → ℝ :=
  match m with
  | HybridMech.fullGPM => g - P *ᵥ g
  | HybridMech.agemFree => g
  | HybridMech.rankTrunc => g - P *ᵥ g

/-- **proj_compl_orth**: for an orthogonal projector
(`P² = P`, `Pᵀ = P`) the complement-projected direction is
exactly orthogonal to the projected subspace. This single
computation powers both the full-GPM branch (exact zero
interference with every old input in the span) and the
`gpmOrthP` hypothesis of the rank-trunc branch. -/
theorem proj_compl_orth {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hPs : Pᵀ = P) (g v : Fin n → ℝ) :
    (g - P *ᵥ g) ⬝ᵥ (P *ᵥ v) = 0 := by
  have hgl : (g - P *ᵥ g) ⬝ᵥ (P *ᵥ v)
      = g ⬝ᵥ (P *ᵥ v) - (P *ᵥ g) ⬝ᵥ (P *ᵥ v) := by
    rw [sub_dotProduct]
  have hR : (P *ᵥ g) ⬝ᵥ (P *ᵥ v) = g ⬝ᵥ (P *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose,
        Matrix.mulVec_mulVec, hPs, hP]
  rw [hgl, hR, sub_self]

/-- **hybrid_step_sound (main)**: selecting the continual
mechanism by the measured per-step state preserves the guarantee
of the SELECTED branch — a disjunction of the three
mechanisms with no weakening. In the full-GPM branch the step is
exactly orthogonal to every old input of the projected span
(zero forgetting, the `gpm_zero_forgetting` face); in the free
A-GEM branch the first-order old-interference is non-negative
(the free case of `agem_step_nonneg_interf`); in the rank-trunc
branch the per-point forgetting bound of
`rank_trunc_forgetting_bound` holds (instantiated by the one-row
step matrix, whose `gpmOrthP` hypothesis is `proj_compl_orth`).
The proof is pure case-on-state. -/
theorem hybrid_step_sound {n : ℕ} (g g_old : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hPs : Pᵀ = P) (spanFree : Bool) :
    match hybridSelect spanFree g g_old with
    | HybridMech.fullGPM =>
        ∀ x : Fin n → ℝ, x = P *ᵥ x →
          hybridStep HybridMech.fullGPM g g_old P ⬝ᵥ x = 0
    | HybridMech.agemFree =>
        0 ≤ hybridStep HybridMech.agemFree g g_old P ⬝ᵥ g_old
    | HybridMech.rankTrunc =>
        ∀ x : Fin n → ℝ,
          |hybridStep HybridMech.rankTrunc g g_old P ⬝ᵥ x|
            ≤ nrm (g - P *ᵥ g) * sigmaTail P x := by
  unfold hybridSelect
  cases spanFree with
  | true =>
    simp only [ite_true]
    intro x hx
    show (g - P *ᵥ g) ⬝ᵥ x = 0
    rw [hx]
    exact proj_compl_orth P hP hPs g x
  | false =>
    by_cases hdot : 0 ≤ g ⬝ᵥ g_old
    · simp only [ite_eq_left hdot]
      exact hdot
    · simp only [ite_eq_right hdot]
      intro x
      have horth : (g - P *ᵥ g) ⬝ᵥ (P *ᵥ x) = 0 :=
        proj_compl_orth P hP hPs g x
      have hgpmOrthP : gpmOrthP
          (Matrix.of fun _ : Fin 1 => (g - P *ᵥ g) :
             Matrix (Fin 1) (Fin n) ℝ)
          (fun _ : Fin 1 => x) P := by
        intro i k
        exact horth
      have hbound := rank_trunc_forgetting_bound
        (Matrix.of fun _ : Fin 1 => (g - P *ᵥ g) :
           Matrix (Fin 1) (Fin n) ℝ) (fun _ : Fin 1 => x) P
        hgpmOrthP 0 0
      show |hybridStep HybridMech.rankTrunc g g_old P ⬝ᵥ x|
          ≤ nrm (g - P *ᵥ g) * sigmaTail P x
      simpa [hybridStep, Matrix.of_apply, dotProduct, nrm] using hbound

end Hagi.Theory.HybridContinual
