/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Hagi.Core.Concat
import Hagi.Energy.PairwiseCategorical
import Hagi.Optimization.InexactContraction
import Hagi.Energy.SingleCellDescent
import Mathlib.Tactic
import Hagi.Runtime.BF16Delta
import Hagi.Probability.MirrorHedgeMWU
import Hagi.Cert.Core
import Hagi.Cert.StepGen
import Hagi.Probability.Concentration
import Hagi.Model.CEGradient
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Model.EnergyReasoning.Pseudolikelihood.LocalField

set_option linter.style.header false
/-!
# Doeblin mixing bound for the heat-bath kernel

Track A8 (E-track audit, addendum A11 context): the Doeblin contraction
route — re-derived in main from first principles (the quarantined
`Hagi.Research.PPT` module carries the same math for a toy `Seq`
carrier behind the quarantine boundary; it is NOT imported here).

* `doeblinMinorized` — the Doeblin minorization predicate: `0 < c` and
  every kernel entry `≥ c`.
* `vecMul` / `hbChain` — one-step pushforward and the n-step chain of a
  finite kernel.
* `tv_pair_contraction` — (A8 MAIN, first principles) any two mass
  vectors of EQUAL total mass contract under a row-stochastic kernel
  with entry floor `c`: `TV(μK, νK) ≤ (1 − |S|·c)·TV(μ, ν)`. Elementary
  splitting of the signed difference `μ − ν` into positive/negative
  parts; the pair form needs NO stationarity (stationarity enters only
  through the corollaries `tv_contraction_stationary_sharp` /
  `tv_contraction_stationary` — the audit-text `(1 − c)` weak form).
* `heatbathWeight_floor` — field-spread premise: if all local-field
  differences at a cell are within `M`, then every heat-bath weight is
  `≥ exp(−M/T)/card α` (each softmax exponent is within `M/T` of the
  best one).
* `heatbath_doeblin_floor` — (A8 MAIN, premise-form) under the
  field-spread bound and the SUPPORT premise (every target `z` is a
  single-cell move — unconditionally true when `ι` is a subsingleton,
  see `heatbath_doeblin_floor_subsingleton`), the heat-bath kernel is
  `doeblinMinorized` with `c = exp(−M/T)/card α`.
* `stationaryDensity` — the normalized Boltzmann density; stationary
  for the heat-bath kernel (from `heatbath_stationary` by linearity).
* `heatbath_tv_contraction` — (A8 MAIN) Doeblin premise on the
  heat-bath kernel ⇒ `TV(μK, π̂) ≤ (1 − c)·TV(μ, π̂)` (sharp constant
  `(1 − |ι→α|·c)` in `heatbath_tv_contraction_sharp`).
* `heatbath_mixing` / `heatbath_mixing_time` — (A8 MAIN) geometric
  mixing `TV(μKⁿ, π̂) ≤ (1 − c)ⁿ`, and the explicit mixing-time
  corollary: `n ≥ log e / log(1 − c)` steps suffice for `TV ≤ e`.

## Honest boundaries (A8 scope)

* The entrywise floor is a PREMISE for the unconditional single-cell
  kernel: for `card ι ≥ 2` the off-support entries are exactly ZERO,
  so the Doeblin premise FAILS unless supplied by the consumer (e.g. a
  scan mixture, or `card ι ≤ 1`). The floor premise subsumes
  irreducibility and aperiodicity — those are NOT claimed for the
  unconditional kernel (names `heatbath_irreducible` /
  `heatbath_aperiodic` are RootApi negative pins).
* The focused (state-dependent) mixture is OUT of scope: C268 showed
  the INVARIANCE premise can fail; only the plain single-cell
  heat-bath kernel is treated.
* No spectral-gap or cutoff claim; only the Doeblin geometric rate.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy Hagi.Prelude

section Generic

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Doeblin minorization: strictly positive floor `c` under EVERY
kernel entry (row-stochasticity is carried separately by the theorems
that consume this predicate). -/
def doeblinMinorized (K : S → S → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ x y, c ≤ K x y

/-- One kernel step applied to a mass vector: `(μK)(y) = Σ_x μ(x)·K(x,y)`. -/
noncomputable def vecMul (mu : S → ℝ) (K : S → S → ℝ) : S → ℝ :=
  fun y => ∑ x, mu x * K x y

/-- The n-step chain `μKⁿ`, by iterating the one-step pushforward. -/
noncomputable def hbChain (mu : S → ℝ) (K : S → S → ℝ) : ℕ → S → ℝ
  | 0 => mu
  | n + 1 => vecMul (hbChain mu K n) K

omit [Nonempty S] in
/-- Total variation is nonnegative (half of a sum of absolute values;
  the division constant is positive). -/
theorem tvDef_nonneg (mu nu : S → ℝ) : 0 ≤ Hagi.Prelude.tvDef mu nu := by
  unfold Hagi.Prelude.tvDef
  exact div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) (by norm_num)

omit [Nonempty S] in
/-- The pushforward preserves the total mass under row-stochastic
  kernels. -/
theorem vecMul_sum (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (mu : S → ℝ) : ∑ y, vecMul mu K y = ∑ x, mu x := by
  calc ∑ y, vecMul mu K y = ∑ y, ∑ x, mu x * K x y := Finset.sum_congr rfl fun y _ => rfl
    _ = ∑ x, ∑ y, mu x * K x y := Finset.sum_comm
    _ = ∑ x, mu x * ∑ y, K x y := by
        refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum Finset.univ (fun y => K x y) (mu x)).symm
    _ = ∑ x, mu x * 1 := Finset.sum_congr rfl fun x _ => by rw [hrow x]
    _ = ∑ x, mu x := Finset.sum_congr rfl fun x _ => mul_one _

omit [Nonempty S] in
/-- The pushforward of a nonnegative vector is nonnegative under a
  nonnegative kernel. -/
theorem vecMul_nonneg (K : S → S → ℝ) (hnn : ∀ x y, 0 ≤ K x y)
    (mu : S → ℝ) (hmunn : ∀ x, 0 ≤ mu x) (y : S) :
    0 ≤ vecMul mu K y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hmunn x) (hnn x y)

omit [Nonempty S] in
/-- Chain step equation (`hbChain` on `n + 1` pushes the n-th iterate
  through the kernel). -/
theorem hbChain_succ (mu : S → ℝ) (K : S → S → ℝ) (n : ℕ) :
    hbChain mu K (n + 1) = vecMul (hbChain mu K n) K := rfl

omit [Nonempty S] in
/-- The chain preserves unit mass under a row-stochastic kernel. -/
theorem hbChain_sum (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (mu : S → ℝ) (hmass : ∑ x, mu x = 1) (n : ℕ) :
    ∑ y, hbChain mu K n y = 1 := by
  induction n with
  | zero => exact hmass
  | succ n ih =>
      rw [hbChain_succ, vecMul_sum K hrow, ih]

omit [Nonempty S] in
/-- The chain preserves nonnegativity under a nonnegative kernel. -/
theorem hbChain_nonneg (K : S → S → ℝ) (hnn : ∀ x y, 0 ≤ K x y)
    (mu : S → ℝ) (hmunn : ∀ x, 0 ≤ mu x) (n : ℕ) (y : S) :
    0 ≤ hbChain mu K n y := by
  have key : ∀ (n : ℕ) (y : S), 0 ≤ hbChain mu K n y := by
    intro n
    induction n with
    | zero => intro y; exact hmunn y
    | succ n ih =>
        intro y
        rw [hbChain_succ]
        exact vecMul_nonneg K hnn _ ih y
  exact key n y

/-- (A8 MAIN, first principles) One-step Doeblin PAIR contraction: for
any row-stochastic kernel with entry floor `c` and any two mass
vectors of EQUAL total mass, `TV(μK, νK) ≤ (1 − |S|·c)·TV(μ, ν)`.
Elementary proof: split the signed difference `μ − ν` into its
positive part (on `A`) and negative part (on `B`); each pushed through
the kernel stays `≥ c·δ` pointwise (`δ = Σ_A (μ − ν)` is the TV
value); the identity `|P − Q| = P + Q − 2·min(P, Q)` then shrinks the
total mass `2δ` by `2·|S|·c·δ`. No stationarity and no nonnegativity
of `μ`, `ν` is needed — only equal total mass. The constant
`1 − |S|·c` is sharp; the audit-text `1 − c` is the weak corollary
below. -/
theorem tv_pair_contraction (K : S → S → ℝ) (hrow : ∀ x, ∑ y, K x y = 1)
    (c : ℝ) (hc : ∀ x y, c ≤ K x y) (mu nu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, nu x) :
    Hagi.Prelude.tvDef (vecMul mu K) (vecMul nu K)
      ≤ (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu nu := by
  classical
  set A : Finset S := Finset.univ.filter (fun x => 0 ≤ mu x - nu x) with hAdef
  set B : Finset S := Finset.univ.filter (fun x => ¬ 0 ≤ mu x - nu x) with hBdef
  have hAnn : ∀ x ∈ A, 0 ≤ mu x - nu x := by
    intro x hx
    rw [hAdef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hBnn : ∀ x ∈ B, mu x - nu x ≤ 0 := by
    intro x hx
    rw [hBdef] at hx
    exact (not_le.mp (Finset.mem_filter.mp hx).2).le
  have hAB : (∑ x ∈ A, (mu x - nu x)) + (∑ x ∈ B, (mu x - nu x))
      = ∑ x : S, (mu x - nu x) := by
    rw [hAdef, hBdef]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x => 0 ≤ mu x - nu x) (fun x => mu x - nu x)
  have hdsum : ∑ x : S, (mu x - nu x) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  set delta : ℝ := ∑ x ∈ A, (mu x - nu x) with hdeltadef
  have hBdelta : ∑ x ∈ B, (mu x - nu x) = -delta := by linarith
  have hdeltann : 0 ≤ delta := Finset.sum_nonneg fun x hx => hAnn x hx
  set P : S → ℝ := fun y => ∑ x ∈ A, (mu x - nu x) * K x y with hPdef
  set Q : S → ℝ := fun y => -∑ x ∈ B, (mu x - nu x) * K x y with hQdef
  have hPy : ∀ y, P y = ∑ x ∈ A, (mu x - nu x) * K x y := fun _ => rfl
  have hQy : ∀ y, Q y = -∑ x ∈ B, (mu x - nu x) * K x y := fun _ => rfl
  -- the pushed-through signed difference (pair form: no stationarity)
  have hdiff : ∀ y, vecMul mu K y - vecMul nu K y = P y - Q y := by
    intro y
    have hsplitA : (∑ x ∈ A, (mu x - nu x) * K x y)
        + (∑ x ∈ B, (mu x - nu x) * K x y)
        = ∑ x : S, (mu x - nu x) * K x y := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - nu x) (fun x => (mu x - nu x) * K x y)
    calc vecMul mu K y - vecMul nu K y
        = (∑ x, mu x * K x y) - (∑ x, nu x * K x y) := rfl
      _ = ∑ x, (mu x - nu x) * K x y := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => (sub_mul _ _ _).symm
      _ = (∑ x ∈ A, (mu x - nu x) * K x y)
          + (∑ x ∈ B, (mu x - nu x) * K x y) := hsplitA.symm
      _ = P y - Q y := by rw [hPy y, hQy y]; ring
  -- both halves stay above the Doeblin floor
  have hPge : ∀ y, c * delta ≤ P y := by
    intro y
    rw [hPy y]
    calc c * delta = ∑ x ∈ A, c * (mu x - nu x) := by
          rw [hdeltadef, ← Finset.mul_sum]
      _ = ∑ x ∈ A, (mu x - nu x) * c :=
          Finset.sum_congr rfl fun x _ => mul_comm _ _
      _ ≤ ∑ x ∈ A, (mu x - nu x) * K x y :=
          Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (hc x y) (hAnn x hx)
  have hQge : ∀ y, c * delta ≤ Q y := by
    intro y
    rw [hQy y]
    have h1 : ∑ x ∈ B, (mu x - nu x) * K x y
        ≤ c * (∑ x ∈ B, (mu x - nu x)) := by
      calc ∑ x ∈ B, (mu x - nu x) * K x y
          ≤ ∑ x ∈ B, (mu x - nu x) * c :=
            Finset.sum_le_sum fun x hx =>
              mul_le_mul_of_nonpos_left (hc x y) (hBnn x hx)
        _ = c * (∑ x ∈ B, (mu x - nu x)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
    rw [hBdelta] at h1
    calc -∑ x ∈ B, (mu x - nu x) * K x y ≥ -(c * -delta) := neg_le_neg h1
      _ = c * delta := by ring
  -- totals
  have hinner : ∀ x : S, ∑ y : S, (mu x - nu x) * K x y = (mu x - nu x) := by
    intro x
    calc ∑ y : S, (mu x - nu x) * K x y
        = ∑ y : S, K x y * (mu x - nu x) :=
            Finset.sum_congr rfl fun y _ => mul_comm _ _
      _ = (∑ y : S, K x y) * (mu x - nu x) :=
            (Finset.sum_mul Finset.univ (fun y => K x y) (mu x - nu x)).symm
      _ = 1 * (mu x - nu x) := by rw [hrow x]
      _ = mu x - nu x := one_mul _
  have hPsum : ∑ y, P y = delta := by
    have hswap : ∑ y, P y = ∑ y, ∑ x ∈ A, (mu x - nu x) * K x y :=
      Finset.sum_congr rfl fun y _ => hPy y
    rw [hswap, Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
  have hQsum : ∑ y, Q y = delta := by
    have hstep : ∑ y, ∑ x ∈ B, (mu x - nu x) * K x y = ∑ x ∈ B, (mu x - nu x) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun x hx => hinner x]
    calc ∑ y, Q y = -∑ y, ∑ x ∈ B, (mu x - nu x) * K x y := by
          rw [← Finset.sum_neg_distrib]
      _ = -∑ x ∈ B, (mu x - nu x) := by rw [hstep]
      _ = delta := by rw [hBdelta]; ring
  -- the L1 mass of the signed difference
  have hL1d : ∑ x : S, |mu x - nu x| = 2 * delta := by
    have hAabs : ∑ x ∈ A, |mu x - nu x| = ∑ x ∈ A, (mu x - nu x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonneg (hAnn x hx)
    have hBabs : ∑ x ∈ B, |mu x - nu x| = ∑ x ∈ B, -(mu x - nu x) :=
      Finset.sum_congr rfl fun x hx => abs_of_nonpos (hBnn x hx)
    have hsplit : (∑ x ∈ A, |mu x - nu x|) + (∑ x ∈ B, |mu x - nu x|)
        = ∑ x : S, |mu x - nu x| := by
      rw [hAdef, hBdef]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => 0 ≤ mu x - nu x) (fun x => |mu x - nu x|)
    have hneg : ∑ x ∈ B, -(mu x - nu x) = -∑ x ∈ B, (mu x - nu x) := by
      simp
    rw [← hsplit, hAabs, hBabs, hneg, hBdelta]
    ring
  -- the min-overlap floor
  have hsummin : (Fintype.card S : ℝ) * (c * delta) ≤ ∑ y, min (P y) (Q y) := by
    calc (Fintype.card S : ℝ) * (c * delta)
        = ∑ y : S, c * delta := by simp
      _ ≤ ∑ y, min (P y) (Q y) :=
          Finset.sum_le_sum fun y _ => le_min (hPge y) (hQge y)
  -- the L1 identity behind the coupling bound
  have habs : ∀ y, |vecMul mu K y - vecMul nu K y|
      = P y + Q y - 2 * min (P y) (Q y) := by
    intro y
    rw [hdiff y]
    rcases le_total (P y) (Q y) with h | h
    · rw [abs_of_nonpos (by linarith : P y - Q y ≤ 0), min_eq_left h]
      ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ P y - Q y), min_eq_right h]
      ring
  -- assemble
  change (∑ y, |vecMul mu K y - vecMul nu K y|) / 2
      ≤ (1 - (Fintype.card S : ℝ) * c) * ((∑ y, |mu y - nu y|) / 2)
  calc (∑ y, |vecMul mu K y - vecMul nu K y|) / 2
      = (∑ y, (P y + Q y - 2 * min (P y) (Q y))) / 2 := by
        refine congrArg (fun t => t / 2) (Finset.sum_congr rfl fun y _ => habs y)
    _ = ((∑ y, P y) + (∑ y, Q y) - 2 * ∑ y, min (P y) (Q y)) / 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ((2 * delta) - 2 * ((Fintype.card S : ℝ) * (c * delta))) / 2 := by
        nlinarith [hPsum, hQsum]
    _ = (1 - (Fintype.card S : ℝ) * c) * ((∑ y, |mu y - nu y|) / 2) := by
        rw [hL1d]; ring

/-- (A8 MAIN) One-step contraction TO A STATIONARY measure (sharp
constant): if `π` is stationary for a row-stochastic kernel with
entry floor `c`, then `TV(μK, π) ≤ (1 − |S|·c)·TV(μ, π)` for any `μ`
with the same total mass as `π`. -/
theorem tv_contraction_stationary_sharp (K : S → S → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (hc : ∀ x y, c ≤ K x y)
    (pi : S → ℝ) (hstat : ∀ y, vecMul pi K y = pi y) (mu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, pi x) :
    Hagi.Prelude.tvDef (vecMul mu K) pi
      ≤ (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi := by
  have hpi : vecMul pi K = pi := funext hstat
  have halign : Hagi.Prelude.tvDef (vecMul mu K) pi
      = Hagi.Prelude.tvDef (vecMul mu K) (vecMul pi K) := by rw [hpi]
  rw [halign]
  exact tv_pair_contraction K hrow c hc mu pi hmass

omit [Nonempty S] in
/-- `(1 : ℝ) ≤ |S|` for a nonempty finite type. -/
theorem one_le_card_fin (S : Type*) [Fintype S] [Nonempty S] :
    (1 : ℝ) ≤ (Fintype.card S : ℝ) := by
  obtain ⟨a⟩ := ‹Nonempty S›
  rw [← Nat.cast_one, Nat.cast_le]
  exact Finset.one_le_card.2 ⟨a, Finset.mem_univ a⟩

/-- One-step contraction to a stationary measure, audit-text weak
constant: `TV(μK, π) ≤ (1 − c)·TV(μ, π)` (the sharp constant is
`(1 − |S|·c)`, see `tv_contraction_stationary_sharp`; `0 ≤ c` and
nonemptiness make the weak form a corollary). -/
theorem tv_contraction_stationary (K : S → S → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x y, c ≤ K x y)
    (pi : S → ℝ) (hstat : ∀ y, vecMul pi K y = pi y) (mu : S → ℝ)
    (hmass : ∑ x, mu x = ∑ x, pi x) :
    Hagi.Prelude.tvDef (vecMul mu K) pi
      ≤ (1 - c) * Hagi.Prelude.tvDef mu pi := by
  refine le_trans (tv_contraction_stationary_sharp K hrow c hc pi hstat mu hmass) ?_
  have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) := one_le_card_fin S
  have hnn : 0 ≤ Hagi.Prelude.tvDef mu pi := tvDef_nonneg mu pi
  have key : (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi
      ≤ (1 - c) * Hagi.Prelude.tvDef mu pi := by
    have hnnn : 0 ≤ ((Fintype.card S : ℝ) - 1) * c * Hagi.Prelude.tvDef mu pi :=
      mul_nonneg (mul_nonneg (by linarith) hc0) hnn
    have hident : (1 - c) * Hagi.Prelude.tvDef mu pi
        - (1 - (Fintype.card S : ℝ) * c) * Hagi.Prelude.tvDef mu pi
        = ((Fintype.card S : ℝ) - 1) * c * Hagi.Prelude.tvDef mu pi := by ring
    linarith
  linarith

omit [Nonempty S] in
/-- TV between two probability vectors is at most one. -/
theorem tvDef_le_one_of_prob (mu nu : S → ℝ)
    (hnn1 : ∀ x, 0 ≤ mu x) (hnn2 : ∀ x, 0 ≤ nu x)
    (hs1 : ∑ x, mu x = 1) (hs2 : ∑ x, nu x = 1) :
    Hagi.Prelude.tvDef mu nu ≤ 1 := by
  have h1 : ∑ y, |mu y - nu y| ≤ ∑ y, (mu y + nu y) :=
    Finset.sum_le_sum fun y _ => abs_le.2 ⟨by linarith [hnn1 y, hnn2 y],
      by linarith [hnn1 y, hnn2 y]⟩
  rw [Finset.sum_add_distrib, hs1, hs2] at h1
  unfold Hagi.Prelude.tvDef
  linarith

end Generic

section WeightFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Field-spread weight floor: if all local-field differences at cell
`i` are bounded by `M` in absolute value and `T > 0`, then EVERY
heat-bath weight is at least `exp(−M/T) / card α` — each softmax
exponent is within `M/T` of the largest one, so the normalizer is at
most `card α · exp(M/T)` times the numerator. -/
theorem heatbathWeight_floor (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (M : ℝ)
    (hM : ∀ a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T) (a : α) :
    Real.exp (-(M / T)) / (Fintype.card α : ℝ)
      ≤ heatbathWeight B K T y i a := by
  have hcardpos : 0 < (Fintype.card α : ℝ) :=
    Nat.cast_pos.2 (Fintype.card_pos)
  unfold heatbathWeight softDef
  set La : ℝ := -(localField B K y i a) / T with hLa
  set Z : ℝ := ∑ b : α, Real.exp (-(localField B K y i b) / T) with hZ
  have hZpos : 0 < Z :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hmem : ∀ b : α, Real.exp (-(localField B K y i b) / T)
      ≤ Real.exp La * Real.exp (M / T) := by
    intro b
    have hL : localField B K y i a - localField B K y i b ≤ M :=
      (abs_le.mp (hM a b)).2
    have hexp : -(localField B K y i b) / T ≤ La + M / T := by
      have key : -localField B K y i b / T
          ≤ (-localField B K y i a + M) / T := by
        rw [div_le_div_iff₀ hT hT]
        nlinarith [hT]
      have hsplit : (-localField B K y i a + M) / T
          = -localField B K y i a / T + M / T := by
        rw [add_div]
      linarith
    calc Real.exp (-(localField B K y i b) / T)
        ≤ Real.exp (La + M / T) := Real.exp_le_exp.2 hexp
      _ = Real.exp La * Real.exp (M / T) := Real.exp_add _ _
  have hZle : Z ≤ (Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)) := by
    calc Z = ∑ b, Real.exp (-(localField B K y i b) / T) := rfl
      _ ≤ ∑ b : α, Real.exp La * Real.exp (M / T) :=
          Finset.sum_le_sum fun b _ => hmem b
      _ = (Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)) := by
          have hsc : ∑ b : α, Real.exp (M / T)
              = (Fintype.card α : ℝ) * Real.exp (M / T) := by simp
          rw [← Finset.mul_sum, hsc]
          ring
  have hexp1 : Real.exp (-(M / T)) * Real.exp (M / T) = 1 := by
    have h0 : (-(M / T)) + M / T = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  have h1 : Real.exp (-(M / T)) * Z
      ≤ Real.exp La * (Fintype.card α : ℝ) := by
    have h2 : Real.exp (-(M / T)) * Z
        ≤ Real.exp (-(M / T))
            * ((Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T))) :=
      mul_le_mul_of_nonneg_left hZle (Real.exp_nonneg _)
    have h3 : Real.exp (-(M / T))
        * ((Fintype.card α : ℝ) * (Real.exp La * Real.exp (M / T)))
        = Real.exp La * (Fintype.card α : ℝ) := by
      linear_combination (Real.exp La * (Fintype.card α : ℝ)) * hexp1
    linarith
  rw [div_le_div_iff₀ hcardpos hZpos]
  linarith

/-- (A8 MAIN, premise-form) Doeblin floor for the heat-bath kernel:
under the field-spread bound `hM` at cell `i`, temperature `T > 0`,
and the SUPPORT premise `hsupp` (every target `z` agrees with the
source `y` off cell `i` — i.e. every transition is a single-cell
move), the heat-bath kernel is `doeblinMinorized` with floor
`exp(−M/T)/card α`. HONEST: for `card ι ≥ 2` the unconditional
single-cell kernel does NOT satisfy `hsupp` (off-support entries are
zero) — the floor is a premise the consumer must discharge (see
`heatbath_doeblin_floor_subsingleton` for the case where it holds
unconditionally). -/
theorem heatbath_doeblin_floor (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (M : ℝ)
    (hM : ∀ y a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T)
    (hsupp : ∀ (y z : ι → α), ∀ j, j ≠ i → z j = y j) :
    doeblinMinorized (heatbathKernel B K T i)
      (Real.exp (-(M / T)) / (Fintype.card α : ℝ)) := by
  have hcardpos : 0 < (Fintype.card α : ℝ) :=
    Nat.cast_pos.2 (Fintype.card_pos)
  refine ⟨div_pos (Real.exp_pos _) hcardpos, ?_⟩
  intro y z
  classical
  simp only [heatbathKernel]
  split
  · exact heatbathWeight_floor B K T y i M (hM y) hT (z i)
  · next h => exact absurd (fun j hj => hsupp y z j hj) h

/-- The support premise of `heatbath_doeblin_floor` holds
unconditionally when the cell index type is a subsingleton (a
single-cell configuration space: every target trivially agrees with
the source off the only cell). -/
theorem heatbath_doeblin_floor_subsingleton (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (M : ℝ)
    (hM : ∀ y a b, |localField B K y i a - localField B K y i b| ≤ M)
    (hT : 0 < T) [Subsingleton ι] :
    doeblinMinorized (heatbathKernel B K T i)
      (Real.exp (-(M / T)) / (Fintype.card α : ℝ)) :=
  heatbath_doeblin_floor B K T i M hM hT
    (fun y z j hj => absurd (Subsingleton.elim j i) hj)

end WeightFloor

section Stationary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The NORMALIZED Boltzmann density: `boltzmannDensity` divided by
its total mass (a genuine probability vector on the finite
configuration space). -/
noncomputable def stationaryDensity (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) : (ι → α) → ℝ :=
  fun y => boltzmannDensity B K T y / (∑ z, boltzmannDensity B K T z)

/-- The normalizer is strictly positive (an exponential sum over a
  nonempty space). -/
theorem stationaryDensity_norm_pos (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) :
    0 < ∑ z, boltzmannDensity B K T z :=
  Finset.sum_pos (fun z _ => Real.exp_pos _) Finset.univ_nonempty

/-- The stationary density is strictly positive everywhere. -/
theorem stationaryDensity_pos (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (y : ι → α) :
    0 < stationaryDensity B K T y := by
  unfold stationaryDensity
  exact div_pos (Real.exp_pos _) (stationaryDensity_norm_pos B K T)

/-- The stationary density sums to one. -/
theorem stationaryDensity_sum_one (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) :
    ∑ y, stationaryDensity B K T y = 1 := by
  have hZ : 0 < ∑ z, boltzmannDensity B K T z := stationaryDensity_norm_pos B K T
  unfold stationaryDensity
  rw [← Finset.sum_div, div_self (ne_of_gt hZ)]

/-- The normalized Boltzmann density is stationary for the heat-bath
kernel (the unnormalized `heatbath_stationary` divided through by the
constant normalizer). -/
theorem stationaryDensity_stationary (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (hT : T ≠ 0) (i : ι) (z : ι → α) :
    vecMul (stationaryDensity B K T) (heatbathKernel B K T i) z
      = stationaryDensity B K T z := by
  have hZ : 0 < ∑ w, boltzmannDensity B K T w := stationaryDensity_norm_pos B K T
  have hstat := heatbath_stationary B K hK hT i z
  unfold kernelStationary at hstat
  unfold stationaryDensity vecMul
  have hsplit : ∀ y : ι → α,
      (boltzmannDensity B K T y / ∑ w, boltzmannDensity B K T w)
          * heatbathKernel B K T i y z
      = (boltzmannDensity B K T y * heatbathKernel B K T i y z)
          / ∑ w, boltzmannDensity B K T w := by
    intro y
    rw [div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl fun y _ => hsplit y, ← Finset.sum_div, hstat]

/-- (A8 MAIN) One-step TV contraction for the heat-bath kernel,
audit-text weak constant: IF the kernel is Doeblin-minorized with
floor `c` (a PREMISE — see `heatbath_doeblin_floor` for when it
holds), THEN `TV(μK, π̂) ≤ (1 − c)·TV(μ, π̂)` for every probability
vector `μ`, with `π̂` the normalized Boltzmann density. -/
theorem heatbath_tv_contraction (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1) :
    Hagi.Prelude.tvDef (vecMul mu (heatbathKernel B K T i))
        (stationaryDensity B K T)
      ≤ (1 - c) * Hagi.Prelude.tvDef mu (stationaryDensity B K T) :=
  tv_contraction_stationary (heatbathKernel B K T i)
    (fun y => heatbathKernel_rowsum B K T i y) c (le_of_lt hD.1) hD.2 _
    (stationaryDensity_stationary B K hK hT i) mu
    (by rw [hmu, stationaryDensity_sum_one])

/-- (A8 MAIN) One-step TV contraction for the heat-bath kernel, SHARP
constant `1 − |ι→α|·c` (the audit-text `1 − c` form is
`heatbath_tv_contraction`; the row sums force `c ≤ 1/|ι→α|`, so the
sharp constant is the larger contraction rate). -/
theorem heatbath_tv_contraction_sharp (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1) :
    Hagi.Prelude.tvDef (vecMul mu (heatbathKernel B K T i))
        (stationaryDensity B K T)
      ≤ (1 - (Fintype.card (ι → α) : ℝ) * c)
          * Hagi.Prelude.tvDef mu (stationaryDensity B K T) :=
  tv_contraction_stationary_sharp (heatbathKernel B K T i)
    (fun y => heatbathKernel_rowsum B K T i y) c hD.2 _
    (stationaryDensity_stationary B K hK hT i) mu
    (by rw [hmu, stationaryDensity_sum_one])

/-- (A8 MAIN) Geometric mixing: under the Doeblin premise, the n-step
heat-bath chain from ANY start distribution `μ` satisfies
`TV(μKⁿ, π̂) ≤ (1 − c)ⁿ`. The chain stays a probability vector
(`hbChain_sum` / `hbChain_nonneg`) and `TV(μ, π̂) ≤ 1`
(`tvDef_le_one_of_prob`). -/
theorem heatbath_mixing (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1)
    (hnn : ∀ x, 0 ≤ mu x) (n : ℕ) :
    Hagi.Prelude.tvDef (hbChain mu (heatbathKernel B K T i) n)
        (stationaryDensity B K T)
      ≤ (1 - c) ^ n := by
  have hrow : ∀ x, ∑ y, heatbathKernel B K T i x y = 1 :=
    fun x => heatbathKernel_rowsum B K T i x
  have hnnK : ∀ x y, 0 ≤ heatbathKernel B K T i x y :=
    fun x y => heatbathKernel_nonneg B K T i x y
  -- c ≤ 1: the row sums force card · c ≤ 1
  obtain ⟨x0⟩ : Nonempty (ι → α) := inferInstance
  have hcard1 : (1 : ℝ) ≤ (Fintype.card (ι → α) : ℝ) := one_le_card_fin _
  have hcardc : (Fintype.card (ι → α) : ℝ) * c ≤ 1 := by
    have h1 : ∑ y : ι → α, c ≤ ∑ y : ι → α, heatbathKernel B K T i x0 y :=
      Finset.sum_le_sum fun y _ => hD.2 x0 y
    have h2 : ∑ y : ι → α, c = (Fintype.card (ι → α) : ℝ) * c := by simp
    rw [h2, hrow x0] at h1
    exact h1
  have hc1 : 0 ≤ 1 - c := by nlinarith
  have hstep : ∀ m : (ι → α) → ℝ, ∑ x, m x = 1 →
      Hagi.Prelude.tvDef (vecMul m (heatbathKernel B K T i))
          (stationaryDensity B K T)
        ≤ (1 - c) * Hagi.Prelude.tvDef m (stationaryDensity B K T) :=
    fun m hm =>
      heatbath_tv_contraction B K T i c hD hK hT m hm
  induction n with
  | zero =>
      show Hagi.Prelude.tvDef mu (stationaryDensity B K T) ≤ 1
      have hpi : ∀ x, 0 ≤ stationaryDensity B K T x :=
        fun x => le_of_lt (stationaryDensity_pos B K T x)
      exact tvDef_le_one_of_prob mu (stationaryDensity B K T) hnn hpi hmu
        (stationaryDensity_sum_one B K T)
  | succ n ih =>
      have hsumn : ∑ x, hbChain mu (heatbathKernel B K T i) n x = 1 :=
        hbChain_sum (heatbathKernel B K T i) hrow mu hmu n
      show Hagi.Prelude.tvDef
          (vecMul (hbChain mu (heatbathKernel B K T i) n)
            (heatbathKernel B K T i)) (stationaryDensity B K T)
        ≤ (1 - c) ^ (n + 1)
      calc Hagi.Prelude.tvDef
            (vecMul (hbChain mu (heatbathKernel B K T i) n)
              (heatbathKernel B K T i)) (stationaryDensity B K T)
          ≤ (1 - c) * Hagi.Prelude.tvDef
              (hbChain mu (heatbathKernel B K T i) n)
              (stationaryDensity B K T) := hstep _ hsumn
        _ ≤ (1 - c) * ((1 - c) ^ n) :=
            mul_le_mul_of_nonneg_left ih hc1
        _ = (1 - c) ^ (n + 1) := by rw [pow_succ]; ring

/-- (A8 MAIN) Mixing-time corollary: under the Doeblin premise with
`c < 1`, after `n ≥ log e / log (1 − c)` steps the chain is within
`e` (any `e > 0`) of the stationary density in TV. Route: the
geometric bound `heatbath_mixing` plus `exp (n · log (1 − c)) ≤ e`
(the base `1 − c` lies in `(0, 1)`, so `log (1 − c) < 0` and the
division flips). -/
theorem heatbath_mixing_time (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (T : ℝ) (i : ι) (c : ℝ)
    (hD : doeblinMinorized (heatbathKernel B K T i) c)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (mu : (ι → α) → ℝ) (hmu : ∑ x, mu x = 1)
    (hnn : ∀ x, 0 ≤ mu x)
    (e : ℝ) (he : 0 < e) (hc1 : c < 1) (n : ℕ)
    (hn : Real.log e / Real.log (1 - c) ≤ n) :
    Hagi.Prelude.tvDef (hbChain mu (heatbathKernel B K T i) n)
        (stationaryDensity B K T)
      ≤ e := by
  have hmix := heatbath_mixing B K T i c hD hK hT mu hmu hnn n
  have h01 : 0 < 1 - c := by linarith [hD.1]
  have hc0 : 0 < c := hD.1
  have hlogneg : Real.log (1 - c) < 0 := by
    have hlt : 1 - c < (1 : ℝ) := by linarith
    have h := Real.log_lt_log h01 hlt
    rw [Real.log_one] at h
    linarith
  have hnpow : (1 - c) ^ n ≤ e := by
    have hkey : (n : ℝ) * Real.log (1 - c) ≤ Real.log e := by
      have hLne : Real.log (1 - c) ≠ 0 := by
        intro h0
        rw [h0] at hlogneg
        exact absurd hlogneg (by norm_num : ¬(0 : ℝ) < 0)
      have hdiv : Real.log e / Real.log (1 - c) * Real.log (1 - c)
          = Real.log e := by
        field_simp
      calc (n : ℝ) * Real.log (1 - c)
          ≤ (Real.log e / Real.log (1 - c)) * Real.log (1 - c) :=
            mul_le_mul_of_nonpos_right hn (by linarith)
        _ = Real.log e := hdiv
    calc (1 - c) ^ n
        = Real.exp ((n : ℝ) * Real.log (1 - c)) := by
            rw [Real.exp_nat_mul, Real.exp_log h01]
      _ ≤ Real.exp (Real.log e) := Real.exp_le_exp.2 hkey
      _ = e := Real.exp_log he
  linarith

end Stationary

section Fixture
/-! ## Fin 2 × Bool fixture (Bex/Kex/xtt carriers from C260) -/

open Hagi.Energy

/-- Numeric anchor for `heatbathWeight_floor` (no theorem, bare
numbers): with local fields `0` and `3` at the fixture state, the
spread is `3`, and the floor `exp(−3)/2` is below the exact weight
`1/(1 + exp(−3))` of the better value. -/
example : Real.exp (-(3 : ℝ)) / (Fintype.card Bool : ℝ)
    ≤ 1 / (1 + Real.exp (-(3 : ℝ))) := by
  have hpos : 0 < Real.exp (-(3 : ℝ)) := Real.exp_pos _
  have hle : Real.exp (-(3 : ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by norm_num : -(3 : ℝ) ≤ 0)
  have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num
  have hden : 0 < 1 + Real.exp (-(3 : ℝ)) := by positivity
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [hcard, div_le_div_iff₀ h2 hden]
  nlinarith [hpos, hle, mul_le_mul_of_nonneg_left hle (le_of_lt hpos)]

/-- The same anchor THROUGH `heatbathWeight_floor`: the fixture fields
`L_0(f) = 0`, `L_0(t) = 3` (spread `3` at `T = 1`) give the weight of
the better value `f` the floor `exp(−3)/2`. -/
example : Real.exp (-(3 : ℝ)) / (Fintype.card Bool : ℝ)
    ≤ heatbathWeight Bex Kex 1 xtt 0 false := by
  have hM : ∀ a b : Bool,
      |localField Bex Kex xtt 0 a - localField Bex Kex xtt 0 b| ≤ (3 : ℝ) := by
    intro a b
    have hLt : localField Bex Kex xtt 0 true = 3 := by
      simp only [localField, xtt, Bex, Kex]
      norm_num
    have hLf : localField Bex Kex xtt 0 false = 0 := by
      simp only [localField, xtt, Bex, Kex]
      norm_num
    cases a <;> cases b <;> simp only [hLt, hLf] <;> norm_num
  have hf := heatbathWeight_floor Bex Kex 1 xtt 0 3 hM (by norm_num) false
  simpa using hf

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Greedy finite termination and the focused-policy invariance audit

Track P1-remainder (addendum A11): the two honest closures of the
greedy single-cell search story on a FINITE configuration space.

* `greedy_strict_search_terminates` — (A6 MAIN) on a finite space a
  strictly-improving trajectory cannot be long: a list of
  configurations along which the energy `H` strictly decreases at
  every pair has length at most the number of DISTINCT energy values
  `Fintype.card (Set.image H univ)` (the ranking bound: an infinite
  strictly-descending chain would produce arbitrarily long such
  lists). No rate or complexity claim is made.
* `greedy_search_terminal_is_coordinate_minimum` — (A6 MAIN) a
  terminal state of strict-improvement greedy search — one where NO
  single-cell move has a positive C261 local-field margin — is a
  COORDINATE minimum (`IsCoordinateMinimum` reused verbatim).
* `focusedDisagreementWeight` — the PRACTICAL focused selection rule
  of A9-supplement §E4: cell `i` is weighted by its OWN disagreement
  `Σ_a max 0 (L_i(y_i) − L_i(a))` (state-dependent through y_i itself).
* `concrete_focus_policy_violates_invariance` — (A7 MAIN, NEGATIVE
  witness) the disagreement weight CHANGES under a move of its own
  cell (fixture: `3 → 0`), so the INVARIANCE premise
  `w(y^{i←a})_i = w(y)_i` of `focused_mixture_stationary` FAILS for
  this policy: stationarity of the practical focused sampler is NOT
  certified — premise-form only.

## Honest boundaries (A11 'not to adopt')

* COORDINATE MINIMUM ≠ GLOBAL MINIMUM ≠ VALID SOLUTION: the terminal
  state of greedy search is only a coordinate minimum (ties allowed;
  witness in `Hagi.Energy.SingleCellDescent`: coordinate-min state
  that is not global); energy says nothing about constraints (E4
  separation in `EnergyStop`).
* The termination bound is a LIST bound on a finite type; no
  measure-theoretic packaging, no mixing-time, no convergence rate.
* A7 is a NEGATIVE result by design: it closes the audit question of
  A11 ("focused-policy invariance check — likely VIOLATES") with a
  concrete witness; it does NOT define an alternative invariant
  policy (a y-minus-i-measurable rule would satisfy the premise —
  that is policy design, out of scope).
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section Termination

variable {γ : Type*} [Fintype γ]

omit [Fintype γ] in
/-- The energy values along a pairwise strictly-improving trajectory
are pairwise DISTINCT (strictly decreasing), so the mapped list is
`Nodup`. -/
private theorem nodup_map_energy_of_pairwise {H : γ → ℝ} {l : List γ}
    (h : l.Pairwise (fun a b => H b < H a)) : (List.map H l).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rcases List.pairwise_cons.1 h with ⟨hhead, hchain⟩
    have hnod : (List.map H xs).Nodup := ih hchain
    have hlt : ∀ v ∈ (List.map H xs), v < H x := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
      exact hhead b hb
    rw [List.map_cons, List.nodup_cons]
    exact ⟨fun hmem => absurd (hlt (H x) hmem) (lt_irrefl (H x)), hnod⟩

/-- (A6 MAIN) Greedy finite termination: on a FINITE configuration
space, a strictly-improving trajectory (a list of configurations
whose energy `H` strictly decreases along every pair — the
transitive closure of the per-step strict drop) has length at most
the number of DISTINCT energy values `Fintype.card (Set.image H
univ)`. An infinite strictly-descending chain would produce
arbitrarily long such lists, so none exists. The bound is the honest
ranking statement; NO rate, complexity or mixing-time claim is made,
and the terminal state claim is `greedy_search_terminal_is_
coordinate_minimum` below. -/
theorem greedy_strict_search_terminates (H : γ → ℝ) (l : List γ)
    (h : l.Pairwise (fun a b => H b < H a)) :
    l.length ≤ Fintype.card (Set.image H (Set.univ : Set γ)) := by
  have himage : ∀ v ∈ (List.map H l), v ∈ Set.image H (Set.univ : Set γ) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ⟨x, Set.mem_univ _, rfl⟩
  have hnodup : (List.map H l).Nodup := nodup_map_energy_of_pairwise h
  let m : List {x // x ∈ Set.image H (Set.univ : Set γ)} :=
    (List.map H l).attach.map (fun p => ⟨p.1, himage p.1 p.2⟩)
  have hml : m.length = l.length := by simp [m, List.length_attach]
  have hmn : m.Nodup :=
    List.Nodup.map
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      (List.nodup_attach.mpr hnodup)
  calc l.length = m.length := hml.symm
    _ ≤ Fintype.card {x // x ∈ Set.image H (Set.univ : Set γ)} :=
        hmn.length_le_card

end Termination

section Terminal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- (A6 MAIN) The terminal state of strict-improvement greedy search
is a COORDINATE minimum: if at `y` NO single-cell move has a strictly
positive C261 local-field margin (`0 < L_i(y_i) − L_i(a)` fails for
every cell `i` and value `a` — strict improvement is unavailable),
then `y` is an `IsCoordinateMinimum` (no single-cell move decreases
the energy; ties allowed). HONEST SCOPE: a coordinate minimum is NOT
the global minimum (witness in `Hagi.Energy.SingleCellDescent`) and
NOT a validity certificate (E4 separation in
`EnergyStop`). -/
theorem greedy_search_terminal_is_coordinate_minimum (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (y : ι → α)
    (h : ∀ (i : ι) (a : α),
      ¬ 0 < localField B K y i (y i) - localField B K y i a) :
    IsCoordinateMinimum B K y := by
  intro i a
  have hd := single_cell_move_energy_delta_symm B K hK y i a
  have hle : localField B K y i (y i) ≤ localField B K y i a := by
    linarith [h i a]
  linarith

end Terminal

section FocusAudit

/-! ## A7: the practical focused selection rule vs the C263
INVARIANCE premise. The rule weights cell `i` by its OWN
disagreement — state-dependent through y_i ITSELF, which is
exactly what the invariance premise forbids. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The PRACTICAL focused selection weight of A9-supplement §E4:
cell `i` is weighted by its own disagreement
`Σ_a max 0 (L_i(y_i) − L_i(a))` with `L` the C261 `localField`.
State-dependent through y_i itself (and through the other cells via the
field). This is the rule the CRAM focused sampler actually uses;
against the C263 `focused_mixture_stationary` premises it satisfies
SUPPORT structurally (heat-bath kernels) but INVARIANCE only as an
UNVERIFIED premise — see the witness below. -/
noncomputable def focusedDisagreementWeight (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) (i : ι) : ℝ :=
  ∑ a, max 0 (localField B K y i (y i) - localField B K y i a)

/-- Local-field anchor on the Fin 2 × Bool fixture (C260 `Bex`/
`Kex`/`xtt`): at cell `0`, whenever `y 1 = true`, the field is
`L_0(c) = if c then 3 else 0` — it depends ONLY on `y 1`, never on
`y 0`. -/
private theorem localField_cell0_fixture (y : Fin 2 → Bool)
    (hy1 : y 1 = true) (c : Bool) :
    localField Bex Kex y 0 c = if c then (3 : ℝ) else 0 := by
  simp only [localField, Bex, Kex]
  fin_cases c <;> norm_num [hy1]

/-- Numeric anchor: at `xtt = (t, t)` the disagreement weight of
cell `0` is `max 0 (3 − 3) + max 0 (3 − 0) = 3`. -/
example : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
  have hL : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  simp only [focusedDisagreementWeight, hL, xtt]
  norm_num

/-- (A7 MAIN, NEGATIVE WITNESS) The practical focused selection rule
VIOLATES the INVARIANCE premise of `focused_mixture_stationary`
(C263): after the greedy move of cell `0` from `t` to `f` (its local
field minimizer on the fixture), the weight of cell `0` DROPS from
`3` to `0` — `w(y^{0←f})_0 ≠ w(y)_0`. The weight depends on y_0
itself through `L_i(y_i)`, which is exactly what the premise
forbids. Consequence, stated honestly: the C263 stationarity
theorem applies to the practical focused sampler ONLY in
premise-form — the INVARIANCE premise is FALSE for this policy, so
NO stationarity claim for the practical focused sampler is certified
here. -/
theorem concrete_focus_policy_violates_invariance :
    focusedDisagreementWeight Bex Kex (Function.update xtt 0 false) 0
      ≠ focusedDisagreementWeight Bex Kex xtt 0 := by
  have hy0 : Function.update xtt 0 false 0 = false :=
    Function.update_self 0 false xtt
  have hL : ∀ c, localField Bex Kex (Function.update xtt 0 false) 0 c
      = if c then (3 : ℝ) else 0 := by
    intro c
    simp only [localField, Bex, Kex]
    fin_cases c <;> norm_num [xtt]
  have hw0 : focusedDisagreementWeight Bex Kex
      (Function.update xtt 0 false) 0 = 0 := by
    simp only [focusedDisagreementWeight, hL, hy0]
    norm_num
  have hw1 : focusedDisagreementWeight Bex Kex xtt 0 = 3 := by
    have hL' : ∀ c, localField Bex Kex xtt 0 c = if c then (3 : ℝ) else 0 := by
      intro c
      simp only [localField, Bex, Kex]
      fin_cases c <;> norm_num [xtt]
    simp only [focusedDisagreementWeight, hL', xtt]
    norm_num
  rw [hw0, hw1]
  norm_num

end FocusAudit

section Fixture
/-! ## Fin 2 × Bool fixture: the termination bound closes on a
concrete two-state trajectory (C260 carriers). -/

/-- Bound fixture: the two-state strictly-decreasing trajectory
`[true, false]` under `H = fun b => if b then 1 else 0` has length
`2` at most the cardinality of the two-element energy image. -/
example :
    ([true, false] : List Bool).length ≤
    Fintype.card (Set.image (fun b => if b then (1 : ℝ) else 0)
      (Set.univ : Set Bool)) := by
  refine greedy_strict_search_terminates _ _ ?_
  simp [List.pairwise_cons]

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Concrete validity separation for penalty energies

Track P1-remainder (addendum A11, item A5): the E4 separation premise
"H(y) ≤ τ ⇒ valid(y)" INSTANTIATED for concrete penalty energies —
proved, not postulated. Primary instance: graph coloring with a
conflict-count energy realized as the pairwise energy
`Hagi.Energy.pairwiseEnergy`.

* `energy_threshold_lt_min_penalty_implies_valid` — (A5 CORE,
  premise-form) if the energy is a finite sum of nonnegative
  penalties, every nonzero penalty is at least `pmin > 0`, and zero
  penalties imply validity, then energy `< pmin` gives validity.
  This is the reusable core covering integer-penalty families
  (sudoku cell/duplicate penalties, nqueens attack pairs) in
  premise-form: each family supplies its own `hviol`/`hvalid`.
* `graph_coloring_zero_energy_iff_valid` — the conflict-count energy
  `pairwiseEnergy 0 (coloringCoupling edges) y` is ZERO exactly when
  `y` is a proper coloring of `edges` (adjacency-agnostic: `edges`
  is a Finset of ordered pairs; off-diagonal premise `hnodiag`).
* `graph_coloring_separation` — the SEPARATION PREMISE PROVED for
  the coloring family at any `τ < 1`: a configuration with energy
  `≤ τ` preserves the givens (unary penalty part, via the core
  lemma) and is a proper coloring (pairwise part: each violated
  undirected edge costs exactly 1 — both ordered indicators under
  the E1 `½`-ordered-pair convention — so any violation forces
  energy ≥ 1 > τ; family-optimal threshold, `τ < 1`).
* `graph_coloring_stop_sep_valid` — an `EnergyStop` at `τ < 1`
  PRODUCES a `ValidityCertificate` through
  `stopping_sound_of_separation` with the separation premise proved
  above (an instance, not an axiom).
* `graph_coloring_stop_proper` — the companion theorem carrying the
  FULL proper-coloring content of the same stop.

## Honest boundaries (A11 'not to adopt')

* The E4 cert-kernel's unary constraint slot `C : ι → α → Prop`
  cannot express the binary edge constraint "colors differ along
  every edge"; the `ValidityCertificate` below therefore records the
  unary part (`preserves_givens` + differ from every GIVEN-colored
  neighbor), while the full proper-coloring content ships as
  `graph_coloring_stop_proper`. No overclaim is made that the
  certificate alone encodes proper coloring.
* LEARNED energies have NO such separation: a low learned energy
  does NOT imply validity (the E4 zero-field witness in
  `EnergyStop`: zero energy, invalid
  board). Acceptance of learned-sampler output is only via an
  independent validator — the `CRAMAcceptedSolution` route of the
  A9-supplement cert-kernel.
* `τ < 1` needs the symmetry premise `hsym` on the ordered edge set
  (one violated undirected edge contributes two ordered indicators;
  without symmetry a single directed conflict costs only `½`). The
  zero-energy iff needs only `hnodiag`.
* Sudoku/nqueens are NOT separately instantiated here; the general
  core covers them abstractly in premise-form.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- (A5 CORE, premise-form) Energy-separation for integer penalty
sums: if the energy is the finite sum of nonnegative penalties
(`hpen`), every nonzero penalty is at least `pmin > 0` (`hviol`),
and zero penalties imply validity (`hvalid`), then an energy below
`pmin` yields `Valid y`. The premise `hvalid` is one-directional by
design: only "zero penalties ⇒ valid" is needed; the converse is not
smuggled in. Reusable across integer-penalty families (coloring
conflicts here; sudoku/nqueens penalties in premise-form). -/
theorem energy_threshold_lt_min_penalty_implies_valid
    {κ : Type*} [Fintype κ] {Valid : (ι → α) → Prop}
    (penalty : (ι → α) → κ → ℝ) {pmin : ℝ} (_hpmin : 0 < pmin)
    (hpen : ∀ y' k, 0 ≤ penalty y' k)
    (hviol : ∀ y' k, penalty y' k ≠ 0 → pmin ≤ penalty y' k)
    (hvalid : ∀ y' : ι → α, (∀ k, penalty y' k = 0) → Valid y')
    {y : ι → α} (h : ∑ k, penalty y k < pmin) : Valid y := by
  refine hvalid y (fun k => ?_)
  by_contra h0
  have hne : penalty y k ≠ 0 := fun hc => h0 hc
  have hle : penalty y k ≤ ∑ k', penalty y k' :=
    Finset.single_le_sum (fun k' _ => hpen y k') (Finset.mem_univ k)
  have := hviol y k hne
  linarith

end General

section Coloring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Proper coloring, adjacency-agnostic: `y` is proper for the graph
given by the ordered-pair edge set `edges` when colors differ along
every edge. `edges` is the ordered representation (the graph is its
symmetric hull; `hsym` premises make this explicit where needed). -/
def isProperColoring (edges : Finset (ι × ι)) (y : ι → α) : Prop :=
  ∀ p ∈ edges, y p.1 ≠ y p.2

/-- The coloring coupling: the pairwise kernel realizing the
conflict-count energy — `K i j a b = 1` exactly on ordered edges with
equal endpoint colors, `0` otherwise. With the E1 convention
(`pairwiseEnergy B K y = Σᵢ B i (y i) + ½·Σ_{i≠j} K i j (y i) (y j)`)
this energy IS the (half-ordered) conflict count: no separate count
function is asserted equal to H — H is the conflict count by
construction. -/
def coloringCoupling (edges : Finset (ι × ι)) : ι → ι → α → α → ℝ :=
  fun i j a b => if (i, j) ∈ edges ∧ a = b then (1 : ℝ) else 0

/-- The unary given-violation penalty: `B i a = 1` when cell `i` has
a given color and `a` differs from it, `0` otherwise (precoloring
penalty for the `givens` of the certificate). -/
def coloringField (givens : ι → Option α) : ι → α → ℝ :=
  fun i a => if ∃ b, givens i = some b ∧ a ≠ b then (1 : ℝ) else 0

/-- Zero-energy iff validity for the pure coloring family (no unary
field): the conflict-count energy vanishes exactly on proper
colorings. Off-diagonal premise `hnodiag` (a diagonal "edge"
`(i, i)` never has differing endpoint colors, so zero energy cannot
imply properness there; diagonal pairs contribute nothing to the
ordered sum). -/
theorem graph_coloring_zero_energy_iff_valid (edges : Finset (ι × ι))
    (y : ι → α) (hnodiag : ∀ i, (i, i) ∉ edges) :
    pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling edges) y = 0
      ↔ isProperColoring edges y := by
  have hnn : ∀ i j, (0 : ℝ) ≤ coloringCoupling edges i j (y i) (y j) := by
    intro i j; unfold coloringCoupling; split <;> norm_num
  have hinn : ∀ i, (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {i},
      coloringCoupling edges i j (y i) (y j) :=
    fun i => Finset.sum_nonneg fun j _ => hnn i j
  constructor
  · rintro h ⟨a, b⟩ hab hcon
    -- hab : (a, b) ∈ edges, hcon : y a = y b; derive energy > 0
    have hoff : a ≠ b := by
      intro he
      rw [he] at hab
      exact hnodiag b hab
    have h1 : coloringCoupling edges a b (y a) (y b) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hab, hcon⟩]
    have hinner1 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {a},
        coloringCoupling edges a j (y a) (y j) := by
      rw [← h1]
      exact Finset.single_le_sum (fun j _ => hnn a j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ b,
          fun hb => hoff (Finset.mem_singleton.1 hb).symm⟩)
    have hge : (1 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y := by
      rw [pairwiseInteractionSum]
      calc (1:ℝ) ≤ ∑ j ∈ Finset.univ \ {a},
          coloringCoupling edges a j (y a) (y j) := hinner1
        _ ≤ ∑ i, ∑ j ∈ Finset.univ \ {i},
            coloringCoupling edges i j (y i) (y j) :=
          Finset.single_le_sum (fun i _ => hinn i) (Finset.mem_univ a)
    rw [pairwiseEnergy, Finset.sum_const_zero, zero_add] at h
    linarith
  · intro h
    have hzero : pairwiseInteractionSum (coloringCoupling edges) y = 0 := by
      rw [pairwiseInteractionSum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
      have hne : i ≠ j := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        obtain ⟨_, hj'⟩ := hj
        exact fun he => hj' he.symm
      unfold coloringCoupling
      by_cases hc : (i, j) ∈ edges ∧ y i = y j
      · exact (h (i, j) hc.1 hc.2).elim
      · rw [if_neg hc]
    rw [pairwiseEnergy, Finset.sum_const_zero, zero_add, hzero, mul_zero]

/-- The separation premise PROVED for the coloring family at any
`τ < 1`: a configuration `y` with conflict-plus-given energy `≤ τ`
preserves every given value and is a proper coloring. Unary part via
the A5 core lemma (each given violation costs `1`); pairwise part by
symmetric doubling — a violated undirected edge contributes BOTH
ordered indicators under the E1 `½` convention, so any violation
forces energy `≥ 1 > τ` (family-optimal: one violated undirected
edge costs exactly `1`). -/
theorem graph_coloring_separation (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (y : ι → α)
    (h : pairwiseEnergy (coloringField givens) (coloringCoupling edges) y ≤ τ) :
    (∀ i a, givens i = some a → y i = a) ∧ isProperColoring edges y := by
  have hBnn : ∀ i, (0 : ℝ) ≤ coloringField givens i (y i) := by
    intro i; unfold coloringField; split <;> norm_num
  have hBsum : (0 : ℝ) ≤ ∑ i, coloringField givens i (y i) :=
    Finset.sum_nonneg fun i _ => hBnn i
  have hKnn : ∀ i j, (0 : ℝ) ≤ coloringCoupling edges i j (y i) (y j) := by
    intro i j; unfold coloringCoupling; split <;> norm_num
  have hintnn : ∀ i, (0 : ℝ) ≤ ∑ j ∈ Finset.univ \ {i},
      coloringCoupling edges i j (y i) (y j) :=
    fun i => Finset.sum_nonneg fun j _ => hKnn i j
  rw [pairwiseEnergy] at h
  constructor
  · -- unary given penalties via the A5 core, pmin = 1
    have hBlt : ∑ i, coloringField givens i (y i) < 1 := by
      have hnn' : (0 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y :=
        Finset.sum_nonneg fun i _ => hintnn i
      linarith
    exact energy_threshold_lt_min_penalty_implies_valid
      (ι := ι) (α := α) (κ := ι)
      (Valid := fun y' => ∀ i a, givens i = some a → y' i = a)
      (penalty := fun y' i => coloringField givens i (y' i))
      (pmin := 1) (by norm_num)
      (fun y' i => by unfold coloringField; split <;> norm_num)
      (fun y' i _hne => by
        rcases Classical.em (∃ b, givens i = some b ∧ y' i ≠ b) with hc | hc
        · unfold coloringField; rw [if_pos hc]
        · unfold coloringField at _hne ⊢
          rw [if_neg hc] at _hne; exact absurd rfl _hne)
      (fun y' hz i a hg => by
        by_contra hcon
        have h1 : coloringField givens i (y' i) = 1 := by
          unfold coloringField
          rw [if_pos ⟨a, hg, hcon⟩]
        rw [hz i] at h1
        norm_num at h1)
      hBlt
  · -- pairwise conflicts: each violated (symmetric) edge costs ≥ 1
    by_contra hpr
    obtain ⟨p, hp0⟩ := not_forall.mp hpr
    obtain ⟨hp, hpne⟩ := not_imp.mp hp0
    have hconf : y p.1 = y p.2 := by
      by_contra hc
      exact hpne hc
    have hpe : (p.1, p.2) ∈ edges := by rw [Prod.mk.eta]; exact hp
    have hoff : p.1 ≠ p.2 := by
      intro he
      rw [he] at hpe
      exact hnodiag p.2 hpe
    have hin1 : coloringCoupling edges p.1 p.2 (y p.1) (y p.2) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hpe, hconf⟩]
    have hin2 : coloringCoupling edges p.2 p.1 (y p.2) (y p.1) = 1 := by
      unfold coloringCoupling; rw [if_pos ⟨hsym p.1 p.2 hpe, hconf.symm⟩]
    have hinner1 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {p.1},
        coloringCoupling edges p.1 j (y p.1) (y j) := by
      rw [← hin1]
      exact Finset.single_le_sum (fun j _ => hKnn p.1 j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ p.2,
          fun hb => hoff (Finset.mem_singleton.1 hb).symm⟩)
    have hinner2 : (1 : ℝ) ≤ ∑ j ∈ Finset.univ \ {p.2},
        coloringCoupling edges p.2 j (y p.2) (y j) := by
      rw [← hin2]
      exact Finset.single_le_sum (fun j _ => hKnn p.2 j)
        (Finset.mem_sdiff.2 ⟨Finset.mem_univ p.1,
          fun hb => hoff (Finset.mem_singleton.1 hb)⟩)
    have hpair : ∑ i ∈ ({p.1, p.2} : Finset ι), ∑ j ∈ Finset.univ \ {i},
        coloringCoupling edges i j (y i) (y j)
        = (∑ j ∈ Finset.univ \ {p.1}, coloringCoupling edges p.1 j (y p.1) (y j))
          + ∑ j ∈ Finset.univ \ {p.2}, coloringCoupling edges p.2 j (y p.2) (y j) :=
      Finset.sum_pair hoff
    have hrest : (0 : ℝ) ≤ ∑ i ∈ Finset.univ \ ({p.1, p.2} : Finset ι),
        ∑ j ∈ Finset.univ \ {i}, coloringCoupling edges i j (y i) (y j) :=
      Finset.sum_nonneg fun i _ => hintnn i
    have hsplit := Finset.sum_sdiff
      (s₁ := ({p.1, p.2} : Finset ι)) (s₂ := (Finset.univ : Finset ι))
      (f := fun i => ∑ j ∈ Finset.univ \ {i},
        coloringCoupling edges i j (y i) (y j))
      (Finset.subset_univ _)
    have hintge : (2 : ℝ) ≤ pairwiseInteractionSum (coloringCoupling edges) y := by
      rw [pairwiseInteractionSum]
      linarith
    linarith

/-- An `EnergyStop` for the coloring family at `τ < 1` PRODUCES a
`ValidityCertificate` — the E4 separation transfer with the premise
PROVED (this instance, not an axiom): the unary constraint slot
records "differ from every GIVEN-colored neighbor" plus
`preserves_givens`. HONEST BOUNDARY: the unary slot cannot express
the binary edge constraint; the FULL proper-coloring content ships
as the companion `graph_coloring_stop_proper`. -/
def graph_coloring_stop_sep_valid (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (s : EnergyStop (coloringField givens) (coloringCoupling edges) τ) :
    ValidityCertificate givens
      (fun i a => ∀ j b, (i, j) ∈ edges ∧ givens j = some b → a ≠ b) :=
  stopping_sound_of_separation _ _ _ _ _
    (fun y' hy' => by
      obtain ⟨hgiv, hprop⟩ :=
        graph_coloring_separation givens edges τ hsym hnodiag hτ y' hy'
      refine ⟨hgiv, fun i j b hj => ?_⟩
      obtain ⟨hmem, hgb⟩ := hj
      have h1 : y' j = b := hgiv j b hgb
      have h2 : y' i ≠ y' j := hprop (i, j) hmem
      exact fun hc => h2 (hc.trans h1.symm))
    s

/-- The companion theorem carrying the FULL proper-coloring content
of the same energy stop: the stopped configuration is a proper
coloring of `edges` (binary constraints — beyond the unary slot of
`ValidityCertificate`, see `graph_coloring_stop_sep_valid`). -/
theorem graph_coloring_stop_proper (givens : ι → Option α)
    (edges : Finset (ι × ι)) (τ : ℝ)
    (hsym : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges)
    (hnodiag : ∀ i, (i, i) ∉ edges) (hτ : τ < 1)
    (s : EnergyStop (coloringField givens) (coloringCoupling edges) τ) :
    isProperColoring edges s.y :=
  (graph_coloring_separation givens edges τ hsym hnodiag hτ s.y
    s.energy_bound).2

end Coloring

/-! ## Triangle fixture (Fin 3): anchors of the separation -/

section Fixture

/-- The triangle K₃ as a symmetric ordered edge set (Fin 3). -/
private def tri : Finset (Fin 3 × Fin 3) :=
  {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}

private theorem tri_nodiag : ∀ i : Fin 3, (i, i) ∉ tri := by
  intro i hi
  simp only [tri, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hi
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at h2 <;> exact absurd h2 (by decide)

/-- Anchor: 2 colors do NOT suffice — no proper 2-coloring of the
triangle exists (the separation family is non-vacuous: zero-energy
configurations exist only with ≥ 3 colors). -/
example : ¬ ∃ y : Fin 3 → Bool, isProperColoring tri y := by
  rintro ⟨y, hy⟩
  have h01 := hy (0, 1) (by simp [tri])
  have h02 := hy (0, 2) (by simp [tri])
  have h12 := hy (1, 2) (by simp [tri])
  revert h01 h02 h12
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;>
    simp_all [h0, h1, h2]

/-- Anchor: 3 colors suffice — the identity coloring of the triangle
has ZERO energy (the `iff` in the zero-separation direction). -/
example : pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling tri)
    (fun i => i) = 0 := by
  have hprop : isProperColoring tri (fun i : Fin 3 => i) := by
    intro p hp
    simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact (graph_coloring_zero_energy_iff_valid tri _ tri_nodiag).2 hprop

/-- Anchor: the monochrome coloring has conflicts, hence NONZERO
energy (the `iff` in the converse direction). -/
example : pairwiseEnergy (fun _ _ => (0 : ℝ)) (coloringCoupling tri)
    (fun _ => (0 : Fin 3)) ≠ 0 := by
  intro hc
  have := (graph_coloring_zero_energy_iff_valid tri _ tri_nodiag).1 hc
    (0, 1) (by simp [tri])
  simp at this

end Fixture

end Hagi.Model.EnergyReasoning

set_option linter.style.header false

/-!
# Alternating (z, y) round: strict descent with an inexact latent

Track B4 (master-plan-v3 addendum A11 B4: "alternating minimization
with summable errors ... важно не выдавать текущий frozen-z result
за joint convergence"). DESIGN-FIRST beat: the joint latent-visible
descent is organized as ALTERNATING ROUNDS with per-round
tolerances (route R1 of `.tmp/C293/design.md`):

  round t = z-phase (settle `z` toward `z*` to tolerance η_t) +
            y-phase (one guarded visible move on computed
            `K(z_t)`-fields with the COMPOSED guard).

Structural fact driving the design: `latentUpdate N m G` and
`latentEnergy N m G` do NOT depend on the visible state `y`, so the
latent fixed point `z*` is STATIC across rounds — the coupling is
one-way (z → visible through `attentionK`). Route R2 (small-gain
floor `ε_round/(1−q)`) degenerates to R1's slack inequality in this
regime (no moving latent target ⇒ no nonzero asymptotic floor);
route R3 (joint Lyapunov `E_vis + c·‖z−z*‖²`) would need the
z-differentiability that the E3 protocol forbids claiming.

Main results:

* `alternating_round_nonincreasing` — (B4 MAIN, ROUND THEOREM,
  strict form) one full z-then-y round with an INEXACT latent: if
  the z-phase delivers `‖z_t − z*‖ ≤ η` (premise-form: contracted
  through the declared softmax-Lipschitz premise
  `hsoft : |w(z_t) − w(z*)| ≤ Lsm·η`, delivery lemma
  `LatentEnergy.latent_settle_tolerance`), the computed fields
  `L̂` of the `K(z_t)`-energy carry numerical error ≤ ε (C270
  premise), and the computed margin clears the COMPOSED slack
  `2·(ε + |S_i|·2κmax·fmax·L_sm·η)` (C270's 2ε plus C271's coupling
  bound), then the visible energy at the TRUE frozen-z* kernel
  `pairwiseEnergy B (attentionK κ w(z*) f)` STRICTLY decreases
  across the round. Composition of `guarded_energy_delta` with
  `latent_error_couples_field` via the triangle inequality — the
  frozen statements are used, not restated. Additive over C271's
  `latent_attention_guarded_drop`: the SEPARATE numerical ε on top
  of the coupling η and the round packaging.
* `alternating_zphase_one_step_error` — (B4 η-bookkeeping brick)
  one z-phase step from ANY state contracts the latent error:
  `‖latentUpdate N m G z − z*‖ ≤ (Δ/m)·‖z − z*‖` for a fixed point
  `z*` — per-round tolerances satisfy η_t ≤ q·η_{t−1}, q = Δ/m,
  WITHOUT restarting (the summability input of the R1 design).
* `alternating_round_slack_summable` — (B4 N1, C294) ROUND-ERROR
  SUMMABILITY: a round-guard slack sequence with premise-form
  geometric decay `slack (t+1) ≤ (Δ/m)·slack t` (delivered for
  the coupling part by `alternating_zphase_one_step_error`) has
  ALL partial sums bounded by the geometric budget
  `slack 0 · m/(m−Δ)`.
* `alternating_trajectory_bound` / `alternating_trajectory_
descent_budget` — (B4 N2, C294) TRAJECTORY TELESCOPING: rounds
  each dropping `d t` (premise-form) telescope to
  `E (y N) ≤ E (y 0) − Σ d t`; with a bounded-below PREMISE
  `Emin ≤ E (y t)` the total descent is budgeted by
  `E (y 0) − Emin` (the floor is a hypothesis, not a conclusion).
* `alternating_rounds_converge` — (B4 N3, C294) TERMINAL FINITE
  FORM: on a finite configuration space, strictly-decreasing
  alternating rounds terminate (length ≤ card of the energy
  image) — the C268 ranking bound reused; the unconditional
  analytic convergence stays OPEN (pinned negative).

## Honest boundaries (B4)

* PREMISE-FORM throughout: the z-phase inexactness (η, `hsoft`) and
  the numerical field error (ε) are HYPOTHESES, not conclusions;
  the softmax-Lipschitz step remains a declared premise (C271
  honesty inherited), and rejection below the slack carries no
  information (C270 honesty inherited).
* NO UNCONDITIONAL joint `(z, y)` convergence theorem exists or is
  claimed: the names `alternating_round_converges` and
  `visible_descent_joint_z` are NONEXISTENT (RootApi negative
  pins). What is proven: ONE round, strictly, under premises. The
  chain/summability follow-ups are the recorded next statements
  (N1 round chain nonincrease, N2 η_t summability, N3 bounded-below
  round decreases) — none of them claimed here.
* The latent block of a round is inexact but STATIC-TARGETED: the
  y-independence of `z*` is why no `ε_round/(1−q)` floor appears;
  if the latent energy ever becomes y-dependent, R2's small-gain
  machinery becomes necessary and this file's design must be
  revisited (design doc records the dispositions).
* C294 convergence lift (N1–N3) stays PREMISE-FORM and FINITE:
  the geometric slack decay and the per-round drops are HYPOTHESES;
  the energy floor `Emin` is a PREMISE; the terminal statement is
  the FINITE/STRICT form only (length bound via the C268 ranking
  argument). The UNCONDITIONAL analytic convergence statement
  `alternating_round_converges` STILL does not exist and stays
  OPEN (RootApi negative pin unchanged); the near-name
  `alternating_rounds_converge` (plural) is the finite terminal
  form and states termination, NOT convergence to a minimizer.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy)

/-! ## The round theorem -/
section Round

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`alternating_round_nonincreasing`** — (B4 MAIN, ROUND THEOREM,
strict form) one full z-then-y round with an inexact latent: with
the z-phase settled-state weights `w1 = w(z_t)` within `Lsm·η` of
the fixed-point weights `w2 = w(z*)` (premise-form delivery: η is
the settle tolerance of `latent_settle_tolerance`, composed through
the declared softmax-Lipschitz premise), computed fields `L̂` of the
`K(z_t)`-energy within ε of the exact ones (C270 numerical
premise), and the computed margin clearing the COMPOSED slack
`2·(ε + |S_i|·2κmax·fmax·(Lsm·η))`, the visible energy at the TRUE
frozen-z* kernel STRICTLY decreases across the round. -/
theorem alternating_round_nonincreasing [Nonempty α]
    (B : ι → α → ℝ) (κ : ι → ι → ℝ) (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η ε : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hε : 0 ≤ ε)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ)
    (herr : ∀ b, |Lhat i b - localField B (attentionK κ w1 f) y i b| ≤ ε)
    (hguard : 2 * (ε + ((Finset.univ \ {i}).card : ℝ)
        * (2 * κmax * fmax * (Lsm * η)))
      < Lhat i (y i) - Lhat i a) :
    pairwiseEnergy B (attentionK κ w2 f) (Function.update y i a)
      < pairwiseEnergy B (attentionK κ w2 f) y := by
  have hfmax : (0:ℝ) ≤ fmax := le_trans (abs_nonneg (f (Classical.arbitrary α)
    (Classical.arbitrary α))) (hf _ _)
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hLη : (0:ℝ) ≤ Lsm * η := le_trans (abs_nonneg _) (hsoft i i)
  set C : ℝ := ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η))
    with hC
  have hC0 : (0:ℝ) ≤ C :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκmax) hfmax) hLη)
  have htot : ∀ b, |Lhat i b - localField B (attentionK κ w2 f) y i b| ≤ ε + C := by
    intro b
    have h1 := herr b
    have h2 := latent_error_couples_field B κ w1 w2 f hκ hf hsoft y i b
    calc |Lhat i b - localField B (attentionK κ w2 f) y i b|
        = |(Lhat i b - localField B (attentionK κ w1 f) y i b)
            + (localField B (attentionK κ w1 f) y i b
                - localField B (attentionK κ w2 f) y i b)| := by ring_nf
      _ ≤ |Lhat i b - localField B (attentionK κ w1 f) y i b|
          + |localField B (attentionK κ w1 f) y i b
              - localField B (attentionK κ w2 f) y i b| := abs_add_le _ _
      _ ≤ ε + C := by linarith
  exact guarded_energy_delta B (attentionK κ w2 f)
    (attention_K_symmetric κ w2 f) y i a Lhat (ε + C)
    (by linarith) htot hguard

end Round

/-! ## The η-bookkeeping brick -/
section ZPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`alternating_zphase_one_step_error`** — (B4 η-bookkeeping
brick) one z-phase step contracts the latent error toward the
(y-independent, static) fixed point: for `latentUpdate N m G zstar =
zstar`, `‖latentUpdate N m G z − zstar‖ ≤ (Δ/m)·‖z − zstar‖`. This
is the summability input of the R1 design (per-round tolerance
η_t ≤ q·η_{t−1}, q = Δ/m, without restarting the settle loop); the
summable-series statement itself is NOT claimed here. -/
theorem alternating_zphase_one_step_error (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar z : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ‖latentUpdate N m G z - zstar‖ ≤ ((Δ : ℝ) / m) * ‖z - zstar‖ := by
  have h := latent_update_contraction N m G hΔ hm z zstar
  rw [hz] at h
  exact h

end ZPhase

/-! ## N1: round-error summability (geometric slack budget) -/
section SlackSummable

private theorem slack_partial_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ q * slack t) (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t
      ≤ slack 0 * (1 - q ^ N) / (1 - q) := by
  have hdec : ∀ t, slack t ≤ q ^ t * slack 0 := fun t =>
    Hagi.Probability.compounding_bound q hq0 slack hslack t
  induction N with
  | zero => simp
  | succ n ih =>
    have hqn : 0 ≤ q ^ n := pow_nonneg hq0 n
    have h1 : (0:ℝ) < 1 - q := by linarith
    have h2 := hdec n
    have h3 : (1 - q) * slack n ≤ (1 - q) * (q ^ n * slack 0) :=
      mul_le_mul_of_nonneg_left h2 h1.le
    have h5 : (0:ℝ) ≤ q ^ n * slack 0 := mul_nonneg hqn hs0
    rw [Finset.sum_range_succ]
    calc ∑ t ∈ Finset.range n, slack t + slack n
        ≤ slack 0 * (1 - q ^ n) / (1 - q) + slack n :=
            add_le_add ih (le_refl _)
      _ ≤ slack 0 * (1 - q ^ (n + 1)) / (1 - q) := by
          have h4 : q ^ (n + 1) = q ^ n * q := pow_succ q n
          rw [h4]
          field_simp
          nlinarith [hqn, h5, h3]

/-- **`alternating_round_slack_summable`** — (B4 N1, C294,
ROUND-ERROR SUMMABILITY) the composed round-guard slack with
geometric decay (premise-form `slack (t+1) ≤ (Δ/m)·slack t`; the
delivery for the C·η_t part is `alternating_zphase_one_step_error`)
has ALL partial sums bounded by the geometric-series budget
`slack 0 * m/(m−Δ)`. Premise-form: the decay is a HYPOTHESIS; the
chain from latent-error contraction to slack decay is documented,
not claimed here. -/
theorem alternating_round_slack_summable {Δ : ℕ} {m : ℝ}
    (hm : 0 < m) (hΔm : (Δ : ℝ) < m)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ ((Δ : ℝ) / m) * slack t)
    (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t ≤ slack 0 * m / (m - Δ) := by
  set q : ℝ := (Δ : ℝ) / m with hq
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (Nat.cast_nonneg _) hm.le
  have hq1 : q < 1 := by
    rw [hq]
    exact (div_lt_one hm).2 hΔm
  have hbound := slack_partial_sum hq0 hq1 slack hs0 hslack N
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have hp : (0:ℝ) < 1 - q := by linarith
  have hinner : slack 0 * (1 - q ^ N) ≤ slack 0 * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hle1 : slack 0 * (1 - q ^ N) / (1 - q)
      ≤ slack 0 * 1 / (1 - q) :=
    (div_le_div_iff₀ hp hp).2 (mul_le_mul_of_nonneg_right hinner hp.le)
  have hfinal : slack 0 * 1 / (1 - q) = slack 0 * m / (m - Δ) := by
    rw [hq]
    field_simp
  linarith [hbound, hle1, hfinal.ge]

end SlackSummable

/-! ## N2: trajectory telescoping and the descent budget -/
section Trajectory

variable {γ : Type*}

/-- **`alternating_trajectory_bound`** — (B4 N2, C294, TRAJECTORY
TELESCOPING) a trajectory of rounds `y 0, y 1, …` each satisfying
the strict-drop premise with per-round drop `d t` (premise-form)
telescopes: the final visible energy is at most the initial minus
the total drop. -/
theorem alternating_trajectory_bound {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    E (y N) ≤ E (y 0) - ∑ t ∈ Finset.range N, d t := by
  have hkey : ∀ (n : ℕ), (∀ t < n, E (y (t + 1)) ≤ E (y t) - d t) →
      E (y n) ≤ E (y 0) - ∑ t ∈ Finset.range n, d t := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : ∀ t < k, E (y (t + 1)) ≤ E (y t) - d t :=
        fun t ht => hk t (by omega)
      have hstep' := hk k (by omega)
      have hrec := ih hk'
      rw [Finset.sum_range_succ]
      have : E (y 0) - (∑ t ∈ Finset.range k, d t + d k)
          = E (y 0) - ∑ t ∈ Finset.range k, d t - d k := by ring
      rw [this]
      linarith
  exact hkey N hstep

/-- **`alternating_trajectory_descent_budget`** — (B4 N2, C294,
floor corollary) with the visible energy BOUNDED BELOW by `Emin`
(the honest floor premise — nonneg or bounded-below by
construction; a HYPOTHESIS, not a conclusion), the total descent
of a strictly-dropping trajectory is bounded: Σ drops ≤
`E (y 0) − Emin`. Combined with `alternating_round_slack_
summable`: a per-round drop `d t = c − slack t` with geometric
slack gives the cumulative descent budget `c·N − slack 0·m/(m−Δ)
≤ E (y 0) − Emin`, bounding the achievable number of guarded
rounds (remark, not a theorem — packaging the per-round premises
as a chain is the recorded next statement). -/
theorem alternating_trajectory_descent_budget {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ) (Emin : ℝ)
    (hfloor : ∀ t, Emin ≤ E (y t))
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    ∑ t ∈ Finset.range N, d t ≤ E (y 0) - Emin := by
  have hb := alternating_trajectory_bound (E := E) y d N hstep
  have hf := hfloor N
  linarith

end Trajectory

/-! ## N3: terminal statement, finite form -/
section TerminalFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **`alternating_rounds_converge`** — (B4 N3, C294, TERMINAL
FINITE FORM) on a finite configuration space, a trajectory of
alternating rounds along which the visible energy at the TRUE
frozen-z* kernel `pairwiseEnergy B (attentionK κ w f)` strictly
decreases at every pair has length at most the number of DISTINCT
energy values — the C268 ranking bound reused
(`greedy_strict_search_terminates` cited, not restated). Hence an
infinite strictly-improving alternating run CANNOT exist: the
process reaches a round where the composed guard fails (a STALL —
the honest terminal outcome; NOT a global-minimum claim).
Relation to the pinned negative: the UNCONDITIONAL analytic
convergence statement alternating_round_converges does NOT
exist and stays OPEN; this finite/strict version claims
TERMINATION only. -/
theorem alternating_rounds_converge (B : ι → α → ℝ) (κ : ι → ι → ℝ)
    (w : ι → ι → ℝ) (f : α → α → ℝ) (l : List (ι → α))
    (h : l.Pairwise (fun a b =>
      pairwiseEnergy B (attentionK κ w f) b
        < pairwiseEnergy B (attentionK κ w f) a)) :
    l.length ≤ Fintype.card (Set.image
      (pairwiseEnergy B (attentionK κ w f))
      (Set.univ : Set (ι → α))) :=
  greedy_strict_search_terminates _ l h

end TerminalFinite

/-! ## Numeric anchors (C294) -/
section Anchors

/-- ANCHOR (geometric slack sum numeric check): slack t = (1/2)^t
(q = Δ/m = 1/2, Δ = 1, m = 2): the budget is slack 0 * m/(m−Δ) = 2,
and the partial sum Σ_{t<5} (1/2)^t = 31/16 ≤ 2 through the
theorem itself. -/
example : ∑ t ∈ Finset.range 5, (1 / 2 : ℝ) ^ t ≤ 2 := by
  have h := alternating_round_slack_summable (Δ := 1) (m := 2)
    (by norm_num) (by norm_num) (fun t => (1 / 2 : ℝ) ^ t) (by norm_num)
    (fun t => by simp [pow_succ, mul_comm]) 5
  simp at h
  linarith

/-- ANCHOR (trajectory telescoping numeric check): E = 10 − t,
d = 1, N = 3: final 7 ≤ 10 − 3 through the theorem itself. -/
example : (fun t => (10 : ℝ) - t) 3
    ≤ (fun t => (10 : ℝ) - t) 0 - ∑ _t ∈ Finset.range 3, (1 : ℝ) := by
  have h := alternating_trajectory_bound (E := fun t => (10 : ℝ) - t)
    (fun t => t) (fun _ => 1) 3
    (by intro _t _; simp only [Nat.cast_succ]; linarith)
  show (10:ℝ) - 3 ≤ 10 - 0 - ∑ _t ∈ Finset.range 3, (1:ℝ)
  exact_mod_cast h

end Anchors

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`fan2`** — agreement value-coupling on `Bool`
(`f a b = −1` iff `a = b`). -/
noncomputable def fan2 : Bool → Bool → ℝ := fun a b => if a = b then -1 else 0

/-- **`yan2`** — disagreeing fixture on `Fin 2` (cell 0 ≠ cell 1). -/
noncomputable def yan2 : Fin 2 → Bool := ![true, false]

/-- Numeric anchor (Fin 2 / Bool, APPLIED through the round theorem):
with constant weights (`w1 = w2`, so the latent slack `Lsm·η = 0`),
exact fields (ε = 0) and the agreement kernel, moving cell 0 of
`![true, false]` to `false` AGREES with cell 1 and STRICTLY drops
the energy `0 → −2` — the round theorem fires on a concrete
instance, not just a norm_num identity. -/
example : pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2)
    (Function.update yan2 0 false)
    < pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 := by
  refine alternating_round_nonincreasing (κmax := 1) (fmax := 1)
    (Lsm := 0) (η := 0) (ε := 0)
    (fun _ _ => (0:ℝ))
    (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2
    (fun i j => ⟨by norm_num, le_refl _⟩)
    (fun a b => by unfold fan2; split <;> simp) (by norm_num)
    (fun i j => by simp) yan2 0 false
    (fun _ b => localField (fun _ _ => (0:ℝ))
      (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 0 b)
    (fun b => by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)
    (by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)

end Fixture

end Hagi.Model.EnergyReasoning

