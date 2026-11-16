/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Math.Info.InfoCore
import Hagi.Energy.SingleCellDescent
import Hagi.Model.EnergyReasoning.EnergySearch

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
