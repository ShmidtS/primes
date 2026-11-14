/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.InfoCore
import Hagi.Energy.SingleCellDescent

set_option linter.style.header false

/-!
# Heat-bath kernel, focused mixture stationarity

Track E4 (addendum A9 §E4 + A9-supplement, CRAM / arXiv:2611.17309): the
Gibbs-search transition kernel as an EXPLICIT policy — the single-cell
heat-bath kernel, its detailed balance and stationarity w.r.t. the Boltzmann
density, and the focused (state-dependent) mixture.

* `heatbathWeight` — the heat-bath weight of value `a` at cell `i`:
  `softDef (fun c => −L_i(c)/T) a`, the softmax of the NEGATIVE local field
  over temperature (REUSE of `Hagi.Prelude.softDef`; no new softmax).
* `heatbathKernel` — the single-cell kernel `Q_i(y, z)`: `heatbathWeight` at
  `z i` when `z` agrees with `y` off cell `i` (a single-cell move), `0`
  otherwise. The kernel is UNCLAMPED; clamp preservation is a theorem with a
  free-cells premise, not a construction.
* `heatbath_detailed_balance` — (E4 MAIN) under symmetric `K` and `T ≠ 0`
  the kernel is reversible w.r.t. the unnormalized Boltzmann density
  `π(y) = exp(−E(y)/T)`. The proof reduces EXACTLY to the C261 identity
  `single_cell_move_energy_delta_symm` plus the off-cell localField
  invariance; the softmax normalizer cancels (both weights are evaluated at
  the same state's fields).
* `heatbath_stationary` — (E4 MAIN) reversible + row-stochastic ⇒ stationary
  (`reversible_stationary`), via `heatbathKernel_rowsum` (the map
  `a ↦ y^{i←a}` reindexes the supported row: `Finset.sum_bij`).
* `mixture_reversible` / `focused_mixture_stationary` — (E4 MAIN) the focused
  selection `Q = Σ_i w(y)_i · Q_i` is reversible/stationary under TWO
  explicit load-bearing premises: SUPPORT (each `Q_i` only moves cell `i`)
  and INVARIANCE (`w(y^{i←a})_i = w(y)_i` — the selection weight of cell `i`
  is invariant under moves of cell `i`; state-dependence through OTHER cells,
  frozen latents, givens or a fixed schedule is fine).
* `focused_heatbath_mixture_stationary` — the focused-Gibbs corollary: the
  heat-bath family satisfies SUPPORT structurally, so only `hK`, `T ≠ 0`,
  INVARIANCE and `Σ_i w(y)_i = 1` remain.
* `focused_mixture_preserves_givens` — clamps preserved (premise-form): if
  the selection weights vanish on given cells (`∀ y, w y i = 0` for given
  `i`), the mixture output preserves every given value EXACTLY.

## Honest boundaries (A9 'not to adopt' list + supplement §E4)

* STATIONARITY ≠ MONOTONICITY: `T > 0` can RAISE energy — the heat-bath
  weight of a HIGHER-energy value is strictly positive (fixture witness
  below: weight `exp(−3)/(1 + exp(−3)) > 0` for the worse value). No descent
  claim is made about the kernel or the mixture.
* The A9-supplement phrase "state-dependent mixture preserves stationarity"
  is FALSE as an unconditional statement (two-state flip-vs-stay
  counterexample); the INVARIANCE premise here is exactly what the counterexample
  violates, and it is documented as load-bearing (RootApi-пин: имя
  `focused_mixture_stationarity_without_invariance` отсутствует).
* The stationarity statements are about the unnormalized density on a
  FINITE configuration space; no measure-theoretic packaging, no mixing-time
  or convergence-rate claim.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy Hagi.Prelude

section Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Kernel row condition (private): `z` agrees with `y` off cell `i`,
i.e. `z` is the single-cell move `y^{i←(z i)}`. -/
private def heatbathOffCellCond (y : ι → α) (i : ι) (z : ι → α) : Prop :=
  ∀ j, j ≠ i → z j = y j

/-- The heat-bath weight of value `a` at cell `i` from state `y`: the
softmax (`softDef` reuse) of the NEGATIVE local field over temperature,
`exp(−L_i(a)/T) / Σ_c exp(−L_i(c)/T)` with `L_i` the C261 `localField`. -/
noncomputable def heatbathWeight (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (a : α) : ℝ :=
  softDef (fun c => -(localField B K y i c) / T) a

open Classical in
/-- The single-cell heat-bath kernel `Q_i(y, z)`: `heatbathWeight` at `z i`
when `z` is a single-cell move of `y` at cell `i`, `0` otherwise
(the supported row is exactly `{y^{i←a} : a ∈ α}`). -/
noncomputable def heatbathKernel (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) : ℝ :=
  if heatbathOffCellCond y i z then heatbathWeight B K T y i (z i) else 0

/-- Reversibility (detailed balance) of a kernel `Q` w.r.t. a density `π`
on the finite configuration space. -/
def kernelReversible (π : (ι → α) → ℝ) (Q : (ι → α) → (ι → α) → ℝ) : Prop :=
  ∀ y z, π y * Q y z = π z * Q z y

/-- Stationarity of a kernel `Q` w.r.t. a density `π`:
`Σ_y π y * Q y z = π z` for every `z`. -/
def kernelStationary (π : (ι → α) → ℝ) (Q : (ι → α) → (ι → α) → ℝ) : Prop :=
  ∀ z, ∑ y, π y * Q y z = π z

/-- The unnormalized Boltzmann density `π(y) = exp(−E(y)/T)` of the
C261 `pairwiseEnergy`. -/
noncomputable def boltzmannDensity (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) : ℝ :=
  Real.exp (-(pairwiseEnergy B K y) / T)

/-- The focused (state-dependent) mixture kernel
`Q(y, z) = Σ_i w(y)_i * Q_i(y, z)` — the FocusedSearch selection policy of
A9-supplement §E4. -/
noncomputable def focusedMixture (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (y z : ι → α) : ℝ :=
  ∑ i, w y i * Q i y z

end Definitions

section Weight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The local field only depends on the state off the moved cell: if `z`
agrees with `y` everywhere except (possibly) at `i`, then `L^z_i = L^y_i`
(the off-cell couplings `K i j · (y j)` are untouched by an `i`-move). -/
theorem localField_kcond (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y z : ι → α) (i : ι) (a : α)
    (h : ∀ j, j ≠ i → z j = y j) :
    localField B K z i a = localField B K y i a := by
  simp only [localField]
  refine congrArg (B i a + ·) ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (by simpa using hj)]

omit [DecidableEq α] in
/-- Heat-bath weights are strictly positive (softmax positivity). -/
theorem heatbathWeight_pos (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) (a : α) :
    0 < heatbathWeight B K T y i a :=
  softDef_pos _ a

omit [DecidableEq α] in
/-- Heat-bath weights normalize: `Σ_a w_i(a) = 1` (softmax normalization). -/
theorem heatbathWeight_sum_one (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (y : ι → α) (i : ι) :
    ∑ a, heatbathWeight B K T y i a = 1 :=
  softDef_sum_one _

end Weight

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] in
/-- The kernel is nonnegative: `0 ≤ Q_i(y, z)` (a probability weight or
zero). -/
theorem heatbathKernel_nonneg (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) : 0 ≤ heatbathKernel B K T i y z := by
  classical
  unfold heatbathKernel
  split
  · exact le_of_lt (heatbathWeight_pos B K T y i (z i))
  · norm_num

omit [DecidableEq α] in
omit [DecidableEq α] [Nonempty α] in
/-- Kernel support (clamp premise-form): a nonzero transition `Q_i(y, z) ≠ 0`
forces `z` to be the single-cell move `y^{i←(z i)}` — every OTHER cell `j ≠ i`
is preserved EXACTLY. This is the structural SUPPORT premise consumed by
`mixture_reversible`. -/
theorem heatbathKernel_supported (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y z : ι → α) (h : heatbathKernel B K T i y z ≠ 0) :
    z = Function.update y i (z i) := by
  classical
  by_cases hcond : heatbathOffCellCond y i z
  · unfold heatbathKernel at h
    simp only [hcond, ite_true] at h
    funext j
    by_cases hji : j = i
    · subst hji; simp [Function.update_self]
    · rw [Function.update_of_ne hji]; exact hcond j hji
  · unfold heatbathKernel at h
    simp only [hcond, ite_false] at h
    exact absurd rfl h

omit [DecidableEq α] in
/-- Every kernel row sums to ONE, with NO premises: the map
`a ↦ y^{i←a}` is a bijection from `α` onto the supported row, and the
weights normalize (`heatbathWeight_sum_one`). -/
theorem heatbathKernel_rowsum (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (T : ℝ) (i : ι) (y : ι → α) :
    ∑ z, heatbathKernel B K T i y z = 1 := by
  classical
  have h1 : ∑ z, heatbathKernel B K T i y z
      = ∑ z ∈ Finset.univ.filter (fun z => heatbathOffCellCond y i z),
          heatbathWeight B K T y i (z i) := by
    simp only [heatbathKernel]
    rw [Finset.sum_filter]
  rw [h1]
  refine (Finset.sum_bij (fun z _ => z i)
    (fun z _ => Finset.mem_univ _)
    (fun z₁ h₁ z₂ h₂ heq => by
      funext j
      by_cases hji : j = i
      · subst hji; simpa using heq
      · rw [(Finset.mem_filter.mp h₁).2 j hji,
          (Finset.mem_filter.mp h₂).2 j hji])
    (fun a _ => ⟨Function.update y i a,
      Finset.mem_filter.mpr ⟨Finset.mem_univ (Function.update y i a),
        fun j hj => Function.update_of_ne hj a y⟩,
      Function.update_self i a y⟩)
    (fun z _ => rfl)).trans (heatbathWeight_sum_one B K T y i)

end Rows

section DetailedBalance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN) Heat-bath detailed balance: under symmetric `K`
(`K_ij(a,b) = K_ji(b,a)`, the CRAM `W = sym(K)`) and `T ≠ 0`, the
single-cell kernel is REVERSIBLE w.r.t. the unnormalized Boltzmann density
`π(y) = exp(−E(y)/T)`. The proof is exactly the C261 delta identity
`E(y^{i←a}) − E(y) = L_i(a) − L_i(y_i)` (all non-`i` partition terms cancel)
plus the off-cell localField invariance; the softmax normalizer cancels
because both weights are evaluated at the SAME state's fields. `T ≠ 0` is
the only temperature premise. -/
theorem heatbath_detailed_balance (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0)
    (i : ι) (y z : ι → α) :
    boltzmannDensity B K T y * heatbathKernel B K T i y z
      = boltzmannDensity B K T z * heatbathKernel B K T i z y := by
  classical
  by_cases hc : heatbathOffCellCond y i z
  · simp only [heatbathKernel, hc, ite_true]
    have hc' : heatbathOffCellCond z i y :=
      fun j hj => (hc j hj).symm
    simp only [hc', ite_true]
    have hzu : z = Function.update y i (z i) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · rw [Function.update_of_ne hji]; exact hc j hji
    have hLz : ∀ c, localField B K z i c = localField B K y i c :=
      fun c => localField_kcond B K y z i c hc
    have hd := single_cell_move_energy_delta_symm B K hK y i (z i)
    have hEz : pairwiseEnergy B K z
        = pairwiseEnergy B K (Function.update y i (z i)) :=
      congrArg (pairwiseEnergy B K) hzu
    have hw : heatbathWeight B K T z i (y i)
        = heatbathWeight B K T y i (y i) := by
      simp only [heatbathWeight, hLz]
    rw [hw]
    simp only [heatbathWeight, softDef, boltzmannDensity]
    have key2 :
        Real.exp (-(pairwiseEnergy B K y) / T)
            * Real.exp (-(localField B K y i (z i)) / T)
        = Real.exp (-(pairwiseEnergy B K z) / T)
            * Real.exp (-(localField B K y i (y i)) / T) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp
      linarith
    rw [mul_div_assoc', mul_div_assoc', key2]
  · simp only [heatbathKernel, hc, ite_false]
    obtain ⟨j, hj⟩ := not_forall.mp hc
    have hji : j ≠ i := fun he => hj (fun hne => absurd he hne)
    have hjz : z j ≠ y j := fun heq => hj (fun _ => heq)
    have hne : ¬ heatbathOffCellCond z i y := fun h => hjz (h j hji).symm
    simp only [hne, ite_false]
    ring

omit [DecidableEq α] [Nonempty α] in
/-- Reversible + row-stochastic ⇒ stationary: `Σ_y π y * Q y z`
`= Σ_y π z * Q z y = π z · 1`. -/
theorem reversible_stationary (π : (ι → α) → ℝ)
    (Q : (ι → α) → (ι → α) → ℝ) (hQ : kernelReversible π Q)
    (hrow : ∀ y, ∑ z, Q y z = 1) : kernelStationary π Q := by
  intro z
  calc ∑ y, π y * Q y z = ∑ y, π z * Q z y :=
        Finset.sum_congr rfl fun y _ => hQ y z
    _ = π z * ∑ y, Q z y :=
        (Finset.mul_sum Finset.univ (fun y => Q z y) (π z)).symm
    _ = π z * 1 := by rw [hrow z]
    _ = π z := by ring

omit [DecidableEq α] in
/-- (E4 MAIN) Heat-bath stationarity: the single-cell heat-bath kernel
preserves the Boltzmann density — detailed balance (`heatbath_detailed_balance`)
plus row-stochasticity (`heatbathKernel_rowsum`) via
`reversible_stationary`. STATIONARITY ≠ MONOTONICITY: at `T > 0` the kernel
assigns strictly positive weight to HIGHER-energy values (fixture witness
below); no descent claim is made. -/
theorem heatbath_stationary (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (hK : ∀ i j a b, K i j a b = K j i b a) (hT : T ≠ 0) (i : ι) :
    kernelStationary (boltzmannDensity B K T) (heatbathKernel B K T i) :=
  reversible_stationary _ _
    (fun y z => heatbath_detailed_balance B K hK hT i y z)
    (fun y => heatbathKernel_rowsum B K T i y)

end DetailedBalance

section Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN, part a) The focused mixture of reversible SINGLE-CELL kernels
is reversible under the SUPPORT premise (`Q_i(y,z) ≠ 0 ⇒ z = y^{i←(z i)}`:
each kernel only moves its own cell) and the INVARIANCE premise
(`w(y^{i←a})_i = w(y)_i`: the selection weight of cell `i` is invariant under
moves of cell `i`). Both premises are LOAD-BEARING: without INVARIANCE the
supplement's "state-dependent mixture preserves stationarity" is FALSE
(two-state flip-vs-stay counterexample), and without SUPPORT the invariance
premise would have to range over arbitrary moves. -/
theorem mixture_reversible (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (π : (ι → α) → ℝ)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hQrev : ∀ i, kernelReversible π (Q i)) :
    kernelReversible π (focusedMixture w Q) := by
  intro y z
  simp only [focusedMixture, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hz : Q i z y = 0
  · have h0 : π y * Q i y z = 0 := by
      rw [hQrev i y z, hz, mul_zero]
    rw [mul_left_comm (π y), h0, mul_zero, mul_left_comm (π z), hz,
      mul_zero, mul_zero]
  · have hy : y = Function.update z i (y i) := hQsupp i z y hz
    have hw : w y i = w z i := by rw [hy]; exact hwinv i z (y i)
    rw [hw, mul_left_comm (π y), hQrev i y z]
    ring

omit [DecidableEq α] [Nonempty α] in
/-- Mixture rows sum to one: `Σ_i w(y)_i = 1` plus per-kernel
row-stochasticity. -/
theorem mixture_rowsum (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (y : ι → α)
    (hw : ∀ y', ∑ i, w y' i = 1) (hrow : ∀ i y', ∑ z, Q i y' z = 1) :
    ∑ z, focusedMixture w Q y z = 1 := by
  calc ∑ z, focusedMixture w Q y z
      = ∑ z, ∑ i, w y i * Q i y z := Finset.sum_congr rfl fun z _ => rfl
    _ = ∑ i, ∑ z, w y i * Q i y z := Finset.sum_comm
    _ = ∑ i, w y i * ∑ z, Q i y z :=
        Finset.sum_congr rfl fun i _ =>
          (Finset.mul_sum Finset.univ (fun z => Q i y z) (w y i)).symm
    _ = ∑ i, w y i * 1 :=
        Finset.sum_congr rfl fun i _ => by rw [hrow i y]
    _ = ∑ i, w y i := Finset.sum_congr rfl fun i _ => mul_one _
    _ = 1 := hw y

omit [DecidableEq α] [Nonempty α] in
/-- (E4 MAIN) Focused mixture stationarity: `Q = Σ_i w(y)_i · Q_i` with
`w ≥ 0`-free normalization `Σ_i w(y)_i = 1` preserves `π` under the SUPPORT,
INVARIANCE, reversibility and row-sum premises (see `mixture_reversible`
for why the premises are load-bearing). STATIONARITY ≠ MONOTONICITY:
the mixture can RAISE energy at `T > 0` — no descent claim is made. -/
theorem focused_mixture_stationary (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (π : (ι → α) → ℝ)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hQrev : ∀ i, kernelReversible π (Q i))
    (hrow : ∀ i y', ∑ z, Q i y' z = 1)
    (hw : ∀ y', ∑ i, w y' i = 1) :
    kernelStationary π (focusedMixture w Q) :=
  reversible_stationary π _
    (mixture_reversible w Q π hQsupp hwinv hQrev)
    (fun y => mixture_rowsum w Q y hw hrow)

omit [DecidableEq α] in
/-- (E4 MAIN, corollary) The FOCUSED-GIBBS-SEARCH policy — a state-dependent
mixture of single-cell heat-bath kernels — preserves the Boltzmann density.
The heat-bath family satisfies SUPPORT structurally
(`heatbathKernel_supported`), so only `hK`, `T ≠ 0`, INVARIANCE of the
selection weights and `Σ_i w(y)_i = 1` remain as premises. -/
theorem focused_heatbath_mixture_stationary (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (hK : ∀ i j a b, K i j a b = K j i b a)
    (hT : T ≠ 0) (w : (ι → α) → ι → ℝ)
    (hwinv : ∀ (i : ι) (y : ι → α) (a : α),
      w (Function.update y i a) i = w y i)
    (hw : ∀ y', ∑ i, w y' i = 1) :
    kernelStationary (boltzmannDensity B K T)
      (focusedMixture w (fun i => heatbathKernel B K T i)) :=
  focused_mixture_stationary w _ _
    (fun i y z h => heatbathKernel_supported B K T i y z h)
    hwinv
    (fun i y z => heatbath_detailed_balance B K hK hT i y z)
    (fun i y => heatbathKernel_rowsum B K T i y)
    hw

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Clamps preserved (premise-form): if the selection weights VANISH on
given cells (`hFree` — the free-cells-only premise) and the kernels are
single-cell kernels, then a NONZERO mixture transition `z` from `y`
preserves every given cell value EXACTLY (`z i = y i` for `givens i = some
a`). The premise is the honest form of "the sampler never touches clues";
it is not baked into the kernel. -/
theorem focused_mixture_preserves_givens (w : (ι → α) → ι → ℝ)
    (Q : ι → (ι → α) → (ι → α) → ℝ) (givens : ι → Option α)
    (hQsupp : ∀ (i : ι) (y z : ι → α), Q i y z ≠ 0 →
      z = Function.update y i (z i))
    (hFree : ∀ (i : ι) (a : α) (y : ι → α),
      givens i = some a → w y i = 0)
    (y z : ι → α) (hQ : focusedMixture w Q y z ≠ 0)
    (i : ι) (a : α) (hg : givens i = some a) :
    z i = y i := by
  classical
  by_contra hne
  unfold focusedMixture at hQ
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hwj : w y j ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hj; exact hj rfl
  have hzne : Q j y z ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hj; exact hj rfl
  have hnone : ∀ b : α, givens j ≠ some b :=
    fun b hgb => hwj (hFree j b y hgb)
  have hij : i ≠ j := by
    intro he
    rw [he] at hg
    exact hnone a hg
  have hzj : z = Function.update y j (z j) := hQsupp j y z hzne
  apply hne
  rw [hzj, Function.update_of_ne hij]

end Mixture

section Fixture
/-! ## Fin 2 × Bool fixture (Bex/Kex/xtt carriers from C260) -/

open Hagi.Energy

private theorem Kex_symm :
    ∀ (i j : Fin 2) (a b : Bool), Kex i j a b = Kex j i b a := by
  intro i j a b
  simp only [Kex, Bool.and_comm]
  split_ifs <;> ring

/-- Numeric anchor: `L_0(f) = 0`, `L_0(t) = 3` at `xtt = (t,t)` (C260
anchors `E(t,t) = 5`, `E(f,t) = 2`, so the C261 delta identity gives
`2 − 5 = 0 − 3`), hence the heat-bath weight of moving cell `0` to `f` at
`T = 1` is `1/(1 + exp(−3))`. -/
example : heatbathKernel Bex Kex 1 0 xtt (Function.update xtt 0 false)
      = 1 / (1 + Real.exp (-(3 : ℝ))) := by
  classical
  simp only [heatbathKernel, heatbathOffCellCond, heatbathWeight, softDef]
  have hLt : localField Bex Kex xtt 0 true = 3 := by
    simp only [localField, xtt, Bex, Kex]
    norm_num
  have hLf : localField Bex Kex xtt 0 false = 0 := by
    simp only [localField, xtt, Bex, Kex]
    norm_num
  have hL : ∀ c : Bool, localField Bex Kex xtt 0 c
      = (if c then (3 : ℝ) else 0) := by
    intro c
    cases c
    · exact hLf
    · exact hLt
  simp only [hL]
  norm_num
  linarith [Real.exp_pos (-(3 : ℝ))]

/-- STATIONARITY ≠ MONOTONICITY witness: at `T = 1` the heat-bath weight of
the HIGHER-energy value `t` (local field `3` vs `0`) is strictly positive —
the kernel can RAISE energy, and no descent claim is made. -/
example : 0 < heatbathWeight Bex Kex 1 xtt 0 true := by
  exact heatbathWeight_pos Bex Kex 1 xtt 0 true

/-- Detailed balance on the fixture, by the general theorem (Fin 2 × Bool,
`T = 1`, every pair of configurations). -/
example (y z : Fin 2 → Bool) :
    boltzmannDensity Bex Kex 1 y * heatbathKernel Bex Kex 1 0 y z
      = boltzmannDensity Bex Kex 1 z * heatbathKernel Bex Kex 1 0 z y :=
  heatbath_detailed_balance Bex Kex Kex_symm one_ne_zero 0 y z

/-- Row sums on the fixture: the kernel from `(t,t)` at cell `0`, `T = 1`,
is a probability row. -/
example : ∑ z, heatbathKernel Bex Kex 1 0 xtt z = 1 :=
  heatbathKernel_rowsum Bex Kex 1 0 xtt

end Fixture

end Hagi.Model.EnergyReasoning
