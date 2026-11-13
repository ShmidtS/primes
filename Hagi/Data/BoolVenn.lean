import Mathlib.Tactic
import Hagi.Core.Hadamard

/-!
# Boolean Venn lattice: the 16 two-variable boolean functions

Track B7 (master plan v3 addendum A4), C242. Every `Bool → Bool → Bool`
function is a Venn mask: a lookup `Fin 4 → Bool` indexed by the atom
(active conjunction) of its input (`.vennBool`, `.venn_universal`).
All 16 functions carry the structure of the four-atom boolean lattice:
rank histogram `1-4-6-4-1` by number of active atoms (`.rank_histogram`),
complement-mask De Morgan involution on the SAME inputs
(`.de_morgan`, `.de_morgan_involution` — the negated-inputs variant is
FALSE: the atom index of negated inputs is `3 - k`, not `k`), and
exactly 32 ORIENTED Hasse cover edges (Hamming distance 1 AND strictly
increasing rank, `.hasse_edges`; the naive un-oriented count is 64).

Everything here is `decide`-level on the Bool carrier. The ReLU-neuron
realization of the same lattice and its certified-exact head live in
`Hagi.Model.Logic.VennHead`.

C251 additions (A8 F4): the `H₄` role correction — the mask ↔
truth-table identification on the four atoms is the IDENTITY
(`mask_truth_table_identity`) while the Walsh–Hadamard matrix
`vennWalsh` (the `Hagi.Core.sylvester` order-four matrix reindexed
by atom) is the spectrum transform, its own inverse up to the factor
four (`vennWalsh_sq`), with `(1/2) • vennWalshReal` orthonormal —
and the single-atom choice-CE floor block: the softmax probability
of any mask under the log-linear single-atom head is capped at one
eighth (`qAtom_le`), so the mean CE is at least `log 8` for every
parameterization and mask (`singleAtomCE_floor`), the infimum is
exactly `log 8` (`singleAtomCE_tight`), the adversarial worst case
is at least `log 16` (`singleAtomCE_minimax`), and `sign(θ > 0)`
still recovers every mask (`sign_recover`).
-/

namespace Hagi.Data.BoolVenn

/-- Atom index of a Bool input pair (order: `tt,tt`=0, `tt,ff`=1,
`ff,tt`=2, `ff,ff`=3). -/
def atomIdx (a b : Bool) : Fin 4 :=
  if a then (if b then 0 else 1) else (if b then 2 else 3)

/-- Venn evaluation: a mask is a truth table, evaluation is lookup at
the atom index. -/
def vennBool (m : Fin 4 → Bool) (a b : Bool) : Bool := m (atomIdx a b)

/-- Universality: every two-variable Bool function IS a Venn mask
(16 functions × 4 inputs = 64 cases, constructor-level). -/
theorem venn_universal (f : Bool → Bool → Bool) :
    ∃ m : Fin 4 → Bool, ∀ a b, vennBool m a b = f a b := by
  refine ⟨![f true true, f true false, f false true, f false false], ?_⟩
  intro a b
  cases a <;> cases b <;> rfl

/-- Rank of a mask: number of active atoms. -/
def maskRank (m : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k)).card

/-- Rank histogram `1-4-6-4-1`: the binomial counts `C(4,r)` of the
sixteen masks by rank (all 16 masks enumerated). -/
theorem rank_histogram (r : Fin 5) :
    (Finset.univ.filter (fun m : Fin 4 → Bool => maskRank m = (r : ℕ))).card
      = ![1, 4, 6, 4, 1] r := by
  fin_cases r <;> decide

/-- Mask complement (flip every atom). -/
def mcomp (m : Fin 4 → Bool) : Fin 4 → Bool := fun k => !m k

/-- De Morgan: complementing the mask negates the function on the SAME
inputs (the lattice involution; NOT the negated-inputs variant, which
is false — the atom index of negated inputs is `3 - k`). -/
theorem de_morgan :
    ∀ (m : Fin 4 → Bool) (a b : Bool),
      vennBool (mcomp m) a b = !(vennBool m a b) := by
  decide

/-- De Morgan involution: double complement is identity. -/
theorem de_morgan_involution :
    ∀ m : Fin 4 → Bool, mcomp (mcomp m) = m := by
  decide

/-- Hamming distance between masks. -/
def hamming (m m' : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k ≠ m' k)).card

/-- Exactly 32 Hasse cover edges: ordered mask pairs at Hamming
distance 1 with strictly increasing rank (orientation is essential —
the un-oriented Hamming-1 count is 64). -/
theorem hasse_edges :
    (Finset.univ.filter (fun p : (Fin 4 → Bool) × (Fin 4 → Bool) =>
      hamming p.1 p.2 = 1 ∧ maskRank p.1 < maskRank p.2)).card
      = 32 := by
  decide

/-! ## C251: the `H₄` role correction (identity vs spectrum transform) -/

open Hagi.Core
open scoped Matrix

/-- Bit decomposition of an atom index (order matches `atomIdx`). -/
def atomBits (k : Fin 4) : Fin 2 → ZMod 2 :=
  fun i => if i = 0 then ((k.val % 2 : ℕ) : ZMod 2)
    else ((k.val / 2 : ℕ) : ZMod 2)

/-- Input pair of an atom index (inverse of `atomIdx`). -/
def atomBools : Fin 4 → Bool × Bool :=
  ![(true, true), (true, false), (false, true), (false, false)]

theorem atomIdx_atomBools (k : Fin 4) :
    atomIdx (atomBools k).1 (atomBools k).2 = k := by
  fin_cases k <;> decide

/-- The mask ↔ truth-table identification on the four atoms is the
IDENTITY: reading the mask as a truth table over its own atoms
returns the mask (the `I₄` role — the Hadamard matrix is NOT this
map, it is the spectrum transform `vennWalsh` below). -/
theorem mask_truth_table_identity (m : Fin 4 → Bool) :
    (fun k => vennBool m (atomBools k).1 (atomBools k).2) = m := by
  funext k
  simp only [vennBool, atomIdx_atomBools]

/-- The Walsh–Hadamard matrix on the Venn atoms: `H₄` indexed by the
atom index, i.e. the `Hagi.Core.sylvester` order-four matrix read
through `atomBits` (character `chi2` of the atom-bit dot product).
This is the truth-table ↔ character-spectrum transform, NOT the
mask ↔ truth-table identification (that one is the identity above). -/
def vennWalsh : Matrix (Fin 4) (Fin 4) ℤ :=
  fun k l => chi2 (∑ i, atomBits k i * atomBits l i)

theorem vennWalsh_symm : vennWalshᵀ = vennWalsh := by
  ext k l
  simp only [Matrix.transpose_apply, vennWalsh]
  exact congrArg chi2
    (Finset.sum_congr rfl fun i _ => mul_comm _ _)

/-- Spectrum-transform inversion: `H₄ * H₄ = 4 • 1` — the Walsh
transform on the four atoms is its own inverse up to the factor
four (twice the orthonormal `(1/2) • vennWalshReal` matrix). -/
theorem vennWalsh_sq : vennWalsh * vennWalsh = 4 • 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;> decide

/-- `H₄ * H₄ᵀ = 4 • 1` — the `Hagi.Core.sylvester_mul_transpose`
instance on the atom index. -/
theorem vennWalsh_mul_transpose : vennWalsh * vennWalshᵀ = 4 • 1 := by
  rw [vennWalsh_symm]; exact vennWalsh_sq

/-- Real cast of the atom Hadamard matrix. -/
def vennWalshReal : Matrix (Fin 4) (Fin 4) ℝ :=
  vennWalsh.map (algebraMap ℤ ℝ)

theorem vennWalshReal_mul_transpose :
    vennWalshReal * vennWalshRealᵀ = ((4 : ℝ) • 1) := by
  have h1 : vennWalshReal * vennWalshRealᵀ
      = (vennWalsh * vennWalshᵀ).map (algebraMap ℤ ℝ) := by
    rw [vennWalshReal, ← Matrix.transpose_map, ← Matrix.map_mul]
  rw [h1, vennWalsh_mul_transpose]
  ext k l
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  split <;> simp

/-- `H₄ / 2` is orthonormal (Core `smul_orthonormal` with `c = 1/2`,
`c * c * 4 = 1`) — the `Hagi.Core.hadamardOrthonormal_mul_transpose`
instance on the atom index. -/
theorem vennWalshOrthonormal :
    ((1 / 2 : ℝ) • vennWalshReal) * ((1 / 2 : ℝ) • vennWalshReal)ᵀ = 1 := by
  exact smul_orthonormal vennWalshReal_mul_transpose (by norm_num)

/-! ## C251: 16-class CE floor on single-atom batches

The log-linear choice head of `Hagi.Contracts.LogicChoiceCert` on a
single-atom input `b` (only atom `b` hot) scores a candidate mask
`m'` by the logit `θ b * m'(b)` — one parameter per atom. The
statements below are scoped to exactly this head; unrestricted
predictors are not covered. -/

/-- `{0,1}` value of a mask entry. -/
def vennBit (m : Fin 4 → Bool) (j : Fin 4) : ℝ := if m j then 1 else 0

/-- Denominator identity: the 16 mask logits `θ b * m'(b)` split
into eight masks with a hot atom and eight with a cold one. -/
theorem sum_exp_vennBit (θ : Fin 4 → ℝ) (b : Fin 4) :
    ∑ m' : Fin 4 → Bool, Real.exp (θ b * vennBit m' b)
      = 8 * Real.exp (θ b) + 8 := by
  classical
  have hcardT : (Finset.univ.filter
      (fun m' : Fin 4 → Bool => m' b = true)).card = 8 := by
    fin_cases b <;> decide
  have hcardF : (Finset.univ.filter
      (fun m' : Fin 4 → Bool => ¬m' b = true)).card = 8 := by
    fin_cases b <;> decide
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4 → Bool))
    (fun m' : Fin 4 → Bool => m' b = true)
    (fun m' => Real.exp (θ b * vennBit m' b))
  rw [← hsplit]
  have h1 : ∀ m' ∈ Finset.univ.filter
      (fun m' : Fin 4 → Bool => m' b = true),
      Real.exp (θ b * vennBit m' b) = Real.exp (θ b) := by
    intro m' hm'
    rw [Finset.mem_filter] at hm'
    simp only [vennBit, hm'.2, ite_true, mul_one]
  have h2 : ∀ m' ∈ Finset.univ.filter
      (fun m' : Fin 4 → Bool => ¬m' b = true),
      Real.exp (θ b * vennBit m' b) = 1 := by
    intro m' hm'
    rw [Finset.mem_filter] at hm'
    rw [vennBit, ite_eq_right hm'.2, mul_zero]
    norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
    Finset.sum_const, Finset.sum_const, hcardT, hcardF]
  norm_num

/-- Softmax probability of mask `m` on the single-atom input `b`
under the log-linear choice head with atom parameter `θ b`. -/
noncomputable def qAtom (θ : Fin 4 → ℝ) (b : Fin 4) (m : Fin 4 → Bool) : ℝ :=
  Real.exp (θ b * vennBit m b) / (8 * Real.exp (θ b) + 8)

/-- Bridge: `qAtom` is exactly the softmax of the mask logits on the
single-atom input (denominator identity `sum_exp_vennBit`). -/
theorem qAtom_smul_denom (θ : Fin 4 → ℝ) (b : Fin 4) (m : Fin 4 → Bool) :
    qAtom θ b m * ∑ m' : Fin 4 → Bool, Real.exp (θ b * vennBit m' b)
      = Real.exp (θ b * vennBit m b) := by
  rw [qAtom, sum_exp_vennBit]
  field_simp

theorem qAtom_pos (θ : Fin 4 → ℝ) (b : Fin 4) (m : Fin 4 → Bool) :
    0 < qAtom θ b m := by
  unfold qAtom
  positivity

/-- The cap: the correct class never exceeds `1/8` — the eight masks
sharing its atom side tie at the same logit, so at best the softmax
splits that side's mass seven ways against it. -/
theorem qAtom_le (θ : Fin 4 → ℝ) (b : Fin 4) (m : Fin 4 → Bool) :
    qAtom θ b m ≤ 1 / 8 := by
  have hden : (0 : ℝ) < 8 * Real.exp (θ b) + 8 := by positivity
  have hprod : (1 : ℝ) / 8 * (8 * Real.exp (θ b) + 8)
      = Real.exp (θ b) + 1 := by field_simp
  rw [qAtom, div_le_iff₀ hden, hprod]
  by_cases hm : m b
  · rw [vennBit, ite_eq_left hm, mul_one]
    linarith
  · rw [vennBit, ite_eq_right hm, mul_zero, Real.exp_zero]
    nlinarith [Real.exp_pos (θ b)]

/-- Mean single-atom choice-CE of mask `m` under the log-linear head
(the 16-class CE of a batch of four single-atom inputs, one per
atom, all labeled with the mask `m`). -/
noncomputable def singleAtomCE (m : Fin 4 → Bool) (θ : Fin 4 → ℝ) : ℝ :=
  -(1 / 4) * ∑ b, Real.log (qAtom θ b m)

/-- Per-example floor: every single-atom example alone already pays
`log 8`. -/
theorem singleAtomCE_example_floor (θ : Fin 4 → ℝ) (b : Fin 4)
    (m : Fin 4 → Bool) :
    Real.log 8 ≤ -Real.log (qAtom θ b m) := by
  have h1 : Real.log (qAtom θ b m) ≤ Real.log (1 / 8) :=
    Real.log_le_log (qAtom_pos θ b m) (qAtom_le θ b m)
  have h2 : Real.log (1 / 8) = -Real.log 8 := by
    rw [one_div, Real.log_inv]
  linarith

/-- The A8 floor, verified pointwise (stronger than worst-case): for
EVERY parameterization and EVERY mask the mean single-atom CE is at
least `log 8` — the probability cap `qAtom_le` leaves no escape. -/
theorem singleAtomCE_floor (m : Fin 4 → Bool) (θ : Fin 4 → ℝ) :
    Real.log 8 ≤ singleAtomCE m θ := by
  have h : ∑ b, Real.log (qAtom θ b m) ≤ 4 * Real.log (1 / 8) := by
    have h1 := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) =>
      Real.log_le_log (qAtom_pos θ b m) (qAtom_le θ b m))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    norm_num at h1
    exact h1
  have hlog8 : Real.log (1 / 8) = -Real.log 8 := by
    rw [one_div, Real.log_inv]
  rw [hlog8] at h
  unfold singleAtomCE
  linarith

/-- The adversarial mask: cold exactly where the parameter is hot. -/
noncomputable def worstMask (θ : Fin 4 → ℝ) : Fin 4 → Bool :=
  fun b => θ b ≤ 0

theorem vennBit_worstMask (θ : Fin 4 → ℝ) (b : Fin 4) :
    vennBit (worstMask θ) b = if θ b ≤ 0 then 1 else 0 := by
  unfold worstMask vennBit
  by_cases hb : θ b ≤ 0 <;> simp [hb]

theorem qAtom_worst_le (θ : Fin 4 → ℝ) (b : Fin 4) :
    qAtom θ b (worstMask θ) ≤ 1 / 16 := by
  have hden : (0 : ℝ) < 8 * Real.exp (θ b) + 8 := by positivity
  have hprod : (1 : ℝ) / 16 * (8 * Real.exp (θ b) + 8)
      = Real.exp (θ b) / 2 + 1 / 2 := by
    field_simp
    norm_num
  rw [qAtom, vennBit_worstMask, div_le_iff₀ hden, hprod]
  by_cases hb : θ b ≤ 0
  · rw [ite_eq_left hb, mul_one]
    have h1 : Real.exp (θ b) ≤ 1 := by
      have := Real.exp_le_exp.2 hb
      simpa using this
    linarith
  · rw [ite_eq_right hb, mul_zero, Real.exp_zero]
    have h1 : (1 : ℝ) ≤ Real.exp (θ b) := by
      have := Real.exp_le_exp.2 (by linarith : (0 : ℝ) ≤ θ b)
      simpa using this
    linarith

/-- CORRECTION of the A8 worst-case reading: against an adversarial
mask (the cold side of every parameter) the log-linear head pays at
least `log 16`, for every parameterization — `log 8` is the
per-mask (non-adversarial) irreducible floor `singleAtomCE_floor`,
NOT the minimax value; the minimax is attained by the uniform
parameterization and equals `log 16`. -/
theorem singleAtomCE_minimax (θ : Fin 4 → ℝ) :
    Real.log 16 ≤ singleAtomCE (worstMask θ) θ := by
  have h : ∑ b, Real.log (qAtom θ b (worstMask θ))
      ≤ 4 * Real.log (1 / 16) := by
    have h1 := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) =>
      Real.log_le_log (qAtom_pos θ b _) (qAtom_worst_le θ b))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    norm_num at h1
    exact h1
  have hlog16 : Real.log (1 / 16) = -Real.log 16 := by
    rw [one_div, Real.log_inv]
  rw [hlog16] at h
  unfold singleAtomCE
  linarith

/-- Aligned parameters: hot exactly where the mask is true. -/
def thetaAlign (m : Fin 4 → Bool) (t : ℝ) : Fin 4 → ℝ :=
  fun b => if m b then t else -t

theorem qAtom_align (m : Fin 4 → Bool) {t : ℝ} (_ht : 0 < t) (b : Fin 4) :
    qAtom (thetaAlign m t) b m = 1 / (8 * (1 + Real.exp (-t))) := by
  have et : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have he : Real.exp (-t) = (Real.exp t)⁻¹ := by rw [Real.exp_neg]
  rw [qAtom, vennBit]
  by_cases hm : m b
  · rw [ite_eq_left hm, thetaAlign, ite_eq_left hm, mul_one, he]
    field_simp
  · rw [ite_eq_right hm, thetaAlign, ite_eq_right hm, mul_zero, Real.exp_zero, he]
    field_simp
    ring

/-- Exact closed form at the aligned parameterization: the CE sits
exactly `log(1 + e^{-t})` above the floor. -/
theorem singleAtomCE_align (m : Fin 4 → Bool) {t : ℝ} (ht : 0 < t) :
    singleAtomCE m (thetaAlign m t)
      = Real.log 8 + Real.log (1 + Real.exp (-t)) := by
  have key : ∀ b : Fin 4, Real.log (qAtom (thetaAlign m t) b m)
      = -(Real.log 8 + Real.log (1 + Real.exp (-t))) := by
    intro b
    rw [qAtom_align m ht b,
      Real.log_div (by norm_num) (by positivity), Real.log_one,
      ← Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [singleAtomCE, Finset.sum_congr rfl (fun b _ => key b),
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

/-- Tightness: the per-mask floor `log 8` is an infimum — for every
`ε > 0` some parameterization beats `log 8 + ε` (the aligned
closed form `singleAtomCE_align` tends to the floor). -/
theorem singleAtomCE_tight (m : Fin 4 → Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : Fin 4 → ℝ, singleAtomCE m θ < Real.log 8 + ε := by
  by_cases h1 : ε < 1
  · have h2e : (0 : ℝ) < 2 / ε := by positivity
    have hlt : 1 < 2 / ε := by
      rw [lt_div_iff₀ hε, one_mul]
      linarith
    refine ⟨thetaAlign m (Real.log (2 / ε)), ?_⟩
    have ht : 0 < Real.log (2 / ε) := Real.log_pos hlt
    rw [singleAtomCE_align m ht]
    have hexp : Real.exp (-(Real.log (2 / ε))) = ε / 2 := by
      rw [Real.exp_neg, Real.exp_log h2e, inv_div]
    rw [hexp]
    have h2 : Real.log (1 + ε / 2) ≤ Real.log (1 + ε) :=
      Real.log_le_log (by linarith : (0 : ℝ) < 1 + ε / 2)
        (by linarith : (1 : ℝ) + ε / 2 ≤ 1 + ε)
    have h3 : Real.log (1 + ε) < ε := by
      have := Real.log_lt_sub_one_of_pos
        (by linarith : (0 : ℝ) < 1 + ε) (by linarith : (1 : ℝ) + ε ≠ 1)
      linarith
    linarith
  · refine ⟨thetaAlign m (Real.log 2), ?_⟩
    have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [singleAtomCE_align m ht]
    have hexp : Real.exp (-(Real.log 2)) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
      norm_num
    rw [hexp]
    have h3 : Real.log (1 + 1 / 2) < 1 / 2 := by
      have := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 1 + 1 / 2)
        (by norm_num : (1 : ℝ) + 1 / 2 ≠ 1)
      linarith
    linarith

/-- Sign decode of a parameterization. -/
noncomputable def signDecode (θ : Fin 4 → ℝ) : Fin 4 → Bool :=
  fun b => 0 < θ b

/-- Despite the CE floor `singleAtomCE_floor`, `sign(θ > 0)` recovers
all sixteen masks at the aligned parameterization — 16/16 exact
recovery with the CE stuck at or above `log 8`. -/
theorem sign_recover (m : Fin 4 → Bool) {t : ℝ} (ht : 0 < t) :
    signDecode (thetaAlign m t) = m := by
  funext b
  by_cases hm : m b
  · have hb : signDecode (thetaAlign m t) b = true := by
      simp only [signDecode, thetaAlign, hm, ite_true]
      exact decide_eq_true (by linarith)
    rw [hb, hm]
  · have hm' : m b = false := by simp [hm]
    have hb : signDecode (thetaAlign m t) b = false := by
      rw [signDecode, thetaAlign, hm']
      rw [ite_eq_right (by simp)]
      exact decide_eq_false (by linarith)
    rw [hb, hm']

end Hagi.Data.BoolVenn
