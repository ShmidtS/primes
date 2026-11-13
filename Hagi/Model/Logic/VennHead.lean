import Mathlib.Tactic
import Hagi.Energy.Ternary
import Hagi.Runtime.TernaryExact
import Hagi.Cert.CertifiedArgmax
import Hagi.Data.BoolVenn

/-!
# Exact Boolean Venn head: atoms as ReLU neurons

Track B7 (master plan v3 addendum A4), C242. The four Venn atoms of
`Hagi.Data.BoolVenn` are realized by ReLU threshold neurons
`vAtom sA sB A B = relu (sA*A + sB*B - 1)` on `{−1,+1}` inputs
(exactly-one-hot: `vAtoms_sum_one`, `vAtoms_mem`), and the 16 boolean
functions of two variables become a LINEAR head `vennHead m` over the
atoms with `{0,1}` mask weights.

Exactness is end-to-end and certified:

- `vennHead_exact` — the 64-case bridge: on sign inputs the head
  computes the truth value of the `Hagi.Data.BoolVenn` mask
  (16 masks × 4 inputs).
- `venn_pair_win` / `venn_certified` — the head emits the logit pair
  `![f, 1 - f]` over `Fin 2` with eps-gap exactly 1, composing with
  `Hagi.Data.CertifiedArgmax.certified_argmax_strict` at zero
  estimation error: for any `ε` with `2 * ε < 1` the certified argmax
  index IS the truth value of the boolean function.
- `venn_mask_ternary` — ternary representability: the ACTUAL quantizer
  `Hagi.Runtime.qTern` at scale 1 is the identity on `{0,1}`, i.e. the
  quantization penalty of every head row is exactly 0 (not merely
  bounded; cf. the in-range bound `Hagi.Energy.roundTern_error`).

Boundary, honestly: this is exactness for two-variable boolean logic
(the 16-function Venn lattice), not logic in general; the honest
scalability boundary of mask-linear heads is `n ≤ 4-5` inputs.

C251 additions (A8 F4): the two-layer Hasse composition — the 2-bit
adder/subtractor built from two 1-layer heads over bit-split
channels (`venn2Head`): sum = XOR (`xorMask`, rank two), carry =
AND (`andMask`, rank one, the two-input majority), borrow =
`¬x ∧ y` (`borrowMask`, rank one), with exact two-bit arithmetic
(`venn2_adder_correct`, `venn2_suber_correct`, `venn2_adder_real`).
-/

set_option linter.style.header false

namespace Hagi.Model.Logic

open Hagi.Energy Hagi.Data.CertifiedArgmax Hagi.Runtime Hagi.Data.BoolVenn

/-- ReLU (if-form of `max 0 ·`; the if-form makes `norm_num` automation
robust on numeric goals). -/
noncomputable def relu (x : ℝ) : ℝ := if 0 < x then x else 0

/-- The ReLU if-form agrees with `max 0 ·`. -/
theorem relu_max (x : ℝ) : relu x = max 0 x := by
  unfold relu
  by_cases h : 0 < x
  · rw [ite_eq_left h, max_eq_right (le_of_lt h)]
  · rw [ite_eq_right h, max_eq_left]
    linarith

/-- Venn atom: ReLU threshold on a `±A ±B - 1` sign form. -/
noncomputable def vAtom (sA sB A B : ℝ) : ℝ := relu (sA * A + sB * B - 1)

/-- The 4 atoms as a `Fin 4` family (order `++`, `+-`, `-+`, `--`,
matching `Hagi.Data.BoolVenn.atomIdx`). -/
noncomputable def vAtoms (A B : ℝ) : Fin 4 → ℝ :=
  ![vAtom 1 1 A B, vAtom 1 (-1) A B, vAtom (-1) 1 A B, vAtom (-1) (-1) A B]

/-- Exactly-one-hot: the four atoms sum to 1 on `{−1,+1}` inputs. -/
theorem vAtoms_sum_one {A B : ℝ} (hA : A = 1 ∨ A = -1)
    (hB : B = 1 ∨ B = -1) :
    ∑ k, vAtoms A B k = 1 := by
    rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    subst hA <;> subst hB <;>
    norm_num [vAtoms, vAtom, relu, Fin.sum_univ_four]

/-- Each atom is 0 or 1 on `{−1,+1}` inputs. -/
theorem vAtoms_mem {A B : ℝ} (hA : A = 1 ∨ A = -1)
    (hB : B = 1 ∨ B = -1) (k : Fin 4) :
    vAtoms A B k = 0 ∨ vAtoms A B k = 1 := by
  fin_cases k <;>
    rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    subst hA <;> subst hB <;>
    norm_num [vAtoms, vAtom, relu]

/-- Linear head over the atoms: `vennHead m A B = ∑ k, m k * atom k`. -/
noncomputable def vennHead (m : Fin 4 → ℝ) (A B : ℝ) : ℝ := ∑ k, m k * vAtoms A B k

/-- Head output is boolean (0 or 1) for a `{0,1}` mask. -/
theorem vennHead_mem {m : Fin 4 → ℝ} {A B : ℝ}
    (hm : ∀ k, m k = 0 ∨ m k = 1)
    (hA : A = 1 ∨ A = -1) (hB : B = 1 ∨ B = -1) :
    vennHead m A B = 0 ∨ vennHead m A B = 1 := by
  rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    subst hA <;> subst hB
  · have h : vennHead m 1 1 = m 0 := by
      norm_num [vennHead, vAtoms, vAtom, relu, Fin.sum_univ_four]
    rw [h]; exact hm 0
  · have h : vennHead m 1 (-1) = m 1 := by
      norm_num [vennHead, vAtoms, vAtom, relu, Fin.sum_univ_four]
    rw [h]; exact hm 1
  · have h : vennHead m (-1) 1 = m 2 := by
      norm_num [vennHead, vAtoms, vAtom, relu, Fin.sum_univ_four]
    rw [h]; exact hm 2
  · have h : vennHead m (-1) (-1) = m 3 := by
      norm_num [vennHead, vAtoms, vAtom, relu, Fin.sum_univ_four]
    rw [h]; exact hm 3

/-- Sign embedding `Bool → {−1,+1}`. -/
def s (a : Bool) : ℝ := if a then 1 else -1

/-- Mask embedding `(Fin 4 → Bool) → {0,1}`. -/
def maskReal (m : Fin 4 → Bool) : Fin 4 → ℝ := fun k => if m k then 1 else 0

/-- The 64-case bridge: on sign inputs the linear head computes the
truth value of the Venn mask (16 masks × 4 inputs, `vennHead_exact`). -/
theorem vennHead_exact (m : Fin 4 → Bool) (a b : Bool) :
    vennHead (maskReal m) (s a) (s b)
      = (if vennBool m a b then (1:ℝ) else 0) := by
  unfold vennHead vAtoms vAtom relu vennBool atomIdx maskReal s
  cases a <;> cases b <;>
    norm_num [Fin.sum_univ_four] <;>
    (cases m 0 <;> cases m 1 <;> cases m 2 <;> cases m 3 <;> norm_num)

/-- The winning logit of the pair `![f, 1 - f]` at the truth index is
exactly 1. -/
theorem venn_pair_win (m : Fin 4 → Bool) (a b : Bool) :
    (![vennHead (maskReal m) (s a) (s b),
       1 - vennHead (maskReal m) (s a) (s b)] : Fin 2 → ℝ)
      (if vennBool m a b then 0 else 1) = 1 := by
  have hb := vennHead_exact m a b
  cases hbv : vennBool m a b <;> simp [hb, hbv]

/-- Certified composition: `Hagi.Data.CertifiedArgmax.certified_argmax_strict`
with `est = v` (zero estimation error ≤ ε) and truth gap 1 > 2ε. The
certified argmax index of the head's logit pair IS the truth value of
the boolean function, for any `ε` with `2 * ε < 1`. -/
theorem venn_certified (m : Fin 4 → Bool) (a b : Bool) {ε : ℝ}
    (hε : 0 ≤ ε) (hε2 : 2 * ε < 1) :
    ∀ i, i ≠ (if vennBool m a b then 0 else 1) →
      (![vennHead (maskReal m) (s a) (s b),
         1 - vennHead (maskReal m) (s a) (s b)] : Fin 2 → ℝ) i
        < ![vennHead (maskReal m) (s a) (s b),
            1 - vennHead (maskReal m) (s a) (s b)]
            (if vennBool m a b then 0 else 1) :=
  certified_argmax_strict
    (v := ![vennHead (maskReal m) (s a) (s b),
       1 - vennHead (maskReal m) (s a) (s b)])
    (est := ![vennHead (maskReal m) (s a) (s b),
       1 - vennHead (maskReal m) (s a) (s b)])
    (ε := ε)
    (herr := fun i => by
      fin_cases i <;> simp only [sub_self, abs_zero] <;> exact hε)
    (hgap := by
      intro i hi
      have hb := vennHead_exact m a b
      have hlose : (![vennHead (maskReal m) (s a) (s b),
         1 - vennHead (maskReal m) (s a) (s b)] : Fin 2 → ℝ) i = 0 := by
        fin_cases i
        · cases hbv : vennBool m a b
          · simp [hb, hbv] <;> norm_num
          · exfalso; exact hi (by simp [hbv])
        · cases hbv : vennBool m a b
          · exfalso; exact hi (by simp [hbv])
          · simp [hb, hbv] <;> norm_num
      have hwin := venn_pair_win m a b
      rw [hlose, hwin]
      linarith)

/-- Ternary representability: the ACTUAL quantizer `Hagi.Runtime.qTern`
at scale 1 is the identity on `{0,1}` — the quantization penalty of a
`{0,1}` head weight is exactly 0 (not merely bounded; the in-range
bound `Hagi.Energy.roundTern_error` gives error ≤ s/2, here it is 0). -/
theorem venn_mask_ternary {w : ℝ} (hw : w = 0 ∨ w = 1) :
    qTern 1 w = w := by
  rcases hw with hw | hw <;> subst hw <;>
    unfold qTern roundTern <;> norm_num

/-! ## C251: 2-layer Hasse composition (ADD4 / SUB4 grounding) -/

/-- The XOR mask (rank two). -/
def xorMask : Fin 4 → Bool := ![false, true, true, false]

/-- The AND mask (rank one). -/
def andMask : Fin 4 → Bool := ![true, false, false, false]

/-- The borrow mask `¬x ∧ y` (rank one). -/
def borrowMask : Fin 4 → Bool := ![false, false, true, false]

theorem vennBool_xor : ∀ (a b : Bool), vennBool xorMask a b = xor a b := by
  decide

theorem vennBool_and : ∀ (a b : Bool), vennBool andMask a b = (a && b) := by
  decide

theorem vennBool_borrow : ∀ (a b : Bool),
    vennBool borrowMask a b = (!a && b) := by
  decide

theorem maskRank_xor : maskRank xorMask = 2 := by decide

theorem maskRank_and : maskRank andMask = 1 := by decide

theorem maskRank_borrow : maskRank borrowMask = 1 := by decide

/-- The two-channel head: two 1-layer Venn heads over bit-split
outputs (channel zero = the carry/borrow head, channel one = the
sum/diff head). -/
noncomputable def venn2Head (mo mc : Fin 4 → Bool) (A B : ℝ) : Fin 2 → ℝ :=
  ![vennHead (maskReal mo) A B, vennHead (maskReal mc) A B]

/-- `{0,1}` value of a Bool. -/
def bval (a : Bool) : ℕ := if a then 1 else 0

/-- ADD composition: sum bit = XOR, carry = AND (the two-input
majority); the two-channel head computes two-bit addition exactly
(`ADD4` modulo four). -/
theorem venn2_adder_correct (x y : Bool) :
    (2 * bval (x && y) + bval (xor x y)) % 4
      = (bval x + bval y) % 4 := by
  cases x <;> cases y <;> norm_num [bval]

/-- SUB composition: diff bit = XOR, borrow = `¬x ∧ y`; two-bit
subtraction modulo four (`SUB4`). -/
theorem venn2_suber_correct (x y : Bool) :
    (2 * bval (!x && y) + bval (xor x y)) % 4
      = (bval x + (4 - bval y)) % 4 := by
  cases x <;> cases y <;> norm_num [bval]

/-- The executed sum channel equals the XOR truth value (the C242
bridge `vennHead_exact` on the XOR mask). -/
theorem venn2_sum_head (x y : Bool) :
    vennHead (maskReal xorMask) (s x) (s y)
      = (if xor x y then (1 : ℝ) else 0) := by
  rw [vennHead_exact]
  rw [vennBool_xor]

/-- The executed carry channel equals the AND truth value. -/
theorem venn2_carry_head (x y : Bool) :
    vennHead (maskReal andMask) (s x) (s y)
      = (if x && y then (1 : ℝ) else 0) := by
  rw [vennHead_exact]
  rw [vennBool_and]

/-- The executed borrow channel equals the `¬x ∧ y` truth value. -/
theorem venn2_borrow_head (x y : Bool) :
    vennHead (maskReal borrowMask) (s x) (s y)
      = (if !x && y then (1 : ℝ) else 0) := by
  rw [vennHead_exact]
  rw [vennBool_borrow]

/-- The two-channel adder head on sign inputs produces exactly the
`(carry, sum)` pair of truth values. -/
theorem venn2Head_add (x y : Bool) :
    venn2Head andMask xorMask (s x) (s y)
      = ![if x && y then (1 : ℝ) else 0, if xor x y then (1 : ℝ) else 0] := by
  rw [venn2Head, venn2_carry_head, venn2_sum_head]

/-- Real-valued composition: `2 * carry + sum = x + y` on the nose
(no modulus needed — the two-bit sum is at most two). -/
theorem venn2_adder_real (x y : Bool) :
    2 * vennHead (maskReal andMask) (s x) (s y)
      + vennHead (maskReal xorMask) (s x) (s y)
      = (bval x : ℝ) + (bval y : ℝ) := by
  rw [venn2_carry_head, venn2_sum_head]
  cases x <;> cases y <;> norm_num [bval]

end Hagi.Model.Logic
