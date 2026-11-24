/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Continual
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Weight-decay leak — the GPM memory invariant under decay

The projection face of weight decay: unlike
`Hagi.Step.WeightDecay` (decay as an implicit NORM ball), here
the question is WHERE the decay step lives relative to the
protected subspace of continual learning.

* `wd_proj_preserves`: PROJECTED weight decay — the update
  `W ← W − ηλ·(W − W·P)` (decay only in the complement of the
  GPM-protected span, `W − W·P = W·P⊥`) leaves the protected
  (parallel) component `W·P` EXACTLY invariant. This is the
  machine-checked form of the HAGI_v2 experiment's measured projected
  SubspaceLeak 5.68e-15 (measured) — a numerical zero for an exact one.
* `naive_decay_leak`: NAIVE weight decay `W ← (1 − ηλ)·W`
  shrinks the protected component by the EXACT factor
  (1 − ηλ) < 1 — strict memory leak (the experiment's naive
  SubspaceLeak 1.945). The decay pulls the old-task memory
  toward zero INCLUDING the protected directions.
* `wd_gpm_step_sound`: a full GPM step — an arbitrary
  complement update `ΔC` (momentum projection / polar-NS
  operator / projected EF21: any black box with `ΔC·P = 0`)
  plus projected weight decay — preserves the protected
  component exactly.

The projector hypothesis is only idempotence `P * P = P`
(weaker than the `Pᵀ = P` of `proj_compl_orth`; symmetry is
never used — rows of `W` are projected from the right).

Consumes `Hagi.Theory.Continual` (`nrm`); same-layer import within
`Hagi/Theory` is the sanctioned folder DAG.
-/

open scoped Matrix
open Hagi.Theory.GPMRelaxed

namespace Hagi.Theory.WeightDecayLeak

variable {m n : ℕ}

/-- **nrm_smul**: the row norm of `Hagi.Theory.GPMRelaxed.nrm`
is absolutely homogeneous — scalar scaling scales the norm. -/
theorem nrm_smul (a : ℝ) (v : Fin n → ℝ) :
    nrm (a • v) = |a| * nrm v := by
  have hn : (0:ℝ) ≤ ∑ i, v i * v i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsum : (∑ i, (a • v) i * (a • v) i) = a * a * ∑ i, v i * v i := by
    have hcongr : (∑ i, (a • v) i * (a • v) i)
        = ∑ i, a * a * (v i * v i) :=
      Finset.sum_congr rfl fun i _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hcongr, Finset.mul_sum]
  show Real.sqrt (∑ i, (a • v) i * (a • v) i)
    = |a| * Real.sqrt (∑ i, v i * v i)
  rw [hsum, Real.sqrt_mul (mul_self_nonneg a),
    Real.sqrt_mul_self_eq_abs a]

/-- **proj_compl_mul_cancel**: for an idempotent projector
the complement annihilates the protected span from the right:
`(1 − P) * P = 0`. Pure algebra, no symmetry needed. -/
theorem proj_compl_mul_cancel (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * P = 0 := by
  have h1 : ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * P
      = (1 : Matrix (Fin n) (Fin n) ℝ) * P - P * P := Matrix.sub_mul _ _ _
  rw [h1, Matrix.one_mul, hP, sub_self]

/-- **wd_compl_annihilates**: the complement component
`W − W * P = W·P⊥` has zero parallel projection — decay applied
to it cannot touch the protected span. -/
theorem wd_compl_annihilates (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) :
    (W - W * P) * P = 0 := by
  have e1 : W - W * P = W * ((1 : Matrix (Fin n) (Fin n) ℝ) - P) := by
    conv_lhs => arg 1; rw [← Matrix.mul_one (W : Matrix (Fin m) (Fin n) ℝ)]
    exact (Matrix.mul_sub W (1 : Matrix (Fin n) (Fin n) ℝ) P).symm
  rw [e1, Matrix.mul_assoc, proj_compl_mul_cancel P hP, Matrix.mul_zero]

/-- **wd_proj_preserves (invariant)**: PROJECTED weight
decay — `W' = W − ηλ • (W − W * P)`, i.e. decay applied only in
the complement `W − W * P = W·P⊥` of the protected span —
leaves the protected (parallel) component `W * P` EXACTLY
invariant. The projected-decay experiment line
(SubspaceLeak 5.68e-15, measured) is this exact zero up to floating point. -/
theorem wd_proj_preserves (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) (c : ℝ) :
    (W - c • (W - W * P)) * P = W * P := by
  rw [Matrix.sub_mul, Matrix.smul_mul, wd_compl_annihilates W P hP,
    smul_zero, sub_zero]

/-- **naive_decay_parallel**: NAIVE weight decay
`W ← (1 − c) • W` acts on the protected component as scalar
multiplication by the SAME factor `(1 − c)` — the decay pulls
the memory toward zero including the protected directions. -/
theorem naive_decay_parallel (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    ((1 - c) • W) * P = (1 - c) • (W * P) := by
  exact Matrix.smul_mul _ _ _

/-- **naive_decay_norm (exact leak identity)**: for
`0 ≤ c ≤ 1` the naive-decayed protected component of every row
has norm EXACTLY `(1 − c) * ‖row of W * P‖` — the memory shrinks
by the exact decay factor, not a bound. -/
theorem naive_decay_norm (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc1 : c ≤ 1) (i : Fin m) :
    nrm ((((1 - c) • W) * P) i) = (1 - c) * nrm ((W * P) i) := by
  rw [naive_decay_parallel]
  show nrm ((1 - c) • (W * P) i) = (1 - c) * nrm ((W * P) i)
  rw [nrm_smul, abs_of_nonneg (by linarith)]

/-- **naive_decay_leak (strict)**: if the protected
component of row `i` is non-trivial and `0 < c < 1`, one naive
weight-decay step STRICTLY shrinks it — strict memory leak. This
is the theorem behind the experiment's naive SubspaceLeak 1.945:
without projecting the decay into the complement, the GPM
protection does not protect. -/
theorem naive_decay_leak (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (i : Fin m)
    (hne : nrm ((W * P) i) ≠ 0) :
    nrm ((((1 - c) • W) * P) i) < nrm ((W * P) i) := by
  have hpos : 0 < nrm ((W * P) i) :=
    lt_of_le_of_ne (by unfold nrm; exact Real.sqrt_nonneg _)
      (Ne.symm hne)
  rw [naive_decay_norm W P c hc1.le i]
  have hlt : (1 - c) * nrm ((W * P) i) < 1 * nrm ((W * P) i) :=
    mul_lt_mul_of_pos_right (by linarith) hpos
  linarith

/-- **compl_step_preserves**: any update living entirely
in the complement of the protected span (`ΔC * P = 0`) leaves
the protected component exactly invariant — the black-box
interface for momentum projection, polar/NS operators, and
projected EF21 compressors: one hypothesis, no internals. -/
theorem compl_step_preserves (W ΔC : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hC : ΔC * P = 0) :
    (W + ΔC) * P = W * P := by
  rw [Matrix.add_mul, hC, add_zero]

/-- **wd_gpm_step_sound (main)**: the FULL GPM continual
step — a complement update `ΔC` (any of the mechanisms
in their projected form, kept as the black box `ΔC * P = 0`)
followed by PROJECTED weight decay — preserves the protected
component exactly. Composition of `compl_step_preserves` with
`wd_proj_preserves`: with projected decay, weight decay never
destroys the old-task memory the GPM projection protects. -/
theorem wd_gpm_step_sound (W ΔC : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hC : ΔC * P = 0) (c : ℝ) :
    (W - ΔC - c • (W - W * P)) * P = W * P := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, hC,
    wd_compl_annihilates W P hP, smul_zero, sub_zero, sub_zero]

end Hagi.Theory.WeightDecayLeak
