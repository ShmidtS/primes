/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.SoftmaxHead

/-!
# BlockSmooth — derived Lipschitz constants for the linear-block
softmax-CE head (A18.4, audit priority 1)

The empirical premises `h_emp_smooth` / `h_emp_lip` (Lipschitz
constant of the loss taken as MEASURED) hide that for the canonical
model class — a linear block `W` followed by the CE head
(`Hagi.Model.SoftmaxHead.headCE` at `LogitMap.ident`, i.e.
`Hagi.ceOneHot`) — the constant is DERIVABLE from first principles:

* linear block: `‖W.mulVec x − W.mulVec y‖₂ ≤ ‖W‖_F · ‖x − y‖₂`
  (`linear_lipschitz_frobenius`), with `‖·‖_F` the Frobenius norm
  (per-row Cauchy–Schwarz);
* softmax-CE head: `L_soft = 2`, the frozen sup-norm contraction
  estimate `Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le`
  (`headCE_abs_sub_le_of_l2`);
* composition (chain rule in constant form): `blockCE_lipschitz`
  gives `L = L_soft · ‖W‖_F = 2·‖W‖_F`.

The consumption theorem `quant_loss_bridge_derived` is the
premise-free derived variant of `Hagi.Legacy.TopLevel.quant_loss_bridge`
(whose `hlip`/kappa premise is its own documented "h_emp_lip-style
premise"): quantizing a linear block with componentwise error `D`
changes the CE of its output by at most `2·D·√(m·n)·‖x‖₂`, with the
explicit weight-space constant `kappa = 2·‖x‖₂`
(`blockCE_weight_lipschitz`).

## Honest pins (what this derivation does NOT cover)

- Only the linear-block + ident-CE class. Arbitrary trunks (attention,
  RoPE, nonlinear stacks) keep their abstract `h_emp_smooth` /
  `h_emp_lip` premises — for those, `Hagi.Unified.lip_energy_from_gradient`
  (DerivAlong bridge) still needs a measured `κ = sup‖∇E‖`.
- Frobenius is an upper bound of the ℓ2 operator norm
  (`‖W‖₂ ≤ ‖W‖_F`); the exact op-norm `mulVec` lemma is absent from the
  pinned Mathlib, so the derivation uses the elementary Frobenius bound.
- `L_soft = 2` is the frozen in-repo estimate (sup-norm contraction),
  not the tight Euclidean constant.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.BlockSmooth

open scoped BigOperators

variable {V : Type} [Fintype V]

/-- A single coordinate is dominated by the ℓ2 norm of the vector
(sqrt-sum style). -/
theorem coord_le_l2 (z y : V → ℝ) (v : V) :
    |z v - y v| ≤ Real.sqrt (∑ w, (z w - y w) ^ 2) := by
  have h1 : (z v - y v) ^ 2 ≤ ∑ w, (z w - y w) ^ 2 :=
    Finset.single_le_sum (f := fun w => (z w - y w) ^ 2)
      (fun w _ => sq_nonneg _) (Finset.mem_univ v)
  calc |z v - y v| = Real.sqrt ((z v - y v) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ w, (z w - y w) ^ 2) := Real.sqrt_le_sqrt h1

/-! ## (a) The linear block: Lipschitz = (Frobenius) matrix norm -/

/-- The linear block `W.mulVec ·` is Lipschitz with the Frobenius
constant: `‖W.mulVec x − W.mulVec y‖₂ ≤ ‖W‖_F · ‖x − y‖₂` in the
explicit sqrt-sum norm style of the quantization bridges. Frobenius
dominates the ℓ2 operator norm, so this is an honest (not tight)
`L`-formula. -/
theorem linear_lipschitz_frobenius
    (W : Matrix V (Fin n) ℝ) (x y : Fin n → ℝ) :
    Real.sqrt (∑ i : V, (W.mulVec x i - W.mulVec y i) ^ 2)
      ≤ Real.sqrt (∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * Real.sqrt (∑ j : Fin n, (x j - y j) ^ 2) := by
  have hrow : ∀ i : V,
      (∑ j : Fin n, W i j * (x j - y j)) ^ 2
        ≤ (∑ j : Fin n, W i j ^ 2) * ∑ j : Fin n, (x j - y j) ^ 2 :=
    fun i => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => W i j) (fun j => x j - y j)
  have hE : ∀ i : V, W.mulVec x i - W.mulVec y i
      = ∑ j : Fin n, W i j * (x j - y j) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  have hsq : ∀ i : V, (W.mulVec x i - W.mulVec y i) ^ 2
      ≤ (∑ j : Fin n, W i j ^ 2) * ∑ j : Fin n, (x j - y j) ^ 2 := by
    intro i
    rw [hE i]
    exact hrow i
  have hsum : (∑ i : V, (W.mulVec x i - W.mulVec y i) ^ 2)
      ≤ (∑ i : V, ∑ j : Fin n, W i j ^ 2) * ∑ j : Fin n, (x j - y j) ^ 2 := by
    calc (∑ i : V, (W.mulVec x i - W.mulVec y i) ^ 2)
        ≤ ∑ i : V, (∑ j : Fin n, W i j ^ 2) * ∑ j : Fin n, (x j - y j) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hsq i)
      _ = (∑ i : V, ∑ j : Fin n, W i j ^ 2) * ∑ j : Fin n, (x j - y j) ^ 2 :=
          (Finset.sum_mul _ _ _).symm
  have hX : (0:ℝ) ≤ ∑ j : Fin n, (x j - y j) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hF : (0:ℝ) ≤ ∑ i : V, ∑ j : Fin n, W i j ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  calc Real.sqrt (∑ i : V, (W.mulVec x i - W.mulVec y i) ^ 2)
      ≤ Real.sqrt ((∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * ∑ j : Fin n, (x j - y j) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * Real.sqrt (∑ j : Fin n, (x j - y j) ^ 2) :=
        Real.sqrt_mul hF _


variable [Nonempty V] {n : ℕ}

/-! ## (b) The softmax-CE head: L_soft = 2 -/

/-- The softmax-CE head is 2-Lipschitz in the ℓ2 norm of the logits:
`|headCE .ident t z − headCE .ident t y| ≤ 2·‖z − y‖₂`. This is the
Euclidean form of the frozen sup-norm contraction estimate
(`headCE_le_of_abs_sub_le`), applied symmetrically. The constant
`L_soft = 2` is the derived softmax-head Lipschitz constant. -/
theorem headCE_abs_sub_le_of_l2 (t : V) (z y : V → ℝ) :
    |Hagi.Model.SoftmaxHead.headCE .ident t z
      - Hagi.Model.SoftmaxHead.headCE .ident t y|
      ≤ 2 * Real.sqrt (∑ w, (z w - y w) ^ 2) := by
  set r := Real.sqrt (∑ w, (z w - y w) ^ 2) with hr
  have hz : ∀ v, |z v - y v| ≤ r := coord_le_l2 z y
  have hy : ∀ v, |y v - z v| ≤ r := by
    intro v; rw [abs_sub_comm]; exact hz v
  have h1 := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le
    .ident t z y r hz
  have h2 := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le
    .ident t y z r hy
  rw [abs_le]
  constructor <;> linarith

/-! ## (c) The composition bound: L = L_soft · ‖W‖_F -/

/-- The composition bound (chain rule in constant form): the CE of a
linear block's output is `2·‖W‖_F`-Lipschitz in the block input —
`L_soft · L_lin` with `L_soft = 2` and `L_lin = ‖W‖_F`. This is the
block-level smoothness constant derived from first principles for the
linear + softmax-CE class. -/
theorem blockCE_lipschitz (t : V) (W : Matrix V (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    |Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec x)
      - Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec y)|
      ≤ 2 * Real.sqrt (∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * Real.sqrt (∑ j : Fin n, (x j - y j) ^ 2) := by
  have hlin := linear_lipschitz_frobenius W x y
  have hce := headCE_abs_sub_le_of_l2 t (W.mulVec x) (W.mulVec y)
  calc |Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec x)
        - Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec y)|
      ≤ 2 * Real.sqrt (∑ i : V, (W.mulVec x i - W.mulVec y i) ^ 2) :=
        hce
    _ ≤ 2 * (Real.sqrt (∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * Real.sqrt (∑ j : Fin n, (x j - y j) ^ 2)) :=
        mul_le_mul_of_nonneg_left hlin (by positivity : (0:ℝ) ≤ 2)
    _ = 2 * Real.sqrt (∑ i : V, ∑ j : Fin n, W i j ^ 2)
        * Real.sqrt (∑ j : Fin n, (x j - y j) ^ 2) := by ring

/-! ## (d) The weight-space constant: kappa = 2·‖x‖₂ -/

/-- The CE of a linear block's output is Lipschitz in the WEIGHTS with
the explicit constant `kappa = 2·‖x‖₂`:
`|CE t (W.mulVec x) − CE t (V.mulVec x)| ≤ 2·‖x‖₂·‖W − V‖_F`. This
discharges the `h_emp_lip`-style premise (measured `κ` of the loss)
for the linear + softmax-CE class with a derived formula. -/
theorem blockCE_weight_lipschitz (t : V) (W V' : Matrix V (Fin n) ℝ)
    (x : Fin n → ℝ) :
    |Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec x)
      - Hagi.Model.SoftmaxHead.headCE .ident t (V'.mulVec x)|
      ≤ 2 * Real.sqrt (∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2)
        * Real.sqrt (∑ j : Fin n, x j ^ 2) := by
  have hcoord : ∀ i : V,
      |W.mulVec x i - V'.mulVec x i|
        ≤ Real.sqrt (∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2)
          * Real.sqrt (∑ j : Fin n, x j ^ 2) := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => W i j - V' i j) x
    have hsum : (∑ j : Fin n, (W i j - V' i j) ^ 2)
        ≤ ∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ∑ j : Fin n, (W i j - V' i j) ^ 2)
        (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (Finset.mem_univ i)
    have hE : W.mulVec x i - V'.mulVec x i
        = ∑ j : Fin n, (W i j - V' i j) * x j := by
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    have hX : (0:ℝ) ≤ ∑ j : Fin n, x j ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hA : (0:ℝ) ≤ Real.sqrt (∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2)
        * Real.sqrt (∑ j : Fin n, x j ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : (W.mulVec x i - V'.mulVec x i) ^ 2
        ≤ (Real.sqrt (∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2)
          * Real.sqrt (∑ j : Fin n, x j ^ 2)) ^ 2 := by
      rw [hE, mul_pow,
        Real.sq_sqrt (by positivity : (0:ℝ)
          ≤ ∑ i : V, ∑ j : Fin n, (W i j - V' i j) ^ 2),
        Real.sq_sqrt hX]
      nlinarith [hcs, hsum, hX]
    rw [abs_le]
    constructor <;> nlinarith
  have hce := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le .ident t
    (W.mulVec x) (V'.mulVec x) _ hcoord
  have hce' := Hagi.Model.SoftmaxHead.headCE_le_of_abs_sub_le .ident t
    (V'.mulVec x) (W.mulVec x) _ (fun i => by
      rw [abs_sub_comm]; exact hcoord i)
  rw [abs_le]
  constructor <;> nlinarith

/-! ## (e) Consumption: the derived quantization-loss bridge -/

/-- **The derived quantization→loss bridge** (A18.4 consumption): if
every weight of an `m×n` linear block feeding the CE head is rounded
with componentwise error at most `D`, then the CE of the block output
changes by at most

  `|CE t (Wq.mulVec x) − CE t (W.mulVec x)| ≤ 2 · D · √(m·n) · ‖x‖₂`,

with NO Lipschitz premise: the `hlip`/`kappa` hypothesis of
`Hagi.Legacy.TopLevel.quant_loss_bridge` (its documented h_emp_lip-style
premise) is DERIVED here with `kappa = 2` for the linear-block +
softmax-CE head. Pins: linear/ident-CE class only; Frobenius bound. -/
theorem quant_loss_bridge_derived (t : V) (W Wq : Matrix V (Fin n) ℝ)
    (x : Fin n → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hres : ∀ i j, |Wq i j - W i j| ≤ D) :
    |Hagi.Model.SoftmaxHead.headCE .ident t (Wq.mulVec x)
      - Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec x)|
      ≤ 2 * D * Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ))
        * Real.sqrt (∑ j : Fin n, x j ^ 2) := by
  have hsq : ∀ i : V, ∀ j : Fin n, (Wq i j - W i j) ^ 2 ≤ D ^ 2 := by
    intro i j
    have hr := hres i j
    rw [abs_le] at hr
    nlinarith [hr.1, hr.2]
  have hn : ∑ j : Fin n, D ^ 2 = (n : ℝ) * D ^ 2 := by
    simp [Finset.sum_const]
  have hsum : (∑ i : V, ∑ j : Fin n, (Wq i j - W i j) ^ 2)
      ≤ (Fintype.card V : ℝ) * (n : ℝ) * D ^ 2 := by
    calc (∑ i : V, ∑ j : Fin n, (Wq i j - W i j) ^ 2)
        ≤ ∑ i : V, ∑ j : Fin n, D ^ 2 :=
          Finset.sum_le_sum (fun i _ =>
            Finset.sum_le_sum (fun j _ => hsq i j))
      _ = (Fintype.card V : ℝ) * ((n : ℝ) * D ^ 2) := by
          rw [Finset.sum_congr rfl (fun i _ => hn), Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card V : ℝ) * (n : ℝ) * D ^ 2 := by ring
  have hS : (0:ℝ) ≤ Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) :=
    Real.sqrt_nonneg _
  have hpos : (0:ℝ) ≤ Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D :=
    mul_nonneg hS hD
  have hR : (Fintype.card V : ℝ) * (n : ℝ) * D ^ 2
      = (Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ)
      ≤ (Fintype.card V : ℝ) * (n : ℝ))]
  rw [hR] at hsum
  have hfrob : Real.sqrt (∑ i : V, ∑ j : Fin n, (Wq i j - W i j) ^ 2)
      ≤ Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D := by
    calc Real.sqrt (∑ i : V, ∑ j : Fin n, (Wq i j - W i j) ^ 2)
        ≤ Real.sqrt ((Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D :=
          Real.sqrt_sq hpos
  have hw := blockCE_weight_lipschitz t Wq W x
  have hx : (0:ℝ) ≤ 2 * Real.sqrt (∑ j : Fin n, x j ^ 2) := by
    positivity
  calc |Hagi.Model.SoftmaxHead.headCE .ident t (Wq.mulVec x)
        - Hagi.Model.SoftmaxHead.headCE .ident t (W.mulVec x)|
      ≤ 2 * Real.sqrt (∑ i : V, ∑ j : Fin n, (Wq i j - W i j) ^ 2)
          * Real.sqrt (∑ j : Fin n, x j ^ 2) := hw
    _ ≤ 2 * (Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ)) * D)
          * Real.sqrt (∑ j : Fin n, x j ^ 2) := by
        nlinarith [hfrob, hx, hD, hS]
    _ = 2 * D * Real.sqrt ((Fintype.card V : ℝ) * (n : ℝ))
          * Real.sqrt (∑ j : Fin n, x j ^ 2) := by ring

end Hagi.Theory.BlockSmooth
