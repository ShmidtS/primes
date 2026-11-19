/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.LMCompose
import Hagi.Theory.BlockSmooth

/-!
# BlockLipschitz — derived lip/causal for REAL atoms (RMSNorm, MLP,
bounded-weight attention)

Beat C465 (A19 G1, roadmap C464): the per-block premises
`CertifiedBlock.hLip` / `hCausal` (`Hagi.Model.LMCompose`, разрядка
заявлена в honest pins того модуля) are DISCHARGED here for concrete
real-world atoms with derived constants (derivability, not tightness):

* (a) RMSNorm atom `x ↦ g·x/(‖x‖₂/√n + ε)` (HAGI_v2 ε-floor semantics,
  `C:/HAGI_v2/hagi/lm.py`): GLOBAL ℓ1-Lipschitz constant
  `G·(n+1)/ε` (`rmsN_l1_lip`) — unconditional, via the saturation
  bound `|y_v| ≤ √n·dy` (the normalized output never exceeds √n, so
  NO boundedness premise on the inputs is needed). CertifiedBlock:
  `certifiedRMSNorm`, lip = `1 + G·(n+1)/ε` (residual + norm).
* (b) MLP atom `x ↦ W₂·relu(W₁·x)`: ℓ1-constant
  `√n·‖W₂‖_F·‖W₁‖_F` (`mlp_l1_lip`) — C426
  `linear_lipschitz_frobenius` (cited) on the first layer + row
  Cauchy–Schwarz + relu 1-Lip (`relu_lip_abs`; no ReLU lemma in the
  corpus — NormAct has swish only). CertifiedBlock: `certifiedMLP`,
  lip = `1 + √n·F₂·F₁`.
* (c) Bounded-weight causal attention `attAgg` with geometric decay
  weights `w k = 2^-(k+1)` (row sum ≤ 1 — convex combination; column
  sum ≤ 1 — `geom_tail_le_one`): value-side ℓ1-contraction
  (`convAtt_l1`), CertifiedBlock `certifiedConvAtt` with lip = 2,
  unconditional. Softmax bounded-logit context: `Hagi.Model.QKNorm.attP`
  / `qk_no_saturation` (cited).

## Honest pins (negatives and limits)

- Attention with x-DEPENDENT scores and NO value bound is NOT globally
  Lipschitz even under `|logits| ≤ B`: the weight-shift leg is bounded
  by `M·‖w(x)−w(y)‖₁` with `M = sup_i ‖x i‖∞` — the obstruction is the
  UNBOUNDED VALUES, not the softmax (softmax itself is globally
  ≤ 1/2-Lipschitz in ℓ2, Pauli et al. 2023 — pinned, not restated).
  `CertifiedBlock.hLip` is an unconditional field, so the
  bounded-logit version needs a value-bounded carrier (a domain-bounded
  CertifiedBlock) — deliberately out of scope (YAGNI).
- RMSNorm WITHOUT the ε-floor (`x ↦ x/‖x‖`) is not defined at 0 and
  not Lipschitz across sign changes (x vs −x collapse to opposite
  unit vectors); the ε-floor is exactly what makes the unconditional
  constant derivable. The derived `G(n+1)/ε` is honest but NOT tight
  (true near-zero slope is `1/ε` per coordinate plus saturation).
- MLP constant uses the Frobenius bound (`‖W‖₂ ≤ ‖W‖_F`, C426 pin);
  the op-norm lemma is absent from the pinned Mathlib.
- Constants are per-position ℓ1 (the `dPre` metric of LMCompose);
  ℓ2→ℓ1 conversions cost the √n factors. Derivability is the goal of
  this beat, not optimality.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.BlockLipschitz

open scoped BigOperators NNReal

variable {V : Type} [Fintype V]

/-! ## Norm helpers (ℓ2/ℓ1 bridge, reverse triangle) -/

/-- ℓ2 ≤ ℓ1: the sqrt-sum norm is dominated by the sum of absolute
values (diagonal dominance of the square of the ℓ1 sum). -/
theorem sqrt_sum_sq_le_sum_abs (r : V → ℝ) :
    Real.sqrt (∑ v, r v ^ 2) ≤ ∑ v, |r v| := by
  have hkey : (∑ v, r v ^ 2) ≤ (∑ v, |r v|) * ∑ v, |r v| := by
    calc (∑ v, r v ^ 2) ≤ ∑ v, |r v| * (∑ w, |r w|) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have hsq : r v ^ 2 = |r v| * |r v| := by
            rw [← sq_abs (r v), pow_two]
          rw [hsq, Finset.mul_sum]
          exact Finset.single_le_sum
            (f := fun w => |r v| * |r w|)
            (fun w _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (Finset.mem_univ v)
      _ = (∑ v, |r v|) * ∑ v, |r v| := (Finset.sum_mul _ _ _).symm
  have habs : (0:ℝ) ≤ ∑ v, |r v| :=
    Finset.sum_nonneg (fun v _ => abs_nonneg _)
  calc Real.sqrt (∑ v, r v ^ 2) ≤ Real.sqrt ((∑ v, |r v|) * ∑ v, |r v|) :=
        Real.sqrt_le_sqrt hkey
    _ = Real.sqrt ((∑ v, |r v|) ^ 2) := by
          have h : (∑ v, |r v|) * ∑ v, |r v| = (∑ v, |r v|) ^ 2 := by ring
          rw [h]
    _ = ∑ v, |r v| := Real.sqrt_sq habs

/-- One-sided reverse triangle for the sqrt-sum norm (Cauchy–Schwarz
on the cross term of the expansion `a = b + (a − b)`). -/
theorem sqrt_le_sqrt_add (a b : V → ℝ) :
    Real.sqrt (∑ v, a v ^ 2)
      ≤ Real.sqrt (∑ v, b v ^ 2) + Real.sqrt (∑ v, (a v - b v) ^ 2) := by
  have hexp : (∑ v, a v ^ 2)
      = (∑ v, b v ^ 2) + (∑ v, (a v - b v) ^ 2)
        + 2 * (∑ v, b v * (a v - b v)) := by
    have h : ∀ v : V, a v ^ 2
        = b v ^ 2 + (a v - b v) ^ 2 + 2 * (b v * (a v - b v)) :=
      fun v => by ring
    rw [Finset.sum_congr rfl (fun v _ => h v)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun v => b v) (fun v => a v - b v)
  have hB : (0:ℝ) ≤ ∑ v, b v ^ 2 :=
    Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hC : (0:ℝ) ≤ ∑ v, (a v - b v) ^ 2 :=
    Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hnn : (0:ℝ) ≤ (∑ v, b v ^ 2) * ∑ v, (a v - b v) ^ 2 :=
    mul_nonneg hB hC
  have habs : (∑ v, b v * (a v - b v))
      ≤ Real.sqrt (∑ v, b v ^ 2) * Real.sqrt (∑ v, (a v - b v) ^ 2) := by
    have hle : |∑ v, b v * (a v - b v)|
        ≤ Real.sqrt ((∑ v, b v ^ 2) * ∑ v, (a v - b v) ^ 2) :=
      abs_le_of_sq_le_sq
        (by rw [Real.sq_sqrt hnn]; exact hcs) (Real.sqrt_nonneg _)
    rw [Real.sqrt_mul hB] at hle
    linarith [hle, le_abs_self (∑ v, b v * (a v - b v))]
  have hsb : (Real.sqrt (∑ v, b v ^ 2)) ^ 2 = ∑ v, b v ^ 2 :=
    Real.sq_sqrt hB
  have hsc : (Real.sqrt (∑ v, (a v - b v) ^ 2)) ^ 2
      = ∑ v, (a v - b v) ^ 2 := Real.sq_sqrt hC
  have hs : (0:ℝ) ≤ Real.sqrt (∑ v, b v ^ 2)
      + Real.sqrt (∑ v, (a v - b v) ^ 2) := by positivity
  have hle : (∑ v, a v ^ 2)
      ≤ (Real.sqrt (∑ v, b v ^ 2)
          + Real.sqrt (∑ v, (a v - b v) ^ 2)) ^ 2 := by
    nlinarith [hexp, habs, hsb, hsc]
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hs] at this

/-- Reverse triangle for the sqrt-sum norm. -/
theorem abs_sqrt_sub_sqrt_le (a b : V → ℝ) :
    |Real.sqrt (∑ v, a v ^ 2) - Real.sqrt (∑ v, b v ^ 2)|
      ≤ Real.sqrt (∑ v, (a v - b v) ^ 2) := by
  have h1 := sqrt_le_sqrt_add a b
  have h2 := sqrt_le_sqrt_add b a
  have h2' : Real.sqrt (∑ v, b v ^ 2)
      ≤ Real.sqrt (∑ v, a v ^ 2) + Real.sqrt (∑ v, (a v - b v) ^ 2) := by
    have hsub : (∑ v, (b v - a v) ^ 2) = (∑ v, (a v - b v) ^ 2) :=
      Finset.sum_congr rfl fun v _ => by ring
    rwa [hsub] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Single coordinate is dominated by the ℓ2 norm (plain form, not
the difference form of `BlockSmooth.coord_le_l2`). -/
theorem coord_abs_le_l2 (r : V → ℝ) (v : V) :
    |r v| ≤ Real.sqrt (∑ w, r w ^ 2) := by
  have h1 : r v ^ 2 ≤ ∑ w, r w ^ 2 :=
    Finset.single_le_sum (f := fun w => r w ^ 2)
      (fun w _ => sq_nonneg _) (Finset.mem_univ v)
  calc |r v| = Real.sqrt (r v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ w, r w ^ 2) := Real.sqrt_le_sqrt h1

/-! ## (a) RMSNorm atom: unconditional G·(n+1)/ε -/

/-- Generic coordinate bound for ε-floored normalization:
`|a/dx − b/dy| ≤ |a−b|/ε + S/ε`, given the coordinate-split identity,
saturation `|b| ≤ n·dy`, denominator shift `|dy−dx| ≤ S/n` (n > 0),
and the ε-floor `ε ≤ dx`. -/
theorem coord_norm_bound {a b dx dy S n : ℝ} (hdx : 0 < dx)
    (hdy : 0 < dy) (hex : ε ≤ dx) (hε : 0 < ε)
    (hsplit : a / dx - b / dy = (a - b) / dx + b * (dy - dx) / (dx * dy))
    (hsat : |b| ≤ n * dy) (hsub : |dy - dx| ≤ S / n) (hn : 0 < n)
    (hS : 0 ≤ S) :
    |a / dx - b / dy| ≤ |a - b| / ε + S / ε := by
  rw [hsplit]
  refine le_trans (abs_add_le ((a - b) / dx)
    (b * (dy - dx) / (dx * dy))) ?_
  have h1 : |(a - b) / dx| ≤ |a - b| / ε := by
    rw [abs_div, abs_of_pos hdx]
    exact div_le_div_of_nonneg_left (abs_nonneg (a - b)) hε hex
  have hnum : |b| * |dy - dx| ≤ dy * S := by
    have h2 : |b| * |dy - dx| ≤ n * dy * (S / n) :=
      mul_le_mul hsat hsub (abs_nonneg _) (mul_nonneg hn.le (le_of_lt hdy))
    have h3 : n * dy * (S / n) = dy * S := by
      field_simp [hn.ne']
    linarith
  have hstep : |b * (dy - dx) / (dx * dy)| ≤ dy * S / (dx * dy) := by
    rw [abs_div]
    simp only [abs_mul, abs_of_pos hdx, abs_of_pos hdy]
    rw [div_le_div_iff₀ (mul_pos hdx hdy) (mul_pos hdx hdy)]
    nlinarith [hnum, mul_pos hdx hdy]
  have hcancel : dy * S / (dx * dy) = S / dx := by
    field_simp [hdx.ne', hdy.ne']
  have hlast : S / dx ≤ S / ε :=
    div_le_div_of_nonneg_left hS hε hex
  have h2 := hstep.trans (hcancel ▸ hlast)
  linarith

section RMS

variable [Nonempty V]

/-- RMSNorm denominator: `‖x‖₂/√n + ε` (HAGI_v2 ε-floor semantics,
`hagi/lm.py` — rms-scale normalization with an ε floor). -/
noncomputable def rmsDen (ε : ℝ) (x : V → ℝ) : ℝ :=
  Real.sqrt (∑ v, x v ^ 2) / Real.sqrt (Fintype.card V) + ε

/-- RMSNorm atom output (gain applied by the caller). -/
noncomputable def rmsN (ε : ℝ) (x : V → ℝ) (v : V) : ℝ :=
  x v / rmsDen ε x

/-- The RMSNorm atom is GLOBAL ℓ1-Lipschitz with the unconditional
constant `(n+1)/ε` — no boundedness premise on the inputs: the
saturation bound `|y_v| ≤ √n·dy` caps the weight-shift leg. -/
theorem rmsN_l1_lip (ε : ℝ) (hε : 0 < ε) (x y : V → ℝ) :
    (∑ v, |rmsN ε x v - rmsN ε y v|)
      ≤ ((Fintype.card V : ℝ) + 1) / ε * (∑ v, |x v - y v|) := by
  have hn : (0:ℝ) < Real.sqrt (Fintype.card V) := by
    have hp : (0:ℝ) < (Fintype.card V : ℝ) := by positivity
    exact Real.sqrt_pos.mpr hp
  have hnn : (0:ℝ) ≤ Real.sqrt (Fintype.card V) := hn.le
  have hdx : (0:ℝ) < rmsDen ε x := by
    have h1 : (0:ℝ) ≤ Real.sqrt (∑ v, x v ^ 2) := Real.sqrt_nonneg _
    have hd := div_nonneg h1 hnn
    unfold rmsDen; linarith
  have hdy : (0:ℝ) < rmsDen ε y := by
    have h1 : (0:ℝ) ≤ Real.sqrt (∑ v, y v ^ 2) := Real.sqrt_nonneg _
    have hd := div_nonneg h1 hnn
    unfold rmsDen; linarith
  have hex : ε ≤ rmsDen ε x := by
    have h1 : (0:ℝ) ≤ Real.sqrt (∑ v, x v ^ 2) := Real.sqrt_nonneg _
    have hd := div_nonneg h1 hnn
    unfold rmsDen; linarith
  -- coordinate split identity
  have hsplit : ∀ v : V, rmsN ε x v - rmsN ε y v
      = (x v - y v) / rmsDen ε x
        + y v * (rmsDen ε y - rmsDen ε x)
          / (rmsDen ε x * rmsDen ε y) := by
    intro v
    unfold rmsN
    field_simp [hdx.ne', hdy.ne']
    ring
  -- denominator shift via reverse triangle
  have hsub : |rmsDen ε y - rmsDen ε x|
      ≤ Real.sqrt (∑ w, (x w - y w) ^ 2) / Real.sqrt (Fintype.card V) := by
    have hrw : rmsDen ε x - rmsDen ε y
        = (Real.sqrt (∑ w, x w ^ 2) - Real.sqrt (∑ w, y w ^ 2))
          / Real.sqrt (Fintype.card V) := by
      unfold rmsDen
      field_simp [hn.ne']
      ring
    have hrt := abs_sqrt_sub_sqrt_le x y
    have hnabs : |Real.sqrt (Fintype.card V)|
        = Real.sqrt (Fintype.card V) := abs_of_nonneg hnn
    rw [abs_sub_comm, hrw, abs_div, hnabs, div_le_div_iff₀ hn hn]
    nlinarith [hrt]
  -- saturation
  have hsat : ∀ v : V,
      |y v| ≤ Real.sqrt (Fintype.card V) * rmsDen ε y := by
    intro v
    have hyv : |y v| ≤ Real.sqrt (∑ w, y w ^ 2) :=
      coord_abs_le_l2 y v
    have hd : Real.sqrt (Fintype.card V) * rmsDen ε y
        = Real.sqrt (∑ w, y w ^ 2) + Real.sqrt (Fintype.card V) * ε := by
      unfold rmsDen
      field_simp [hn.ne']
    rw [hd]
    have hprod : (0:ℝ) ≤ Real.sqrt (Fintype.card V) * ε :=
      mul_nonneg hnn hε.le
    linarith
  -- per-coordinate application
  set Δ : ℝ := ∑ w, (x w - y w) ^ 2 with hΔ
  have hcoord : ∀ v : V, |rmsN ε x v - rmsN ε y v|
      ≤ |x v - y v| / ε + Real.sqrt Δ / ε := fun v =>
    coord_norm_bound hdx hdy hex hε (hsplit v) (hsat v) hsub hn
      (Real.sqrt_nonneg _)
  have hl2 : Real.sqrt Δ ≤ ∑ v, |x v - y v| :=
    sqrt_sum_sq_le_sum_abs (fun w => x w - y w)
  calc (∑ v, |rmsN ε x v - rmsN ε y v|)
      ≤ ∑ v, (|x v - y v| / ε + Real.sqrt Δ / ε) :=
        Finset.sum_le_sum (fun v _ => hcoord v)
    _ = (∑ v, |x v - y v|) / ε
        + (Fintype.card V : ℝ) * (Real.sqrt Δ / ε) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← Finset.sum_div]
    _ ≤ ((Fintype.card V : ℝ) + 1) / ε * (∑ v, |x v - y v|) := by
        have hmono : Real.sqrt Δ / ε ≤ (∑ v, |x v - y v|) / ε := by
          rw [div_le_div_iff₀ hε hε]
          nlinarith [hl2]
        have h2 : (∑ v, |x v - y v|) / ε
            + (Fintype.card V : ℝ) * ((∑ v, |x v - y v|) / ε)
          = ((Fintype.card V : ℝ) + 1) / ε * (∑ v, |x v - y v|) := by
          field_simp
          ring
        nlinarith [hmono]

/-- CertifiedBlock for the RMSNorm atom (attn = id, norm = g·rmsN ε):
`hLip` DERIVED with lip = `1 + G·(n+1)/ε` (residual + derived norm
constant), `hCausal` DERIVED (positional dependence only, C450
pattern). Gain bounded by G coordinatewise. -/
noncomputable def certifiedRMSNorm (g : V → ℝ) (G : ℝ≥0) (ε : ℝ)
    (hε : 0 < ε) (hg : ∀ v, |g v| ≤ (G : ℝ)) :
    Hagi.Model.LMCompose.CertifiedBlock V where
  attn := fun x t => x t
  norm := fun z v => g v * rmsN ε z v
  nH := 1
  nKv := 1
  d := 1
  lip := ⟨1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε),
    by positivity⟩
  hLip := by
    intro x y t
    -- per-coordinate residual + gain split
    have hcoord : ∀ i : ℕ, ∀ v : V,
        |(x i v + g v * rmsN ε (x i) v)
          - (y i v + g v * rmsN ε (y i) v)|
        ≤ |x i v - y i v|
          + (G : ℝ) * |rmsN ε (x i) v - rmsN ε (y i) v| := by
      intro i v
      have hsplit : (x i v + g v * rmsN ε (x i) v)
          - (y i v + g v * rmsN ε (y i) v)
        = (x i v - y i v)
          + g v * (rmsN ε (x i) v - rmsN ε (y i) v) := by ring
      rw [hsplit]
      refine le_trans (abs_add_le (x i v - y i v)
        (g v * (rmsN ε (x i) v - rmsN ε (y i) v))) ?_
      have hgain : |g v * (rmsN ε (x i) v - rmsN ε (y i) v)|
        ≤ (G : ℝ) * |rmsN ε (x i) v - rmsN ε (y i) v| :=
        calc |g v * (rmsN ε (x i) v - rmsN ε (y i) v)|
            = |g v| * |rmsN ε (x i) v - rmsN ε (y i) v| := abs_mul _ _
          _ ≤ (G : ℝ) * |rmsN ε (x i) v - rmsN ε (y i) v| :=
              mul_le_mul_of_nonneg_right (hg v) (abs_nonneg _)
      exact add_le_add le_rfl hgain
    -- per-position ℓ1 bound via the derived RMSNorm constant
    have hpos : ∀ i : ℕ,
        (∑ v, |(x i v + g v * rmsN ε (x i) v)
          - (y i v + g v * rmsN ε (y i) v)|)
        ≤ (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
          * ∑ v, |x i v - y i v| := by
      intro i
      have hlip := rmsN_l1_lip ε hε (x i) (y i)
      calc (∑ v, |(x i v + g v * rmsN ε (x i) v)
            - (y i v + g v * rmsN ε (y i) v)|)
          ≤ ∑ v, (|x i v - y i v|
            + (G : ℝ) * |rmsN ε (x i) v - rmsN ε (y i) v|) :=
            Finset.sum_le_sum (fun v _ => hcoord i v)
        _ = (∑ v, |x i v - y i v|)
            + (G : ℝ) * (∑ v, |rmsN ε (x i) v - rmsN ε (y i) v|) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ (∑ v, |x i v - y i v|)
            + (G : ℝ) * ((((Fintype.card V : ℝ) + 1) / ε)
              * ∑ v, |x i v - y i v|) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hlip
              (NNReal.coe_nonneg _))
        _ = (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
            * ∑ v, |x i v - y i v| := by ring
    -- assemble dPre
    show (∑ i ∈ Finset.range (t + 1),
            ∑ v, |x i v + g v * rmsN ε (x i) v
              - (y i v + g v * rmsN ε (y i) v)|)
        ≤ (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
            * ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v|
    calc (∑ i ∈ Finset.range (t + 1),
            ∑ v, |x i v + g v * rmsN ε (x i) v
              - (y i v + g v * rmsN ε (y i) v)|)
        ≤ ∑ i ∈ Finset.range (t + 1),
            (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
            * ∑ v, |x i v - y i v| :=
          Finset.sum_le_sum (fun i _ => hpos i)
      _ = (1 + (G : ℝ) * (((Fintype.card V : ℝ) + 1) / ε))
            * ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v| :=
          (Finset.mul_sum _ _ _).symm
  hCausal := by
    intro x y t hagree v
    have hfun : x t = y t := funext (hagree t (Nat.le_refl t))
    simp only [Hagi.Model.LMCompose.blockApply, hfun]

end RMS

/-! ## (b) MLP atom: relu + two linear layers, √n·‖W₂‖_F·‖W₁‖_F -/

/-- ReLU activation (explicit branch). -/
noncomputable def relu (z : ℝ) : ℝ := if 0 ≤ z then z else 0

/-- ReLU is 1-Lipschitz coordinatewise (4-case split; no ReLU lemma
in the corpus — NormAct has swish only). -/
theorem relu_lip_abs (a b : ℝ) :
    |relu a - relu b| ≤ |a - b| := by
  unfold relu
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [if_pos ha, if_pos hb]
    · rw [if_pos ha, if_neg hb, sub_zero, abs_of_nonneg ha,
        abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
  · by_cases hb : 0 ≤ b
    · rw [if_neg ha, if_pos hb, zero_sub, abs_neg,
        abs_of_nonneg hb, abs_of_nonpos (by linarith : a - b ≤ 0)]
      linarith
    · rw [if_neg ha, if_neg hb, sub_self, abs_zero]
      exact abs_nonneg _

/-- MLP atom: `x ↦ W₂ · relu (W₁ · x)` with matrices as plain
`V → V → ℝ` functions (KISS: no Matrix type needed for the ℓ1
estimate). -/
noncomputable def mlpApply (W₁ W₂ : V → V → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  ∑ j, W₂ v j * relu (∑ k, W₁ j k * x k)

/-- The MLP atom is ℓ1-Lipschitz with constant
`√n·‖W₂‖_F·‖W₁‖_F`: per-layer chain of row Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`, C426 mechanic — first-layer
Frobenius leg CITED from `BlockSmooth.linear_lipschitz_frobenius`
style), relu 1-Lip, and ℓ2→ℓ1 bridges. -/
theorem mlp_l1_lip (W₁ W₂ : V → V → ℝ) (x y : V → ℝ) :
    (∑ v, |mlpApply W₁ W₂ x v - mlpApply W₁ W₂ y v|)
      ≤ Real.sqrt (Fintype.card V)
        * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
        * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
        * ∑ k, |x k - y k| := by
  classical
  set d : V → ℝ := fun k => |x k - y k| with hd
  -- first-layer difference is a plain linear difference
  have hlin : ∀ j : V,
      (∑ k, W₁ j k * x k) - ∑ k, W₁ j k * y k
        = ∑ k, W₁ j k * (x k - y k) := by
    intro j
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- relu difference bound
  have hmid : ∀ j : V,
      |relu (∑ k, W₁ j k * x k) - relu (∑ k, W₁ j k * y k)|
        ≤ ∑ k, |W₁ j k| * d k := by
    intro j
    refine le_trans (relu_lip_abs _ _) ?_
    rw [hlin j]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun k _ => le_of_eq (abs_mul _ _)
  -- coordinate pull-through
  have hpt : ∀ v : V, |mlpApply W₁ W₂ x v - mlpApply W₁ W₂ y v|
      ≤ ∑ j, ∑ k, |W₂ v j| * |W₁ j k| * d k := by
    intro v
    have hdiff : mlpApply W₁ W₂ x v - mlpApply W₁ W₂ y v
        = ∑ j, W₂ v j * (relu (∑ k, W₁ j k * x k)
          - relu (∑ k, W₁ j k * y k)) := by
      unfold mlpApply
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (mul_sub _ _ _).symm
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    calc |W₂ v j * (relu (∑ k, W₁ j k * x k)
          - relu (∑ k, W₁ j k * y k))|
        = |W₂ v j| * |relu (∑ k, W₁ j k * x k)
          - relu (∑ k, W₁ j k * y k)| :=
          abs_mul _ _
      _ ≤ |W₂ v j| * ∑ k, |W₁ j k| * d k :=
          mul_le_mul_of_nonneg_left (hmid j) (abs_nonneg _)
      _ = ∑ k, |W₂ v j| * |W₁ j k| * d k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  set FB : ℝ := Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2) with hFB
  set FA : ℝ := Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2) with hFA
  have hFBn : 0 ≤ FB := Real.sqrt_nonneg _
  have hFAn : 0 ≤ FA := Real.sqrt_nonneg _
  have hFBsq : FB ^ 2 = ∑ v, ∑ j, W₂ v j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun v _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hFAsq : FA ^ 2 = ∑ j, ∑ k, W₁ j k ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)
  -- leg 1: ℓ1 ≤ √n·ℓ2 per column of W₂
  have hleg1 : ∀ j : V, (∑ v, |W₂ v j|)
      ≤ Real.sqrt (Fintype.card V)
        * Real.sqrt (∑ v, W₂ v j ^ 2) := by
    intro j
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : V => (1:ℝ)) (fun v => |W₂ v j|)
    simp only [one_mul, one_pow] at hcs
    have hcardsum : (∑ v : V, (1:ℝ)) = (Fintype.card V : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hcardsum] at hcs
    have habs2 : ∑ v, |W₂ v j| ^ 2 = ∑ v, W₂ v j ^ 2 :=
      Finset.sum_congr rfl fun v _ => sq_abs _
    have hcs2 : (∑ v, |W₂ v j|) ^ 2
        ≤ (Fintype.card V : ℝ) * ∑ v, W₂ v j ^ 2 :=
      hcs.trans_eq (by rw [habs2])
    have hp : (0:ℝ) ≤ ∑ v, |W₂ v j| :=
      Finset.sum_nonneg fun v _ => abs_nonneg _
    have hcard : (0:ℝ) ≤ (Fintype.card V : ℝ) := by positivity
    have hS : (0:ℝ) ≤ ∑ v, W₂ v j ^ 2 :=
      Finset.sum_nonneg fun v _ => sq_nonneg _
    have hsN := Real.sq_sqrt hcard
    have hsS := Real.sq_sqrt hS
    have h2 : (∑ v, |W₂ v j|) ^ 2
        ≤ (Real.sqrt (Fintype.card V)
          * Real.sqrt (∑ v, W₂ v j ^ 2)) ^ 2 := by
      rw [mul_pow, hsN, hsS]
      exact hcs2
    have h3 := Real.sqrt_le_sqrt h2
    have h4 : Real.sqrt ((Real.sqrt (Fintype.card V)
        * Real.sqrt (∑ v, W₂ v j ^ 2)) ^ 2)
        = Real.sqrt (Fintype.card V)
          * Real.sqrt (∑ v, W₂ v j ^ 2) :=
      Real.sqrt_sq (by positivity)
    have h5 : Real.sqrt ((∑ v, |W₂ v j|) ^ 2) = ∑ v, |W₂ v j| :=
      Real.sqrt_sq hp
    rw [h5, h4] at h3
    exact h3
  -- per-column inner-product bound via C-S over j
  have hI : ∀ k : V, (∑ v, ∑ j, |W₂ v j| * |W₁ j k|)
      ≤ Real.sqrt (Fintype.card V) * FB * FA := by
    intro k
    have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : V => |W₁ j k|) (fun j => ∑ v, |W₂ v j|)
    have hcard : (0:ℝ) ≤ (Fintype.card V : ℝ) := by positivity
    have hinner : (∑ v, ∑ j, |W₂ v j| * |W₁ j k|)
        = ∑ j, |W₁ j k| * ∑ v, |W₂ v j| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => mul_comm _ _
    -- column of W₁ inside the Frobenius ball
    have hcolA : (∑ j, |W₁ j k| ^ 2) ≤ FA ^ 2 := by
      have h1 : (∑ j, |W₁ j k| ^ 2) = ∑ j, W₁ j k ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [sq_abs]
      have h2 : (∑ j, W₁ j k ^ 2) ≤ ∑ j, ∑ k', W₁ j k' ^ 2 :=
        Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (f := fun k' => W₁ j k' ^ 2)
            (fun k' _ => sq_nonneg _) (Finset.mem_univ k)
      rw [h1, hFAsq]
      exact h2
    -- squared column sums of W₂
    have hswap : (∑ j, ∑ v, W₂ v j ^ 2) = ∑ v, ∑ j, W₂ v j ^ 2 :=
      Finset.sum_comm
    have hper : ∀ j : V, (∑ v, |W₂ v j|) ^ 2
        ≤ (Fintype.card V : ℝ) * ∑ v, W₂ v j ^ 2 := by
      intro j
      have h1 := hleg1 j
      have hp : (0:ℝ) ≤ ∑ v, |W₂ v j| :=
        Finset.sum_nonneg fun v _ => abs_nonneg _
      have hS : (0:ℝ) ≤ ∑ v, W₂ v j ^ 2 :=
        Finset.sum_nonneg fun v _ => sq_nonneg _
      have hsq : (∑ v, |W₂ v j|) ^ 2
          ≤ (Real.sqrt (Fintype.card V)
            * Real.sqrt (∑ v, W₂ v j ^ 2)) ^ 2 := by
        have hs0 : (0:ℝ) ≤ Real.sqrt (Fintype.card V)
          * Real.sqrt (∑ v, W₂ v j ^ 2) := by positivity
        nlinarith [h1, hp, hs0]
      have hexp : (Real.sqrt (Fintype.card V)
          * Real.sqrt (∑ v, W₂ v j ^ 2)) ^ 2
          = (Fintype.card V : ℝ) * ∑ v, W₂ v j ^ 2 := by
        rw [← Real.sqrt_mul hcard, Real.sq_sqrt
          (mul_nonneg hcard hS)]
      exact hsq.trans (by rw [hexp])
    have hcolB' : (∑ j, (∑ v, |W₂ v j|) ^ 2)
        ≤ (Fintype.card V : ℝ) * FB ^ 2 := by
      have h4 : FB ^ 2 = ∑ j, ∑ v, W₂ v j ^ 2 := hFBsq.trans hswap.symm
      calc (∑ j, (∑ v, |W₂ v j|) ^ 2)
          ≤ ∑ j, ((Fintype.card V : ℝ) * ∑ v, W₂ v j ^ 2) :=
            Finset.sum_le_sum fun j _ => hper j
        _ = (Fintype.card V : ℝ) * ∑ j, ∑ v, W₂ v j ^ 2 := by
            rw [← Finset.mul_sum]
        _ = (Fintype.card V : ℝ) * FB ^ 2 := by rw [h4]
    -- explicit multiplicative chain (no nlinarith on squares)
    have hnA : (0:ℝ) ≤ ∑ j, |W₁ j k| ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hnB : (0:ℝ) ≤ ∑ j, (∑ v, |W₂ v j|) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hFA2 : (0:ℝ) ≤ FA ^ 2 := sq_nonneg _
    have hFB2 : FB ^ 2 = ∑ v, ∑ j, W₂ v j ^ 2 := hFBsq
    have step1 : (∑ j, |W₁ j k| ^ 2) * (∑ j, (∑ v, |W₂ v j|) ^ 2)
        ≤ FA ^ 2 * (∑ j, (∑ v, |W₂ v j|) ^ 2) :=
      mul_le_mul_of_nonneg_right hcolA hnB
    have hC : (∑ j, (∑ v, |W₂ v j|) ^ 2)
        ≤ (Fintype.card V : ℝ) * FB ^ 2 := hcolB'
    have step2 : FA ^ 2 * (∑ j, (∑ v, |W₂ v j|) ^ 2)
        ≤ FA ^ 2 * ((Fintype.card V : ℝ) * FB ^ 2) :=
      mul_le_mul_of_nonneg_left hC hFA2
    have hnonneg : (0:ℝ) ≤ ∑ v, ∑ j, |W₂ v j| * |W₁ j k| :=
      Finset.sum_nonneg fun v _ =>
        Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hprod : (0:ℝ) ≤ Real.sqrt (Fintype.card V) * FB * FA := by positivity
    have hgoal2 : (∑ v, ∑ j, |W₂ v j| * |W₁ j k|) ^ 2
        ≤ (Real.sqrt (Fintype.card V) * FB * FA) ^ 2 := by
      rw [hinner]
      have htgt : (Real.sqrt (Fintype.card V) * FB * FA) ^ 2
          = FA ^ 2 * ((Fintype.card V : ℝ) * FB ^ 2) := by
        have hsN : (Real.sqrt (Fintype.card V)) ^ 2
            = (Fintype.card V : ℝ) :=
          Real.sq_sqrt hcard
        have e1 : (Real.sqrt (Fintype.card V) * FB) ^ 2
            = (Fintype.card V : ℝ) * FB ^ 2 := by
          nlinarith [hsN, hFBn]
        rw [mul_pow, e1]
        ring
      have h1 := hcs2
      nlinarith [h1, step1, step2, htgt, hnA, hnB, hFA2, hcard]
    calc (∑ v, ∑ j, |W₂ v j| * |W₁ j k|)
        = Real.sqrt ((∑ v, ∑ j, |W₂ v j| * |W₁ j k|) ^ 2) :=
          (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt ((Real.sqrt (Fintype.card V) * FB * FA) ^ 2) :=
          Real.sqrt_le_sqrt hgoal2
      _ = Real.sqrt (Fintype.card V) * FB * FA := Real.sqrt_sq hprod
  -- interchange the k-sum to the outside and assemble
  have hcomm1 : (∑ v, ∑ j, ∑ k, |W₂ v j| * |W₁ j k| * d k)
      = ∑ v, ∑ k, ∑ j, |W₂ v j| * |W₁ j k| * d k :=
    Finset.sum_congr rfl fun v _ => Finset.sum_comm
  have hcomm2 : (∑ v, ∑ k, ∑ j, |W₂ v j| * |W₁ j k| * d k)
      = ∑ k, ∑ v, ∑ j, |W₂ v j| * |W₁ j k| * d k := Finset.sum_comm
  have hpull : (∑ k, ∑ v, ∑ j, |W₂ v j| * |W₁ j k| * d k)
      = ∑ k, d k * (∑ v, ∑ j, |W₂ v j| * |W₁ j k|) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (d k) (∑ v, ∑ j, |W₂ v j| * |W₁ j k|)]
    simp only [Finset.sum_mul]
  calc (∑ v, |mlpApply W₁ W₂ x v - mlpApply W₁ W₂ y v|)
      ≤ ∑ k, d k * (∑ v, ∑ j, |W₂ v j| * |W₁ j k|) := by
        exact (Finset.sum_le_sum fun v _ => hpt v).trans
          (by rw [hcomm1, hcomm2, hpull])
    _ ≤ ∑ k, d k * (Real.sqrt (Fintype.card V) * FB * FA) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hI k) (abs_nonneg _)
    _ = Real.sqrt (Fintype.card V) * FB * FA * ∑ k, d k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- CertifiedBlock for the MLP atom (attn = id, norm = mlpApply):
`hLip` DERIVED with lip = `1 + √n·‖W₂‖_F·‖W₁‖_F` (residual +
derived MLP constant), `hCausal` DERIVED (positional). -/
noncomputable def certifiedMLP (W₁ W₂ : V → V → ℝ) :
    Hagi.Model.LMCompose.CertifiedBlock V where
  attn := fun x t => x t
  norm := mlpApply W₁ W₂
  nH := 1
  nKv := 1
  d := 1
  lip := ⟨1 + Real.sqrt (Fintype.card V)
    * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
    * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2), by positivity⟩
  hLip := by
    intro x y t
    have hcoord : ∀ i : ℕ, ∀ v : V,
        |(x i v + mlpApply W₁ W₂ (x i) v)
          - (y i v + mlpApply W₁ W₂ (y i) v)|
        ≤ |x i v - y i v|
          + |mlpApply W₁ W₂ (x i) v - mlpApply W₁ W₂ (y i) v| := by
      intro i v
      have hsplit : (x i v + mlpApply W₁ W₂ (x i) v)
          - (y i v + mlpApply W₁ W₂ (y i) v)
        = (x i v - y i v)
          + (mlpApply W₁ W₂ (x i) v - mlpApply W₁ W₂ (y i) v) := by
        ring
      rw [hsplit]
      exact abs_add_le _ _
    have hpos : ∀ i : ℕ,
        (∑ v, |(x i v + mlpApply W₁ W₂ (x i) v)
          - (y i v + mlpApply W₁ W₂ (y i) v)|)
        ≤ (1 + Real.sqrt (Fintype.card V)
          * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
          * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
          * ∑ v, |x i v - y i v| := by
      intro i
      have hlip := mlp_l1_lip W₁ W₂ (x i) (y i)
      calc (∑ v, |(x i v + mlpApply W₁ W₂ (x i) v)
            - (y i v + mlpApply W₁ W₂ (y i) v)|)
          ≤ ∑ v, (|x i v - y i v|
            + |mlpApply W₁ W₂ (x i) v - mlpApply W₁ W₂ (y i) v|) :=
            Finset.sum_le_sum (fun v _ => hcoord i v)
        _ = (∑ v, |x i v - y i v|)
            + ∑ v, |mlpApply W₁ W₂ (x i) v
              - mlpApply W₁ W₂ (y i) v| := Finset.sum_add_distrib
        _ ≤ (∑ v, |x i v - y i v|)
            + (Real.sqrt (Fintype.card V)
              * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
              * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2)
              * ∑ v, |x i v - y i v|) :=
            add_le_add le_rfl hlip
        _ = (1 + Real.sqrt (Fintype.card V)
              * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
              * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
            * ∑ v, |x i v - y i v| := by ring
    show (∑ i ∈ Finset.range (t + 1),
            ∑ v, |x i v + mlpApply W₁ W₂ (x i) v
              - (y i v + mlpApply W₁ W₂ (y i) v)|)
        ≤ (1 + Real.sqrt (Fintype.card V)
            * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
            * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
            * ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v|
    calc (∑ i ∈ Finset.range (t + 1),
            ∑ v, |x i v + mlpApply W₁ W₂ (x i) v
              - (y i v + mlpApply W₁ W₂ (y i) v)|)
        ≤ ∑ i ∈ Finset.range (t + 1),
            (1 + Real.sqrt (Fintype.card V)
              * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
              * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
            * ∑ v, |x i v - y i v| :=
          Finset.sum_le_sum (fun i _ => hpos i)
      _ = (1 + Real.sqrt (Fintype.card V)
            * Real.sqrt (∑ v, ∑ j, W₂ v j ^ 2)
            * Real.sqrt (∑ j, ∑ k, W₁ j k ^ 2))
            * ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v| :=
          (Finset.mul_sum _ _ _).symm
  hCausal := by
    intro x y t hagree v
    have hfun : x t = y t := funext (hagree t (Nat.le_refl t))
    simp only [Hagi.Model.LMCompose.blockApply, hfun]

/-! ## (c) Bounded-weight causal attention atom: lip = 2 -/

/-- Geometric-decay attention weight `w k = (1/2)^(k+1)` (row sum
≤ 1 — convex combination; column sum ≤ 1 — geometric tail). -/
noncomputable def attW (k : ℕ) : ℝ := (2:ℝ)⁻¹ ^ (k + 1)

/-- Exact geometric partial sum for the decay weights. -/
theorem attW_sum_eq (m : ℕ) :
    ∑ k ∈ Finset.range m, attW k = 1 - (2:ℝ)⁻¹ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hhalf : (2:ℝ)⁻¹ ^ (m + 1) * 2 = (2:ℝ)⁻¹ ^ m := by
        rw [pow_succ]
        field_simp
      unfold attW
      linarith

/-- Causal aggregator with geometric-decay weights: position `t`
reads positions `i ≤ t` only. -/
noncomputable def attAgg (x : ℕ → V → ℝ) (t : ℕ) (v : V) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), attW (t - i) * x i v

/-- Triangular interchange + geometric tail: the weighted prefix sum
with column sums ≤ 1 is dominated by the unweighted prefix sum. -/
theorem attAgg_tri (D : ℕ → ℝ) (hD : ∀ i, 0 ≤ D i) (t : ℕ) :
    (∑ s ∈ Finset.range (t + 1),
        ∑ i ∈ Finset.range (s + 1), attW (s - i) * D i)
      ≤ ∑ i ∈ Finset.range (t + 1), D i := by
  have hstep : ∀ s ∈ Finset.range (t + 1),
      (∑ i ∈ Finset.range (s + 1), attW (s - i) * D i)
      = ∑ i ∈ Finset.range (t + 1),
          (if i ≤ s then attW (s - i) * D i else 0) := by
    intro s hs
    have hsle : s < t + 1 := Finset.mem_range.mp hs
    have hfil : (Finset.range (s + 1))
        = (Finset.range (t + 1)).filter (fun i => i ≤ s) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [hfil, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun s hs => hstep s hs), Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  -- factor out D i
  have hfactor : (∑ s ∈ Finset.range (t + 1),
      (if i ≤ s then attW (s - i) * D i else 0))
      = D i * ∑ s ∈ Finset.range (t + 1),
          (if i ≤ s then attW (s - i) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      by_cases h : i ≤ s <;> simp [h, mul_comm]
  rw [hfactor]
  have h1 : (∑ s ∈ Finset.range (t + 1),
      (if i ≤ s then attW (s - i) else 0)) ≤ 1 := by
    by_cases hi : i ≤ t
    · -- tail: filter to Ico, shift, geometric sum ≤ 1
      have hfilter : ∑ s ∈ Finset.range (t + 1),
          (if i ≤ s then attW (s - i) else 0)
          = ∑ s ∈ (Finset.range (t + 1)).filter (fun s => i ≤ s),
              attW (s - i) := (Finset.sum_filter _ _).symm
      have hIco : (Finset.range (t + 1)).filter (fun s => i ≤ s)
          = Finset.Ico i (t + 1) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_range,
          Finset.mem_Ico]
        omega
      rw [hfilter, hIco, Finset.sum_Ico_eq_sum_range]
      have hshift : (∑ k ∈ Finset.range (t + 1 - i),
          attW (i + k - i))
          = ∑ k ∈ Finset.range (t + 1 - i), attW k :=
        Finset.sum_congr rfl fun k _ => by
          unfold attW
          congr 1
          omega
      rw [hshift, attW_sum_eq]
      have hpw : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ (t + 1 - i) := by positivity
      linarith
    · -- i > t: every term is zero
      have hz : ∀ s ∈ Finset.range (t + 1), ¬ i ≤ s := by
        intro s hs
        have := Finset.mem_range.mp hs
        omega
      exact (Finset.sum_eq_zero fun s hs => if_neg (hz s hs)).le.trans
        zero_le_one
  nlinarith [h1, hD i]

/-- CertifiedBlock for the bounded-weight causal attention atom
(attn = attAgg, norm = id): `hLip` DERIVED with lip = 2
(residual + column-sum ≤ 1 contraction), `hCausal` DERIVED
(support `i ≤ t` only). -/
noncomputable def certifiedConvAtt : Hagi.Model.LMCompose.CertifiedBlock V where
  attn := attAgg
  norm := fun z v => z v
  nH := 1
  nKv := 1
  d := 1
  lip := 2
  hLip := by
    intro x y t
    have hWn : ∀ k : ℕ, 0 ≤ attW k := fun k => by
      unfold attW
      positivity
    have hagg : ∀ s : ℕ, ∀ v : V,
        |attAgg x s v - attAgg y s v|
        ≤ ∑ i ∈ Finset.range (s + 1),
            attW (s - i) * |x i v - y i v| := by
      intro s v
      have hdiff : attAgg x s v - attAgg y s v
          = ∑ i ∈ Finset.range (s + 1),
              attW (s - i) * (x i v - y i v) := by
        unfold attAgg
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
      rw [hdiff]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hWn _)]
    have hpos : ∀ s : ℕ,
        (∑ v, |attAgg x s v - attAgg y s v|)
        ≤ ∑ i ∈ Finset.range (s + 1),
            attW (s - i) * (∑ v, |x i v - y i v|) := by
      intro s
      calc (∑ v, |attAgg x s v - attAgg y s v|)
          ≤ ∑ v, ∑ i ∈ Finset.range (s + 1),
              attW (s - i) * |x i v - y i v| :=
            Finset.sum_le_sum fun v _ => hagg s v
        _ = ∑ i ∈ Finset.range (s + 1),
            ∑ v, attW (s - i) * |x i v - y i v| := Finset.sum_comm
        _ = ∑ i ∈ Finset.range (s + 1),
            attW (s - i) * (∑ v, |x i v - y i v|) :=
            Finset.sum_congr rfl fun i _ =>
              (Finset.mul_sum _ _ _).symm
    have hD : ∀ i, 0 ≤ ∑ v, |x i v - y i v| :=
      fun i => Finset.sum_nonneg fun v _ => abs_nonneg _
    have htri := attAgg_tri (fun i => ∑ v, |x i v - y i v|) hD t
    change (∑ s ∈ Finset.range (t + 1),
            ∑ v, |x s v + attAgg x s v
              - (y s v + attAgg y s v)|)
        ≤ 2 * ∑ s ∈ Finset.range (t + 1), ∑ v, |x s v - y s v|
    have hsplit : ∀ s ∈ Finset.range (t + 1), ∀ v : V,
        (x s v + attAgg x s v) - (y s v + attAgg y s v)
        = (x s v - y s v)
          + (attAgg x s v - attAgg y s v) := by
      intro s _ v
      ring
    have hterm : ∀ s ∈ Finset.range (t + 1), ∀ v : V,
        |x s v + attAgg x s v - (y s v + attAgg y s v)|
        ≤ |x s v - y s v| + |attAgg x s v - attAgg y s v| := by
      intro s hs v
      rw [hsplit s hs v]
      exact abs_add_le _ _
    calc (∑ s ∈ Finset.range (t + 1),
            ∑ v, |x s v + attAgg x s v - (y s v + attAgg y s v)|)
        ≤ ∑ s ∈ Finset.range (t + 1),
            ∑ v, (|x s v - y s v|
              + |attAgg x s v - attAgg y s v|) :=
          Finset.sum_le_sum fun s hs =>
            Finset.sum_le_sum fun v _ => hterm s hs v
      _ = (∑ s ∈ Finset.range (t + 1), ∑ v, |x s v - y s v|)
          + ∑ s ∈ Finset.range (t + 1),
              ∑ v, |attAgg x s v - attAgg y s v| := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => Finset.sum_add_distrib
      _ ≤ (∑ s ∈ Finset.range (t + 1), ∑ v, |x s v - y s v|)
          + ∑ s ∈ Finset.range (t + 1), ∑ i ∈ Finset.range (s + 1),
              attW (s - i) * (∑ v, |x i v - y i v|) :=
          add_le_add le_rfl (Finset.sum_le_sum fun s _ => hpos s)
      _ ≤ (∑ s ∈ Finset.range (t + 1), ∑ v, |x s v - y s v|)
          + ∑ i ∈ Finset.range (t + 1), ∑ v, |x i v - y i v| :=
          add_le_add le_rfl htri
      _ = 2 * ∑ s ∈ Finset.range (t + 1), ∑ v, |x s v - y s v| := by ring
  hCausal := by
    intro x y t hagree v
    have hfun : ∀ i ∈ Finset.range (t + 1), x i = y i := by
      intro i hi
      have := Finset.mem_range.mp hi
      exact funext (hagree i (by omega))
    simp only [Hagi.Model.LMCompose.blockApply]
    have hxA : attAgg x t v = attAgg y t v := by
      unfold attAgg
      exact Finset.sum_congr rfl fun i hi => by rw [hfun i hi]
    rw [hxA, hfun t (Finset.mem_range.mpr (Nat.lt_succ_self t))]

end Hagi.Theory.BlockLipschitz
