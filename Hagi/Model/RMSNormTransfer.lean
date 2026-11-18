/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Hagi.Model.AttentionTransfer
import Hagi.Model.RMSNorm

set_option linter.style.header false

/-!
# RMSNorm Lipschitz constant discharge (E4 rmsnorm rung)

The rmsnorm rung of the E4 backbone ladder (TD E4-C300/C307 notes:
"Lipschitz для RMSNorm premise-form (μn, звено 4)"): the pre-norm
`LipschitzWith μn` premise of the C307 attention transfer stack is
discharged into explicit constants, matched to the EXACT carrier
definition `Hagi.Model.RMSNorm.rnVec x i = x i / sqrt (ms x)` — the
PURE Zhang–Sennrich base form (no ε-floor, no affine weight `g`).

Honest-constant verdict (what is TRUE for this carrier):

* `rnEuc_not_lipschitz_with` — the honest NEGATIVE: the pure carrier
  is NOT Lipschitz on the whole space (`n ≥ 2`): near zero the
  directions `δ•eₐ`, `δ•e_b` map to the FIXED unit-RMS directions
  `√n•eₐ`, `√n•e_b` while their distance shrinks like `δ√2 → 0`.
* `rn_lipschitz_region` — the region discharge `μn(r) = 2√n/r`: on
  `{z | r ≤ ‖z‖}` the pure carrier RMSNorm is `(2√n/r)`-Lipschitz
  (via the radial form `rnEuc x = (√n/‖x‖)•x` and the reverse
  triangle inequality).
* `rnEpsEuc_lipschitz` — the ε-floor discharge `μn(ε) = 2/√ε`: the
  ε-floored variant `rnEpsEuc ε x i = x i / sqrt (msE x + ε)` is
  GLOBALLY `(2/√ε)`-Lipschitz (via the exact conjugate identity
  `(gy−gx)(gy+gx) = △msE` and Euclidean Cauchy–Schwarz
  `msE_abs_sub_le`; no calculus). This is the honest global
  surrogate through which the STACK theorem discharges μn.

Wiring into the C300/C307 stack:

* `residual_transfer_le_pointwise` — the C300 leak bound at a step
  from a POINTWISE branch-response bound (no global Lipschitz).
* `attention_block_transfer_rmsnorm` — THE rung theorem: the C307
  attention block theorem with μn DISCHARGED as `μn(r) = 2√n/r`
  (region premises on both step endpoints), composed leak constant
  `Lc·((2√n/r)·μatt)` explicit.
* `attention_stack_transfer_rmsnorm_eps` (+ `_strict`) — the C307
  stack descent theorem instantiated with the ε-floored pre-norms
  and the explicit global constant `μnEps ε hε = 2/√ε`.

Carrier transport: `rnEuc`/`rnEpsEuc` act on
`EuclideanSpace ℝ (Fin n)` pointwise through `WithLp.ofLp`/`toLp`
(the transfer stack's abstract carrier), with
`norm_eq_sqrt : ‖x‖ = √n·√(msE x)` the exact norm bridge.

Anchors (n = 4): the region constant `2·√4/1 = 4`, and
`‖rnEuc (3,4,0,0)‖ = 2` (unit-RMS output; the 3-4-5 triangle through
`rnEuc_eq` + `norm_eq_sqrt`).

Honest scope: no global Lipschitz claim for the PURE carrier (pinned
as the negative above); the carrier has NO affine weight `g`, so no
`g`-scaling appears in the constants (were a `g` added later, the
constants scale by `max |g|`); the softmax weight-map Lipschitz stays
premise-form (C307); the full FastArch3 forward/backward certificate
is NOT claimed here.
-/

namespace Hagi.Model.RMSNormTransfer

open Finset Hagi.Model.RMSNorm Hagi.Model.Residual Hagi.Model.BackboneTransfer
  Hagi.Model.AttentionTransfer


/-- mean square on the Euclidean carrier -/
noncomputable def msE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ms (WithLp.ofLp x)

/-- RMSNorm on the Euclidean carrier: pointwise the carrier rnVec. -/
noncomputable def rnEuc {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (rnVec (WithLp.ofLp x))

/-- ε-floored RMSNorm on the Euclidean carrier. -/
noncomputable def rnEpsEuc {n : ℕ} (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (WithLp.ofLp x) i / Real.sqrt (msE x + ε))

theorem msE_nonneg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ msE x := by
  unfold msE ms
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · positivity

theorem msE_pos {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < msE x := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact absurd (show x = 0 from by ext i; exact i.elim0) hx
  refine lt_of_le_of_ne (msE_nonneg x) (fun h => hx ?_)
  have hsum : ∑ i, ((WithLp.ofLp x) i) ^ 2 = 0 := by
    have h1 : (∑ i, ((WithLp.ofLp x) i) ^ 2) / n = 0 := by
      simpa [msE, ms] using h.symm
    rcases (div_eq_zero_iff).mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (by positivity)
  have hz : ∀ i, (WithLp.ofLp x) i = 0 := by
    intro i
    have hq := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg _)).mp hsum i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hq
  ext i
  simpa using hz i

theorem norm_eq_sqrt {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ = Real.sqrt n * Real.sqrt (msE x) := by
  have hn : (0:ℝ) ≤ n := by positivity
  have hsq : ‖x‖ ^ 2 = n * msE x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [msE, ms]
    cases n with
    | zero => simp
    | succ m =>
        rw [mul_div_cancel₀ _ (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)]
  have h2 : (Real.sqrt n * Real.sqrt (msE x)) ^ 2 = n * msE x := by
    rw [mul_pow, Real.sq_sqrt hn, Real.sq_sqrt (msE_nonneg x)]
  exact (sq_eq_sq₀ (norm_nonneg x) (by positivity)).mp (hsq.trans h2.symm)


/-- On the nonzero region the carrier RMSNorm is the radial unit-RMS
rescaling `x → (√n / ‖x‖) • x`. -/
theorem rnEuc_eq {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    rnEuc x = (Real.sqrt n / ‖x‖) • x := by
  have hn : (0:ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd (show x = 0 from by ext i; exact i.elim0) hx
    · exact_mod_cast h0
  have hsn : Real.sqrt n ≠ 0 := by positivity
  have hxnn : ‖x‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  have hnorm := norm_eq_sqrt x
  have hms : Real.sqrt (msE x) = ‖x‖ / Real.sqrt n := by
    rw [hnorm, mul_div_cancel_left₀ _ hsn]
  ext i
  simp only [rnEuc, WithLp.ofLp_toLp, WithLp.ofLp_smul, rnVec,
    Pi.smul_apply, smul_eq_mul]
  rw [show Real.sqrt (ms (WithLp.ofLp x)) = ‖x‖ / Real.sqrt n from hms]
  field_simp

/-- Region Lipschitz: on `{z | r ≤ ‖z‖}` the pure carrier RMSNorm is
`(2√n/r)`-Lipschitz. -/
theorem rn_lipschitz_region {n : ℕ} {r : ℝ} (hr : 0 < r)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    ‖rnEuc x - rnEuc y‖ ≤ (2 * Real.sqrt n / r) * ‖x - y‖ := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; linarith
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; linarith
  have ha : (0:ℝ) < ‖x‖ := lt_of_lt_of_le hr hx
  have hb : (0:ℝ) < ‖y‖ := lt_of_lt_of_le hr hy
  have hsn : (0:ℝ) ≤ Real.sqrt n := by positivity
  rw [rnEuc_eq hx0, rnEuc_eq hy0]
  have hsplit : (Real.sqrt n / ‖x‖) • x - (Real.sqrt n / ‖y‖) • y
      = (Real.sqrt n / ‖x‖) • (x - y)
        + ((Real.sqrt n / ‖x‖) - (Real.sqrt n / ‖y‖)) • y := by
    module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have ht1 : ‖(Real.sqrt n / ‖x‖) • (x - y)‖
      = (Real.sqrt n / ‖x‖) * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hsn ha.le)]
  have ht2 : ‖((Real.sqrt n / ‖x‖) - (Real.sqrt n / ‖y‖)) • y‖
      = |(Real.sqrt n / ‖x‖) - (Real.sqrt n / ‖y‖)| * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have habs : |(Real.sqrt n / ‖x‖) - (Real.sqrt n / ‖y‖)| * ‖y‖
      = Real.sqrt n * |‖y‖ - ‖x‖| / ‖x‖ := by
    have he : (Real.sqrt n / ‖x‖) - (Real.sqrt n / ‖y‖)
        = Real.sqrt n * (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp
    rw [he, abs_div, abs_mul, abs_mul, abs_of_nonneg hsn,
      abs_of_pos ha, abs_of_pos hb]
    field_simp
  rw [ht1, ht2, habs]
  have hrev : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le y x
    simpa [norm_sub_rev] using h
  have hD : (0:ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hnd : (0:ℝ) ≤ Real.sqrt n * ‖x - y‖ := mul_nonneg hsn hD
  have hnp : (0:ℝ) ≤ Real.sqrt n / r * ‖x - y‖ :=
    mul_nonneg (div_nonneg hsn hr.le) hD
  have e1 : (Real.sqrt n / ‖x‖) * ‖x - y‖
      ≤ (Real.sqrt n / r) * ‖x - y‖ := by
    have h1 : Real.sqrt n / ‖x‖ ≤ Real.sqrt n / r := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ‖x‖) hr]
      exact mul_le_mul_of_nonneg_left hx hsn
    exact mul_le_mul_of_nonneg_right h1 hD
  have e2 : Real.sqrt n * |‖y‖ - ‖x‖| / ‖x‖
      ≤ (Real.sqrt n / r) * ‖x - y‖ := by
    have hstep : Real.sqrt n * |‖y‖ - ‖x‖| / ‖x‖
        ≤ Real.sqrt n * ‖x - y‖ / ‖x‖ := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ‖x‖)
        (by positivity : (0:ℝ) < ‖x‖)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrev hsn) ha.le
    have h5 : Real.sqrt n * ‖x - y‖ / ‖x‖
        ≤ Real.sqrt n * ‖x - y‖ / r := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ‖x‖) hr]
      exact mul_le_mul_of_nonneg_left hx hnd
    have h6 : Real.sqrt n * ‖x - y‖ / r
        = Real.sqrt n / r * ‖x - y‖ := by ring
    rw [h6] at h5
    exact le_trans hstep h5
  have hrb : (2 * Real.sqrt n / r) * ‖x - y‖
      = 2 * (Real.sqrt n / r * ‖x - y‖) := by ring
  rw [hrb]
  linarith



theorem rnEpsEuc_eq {n : ℕ} {ε : ℝ} (x : EuclideanSpace ℝ (Fin n)) :
    rnEpsEuc ε x = (1 / Real.sqrt (msE x + ε)) • x := by
  ext i
  simp only [rnEpsEuc, WithLp.ofLp_toLp, WithLp.ofLp_smul, msE,
    Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Inner-product bound: `n·|△msE| = |⟪(y+x, y−x)⟫| ≤ ‖y+x‖·‖y−x‖`. -/
theorem msE_abs_sub_le {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    n * |msE y - msE x| ≤ ‖y + x‖ * ‖y - x‖ := by
  cases n with
  | zero => rw [Nat.cast_zero, zero_mul]; positivity
  | succ m =>
      have hnn : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hS : (((m + 1 : ℕ) : ℝ)) * (msE y - msE x)
          = ∑ i, ((WithLp.ofLp y) i + (WithLp.ofLp x) i)
            * ((WithLp.ofLp y) i - (WithLp.ofLp x) i) := by
        unfold msE ms
        rw [← sub_div, ← Finset.sum_sub_distrib]
        field_simp
        exact Finset.sum_congr rfl fun i _ => by ring
      have hie : inner ℝ (y + x) (y - x)
          = ∑ i, ((WithLp.ofLp y) i + (WithLp.ofLp x) i)
            * ((WithLp.ofLp y) i - (WithLp.ofLp x) i) := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [RCLike.inner_apply]
        ring
      have hz : (0:ℝ) ≤ (((m + 1 : ℕ) : ℝ)) * |msE y - msE x| :=
        mul_nonneg (by positivity) (abs_nonneg _)
      calc (((m + 1 : ℕ) : ℝ)) * |msE y - msE x|
          = |(((m + 1 : ℕ) : ℝ)) * (msE y - msE x)| := by
              rw [abs_mul, abs_of_nonneg
                (show (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ) by positivity)]
        _ ≤ ‖y + x‖ * ‖y - x‖ := by
            rw [hS, ← hie]
            exact abs_real_inner_le_norm _ _

theorem rnEpsEuc_norm_sub_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖rnEpsEuc ε x - rnEpsEuc ε y‖ ≤ (2 / Real.sqrt ε) * ‖x - y‖ := by
  have hnn : (0:ℝ) ≤ Real.sqrt n := by positivity
  have hsqn : Real.sqrt n * Real.sqrt n = n :=
    Real.mul_self_sqrt (by positivity)
  have hgx : Real.sqrt ε ≤ Real.sqrt (msE x + ε) :=
    Real.sqrt_le_sqrt (by linarith [msE_nonneg x, hε])
  have hgy : Real.sqrt ε ≤ Real.sqrt (msE y + ε) :=
    Real.sqrt_le_sqrt (by linarith [msE_nonneg y, hε])
  have hgx0 : (0:ℝ) < Real.sqrt (msE x + ε) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 hε) hgx
  have hgy0 : (0:ℝ) < Real.sqrt (msE y + ε) :=
    lt_of_lt_of_le (Real.sqrt_pos.2 hε) hgy
  have hxle : ‖x‖ ≤ Real.sqrt n * Real.sqrt (msE x + ε) := by
    refine le_trans (norm_eq_sqrt x).le ?_
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith [msE_nonneg x, hε])) hnn
  have hyle : ‖y‖ ≤ Real.sqrt n * Real.sqrt (msE y + ε) := by
    refine le_trans (norm_eq_sqrt y).le ?_
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith [msE_nonneg y, hε])) hnn
  have hsum := msE_abs_sub_le x y
  rw [rnEpsEuc_eq, rnEpsEuc_eq]
  have hsplit : (1 / Real.sqrt (msE x + ε)) • x
      - (1 / Real.sqrt (msE y + ε)) • y
      = (1 / Real.sqrt (msE x + ε)) • (x - y)
        + ((1 / Real.sqrt (msE x + ε))
          - (1 / Real.sqrt (msE y + ε))) • y := by
    module
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have ht1 : ‖(1 / Real.sqrt (msE x + ε)) • (x - y)‖
      = (1 / Real.sqrt (msE x + ε)) * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one hgx0.le)]
  have ht2 : ‖((1 / Real.sqrt (msE x + ε))
      - (1 / Real.sqrt (msE y + ε))) • y‖
      = |(1 / Real.sqrt (msE x + ε))
        - (1 / Real.sqrt (msE y + ε))| * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hgd : |(1 / Real.sqrt (msE x + ε))
      - (1 / Real.sqrt (msE y + ε))|
      = |Real.sqrt (msE y + ε) - Real.sqrt (msE x + ε)|
        / (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε)) := by
    have he : (1 / Real.sqrt (msE x + ε))
        - (1 / Real.sqrt (msE y + ε))
        = (Real.sqrt (msE y + ε) - Real.sqrt (msE x + ε))
          / (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε)) := by
      field_simp
    rw [he, abs_div, abs_mul, abs_of_pos hgx0, abs_of_pos hgy0]
  have hsqd : (Real.sqrt (msE y + ε) - Real.sqrt (msE x + ε))
      * (Real.sqrt (msE y + ε) + Real.sqrt (msE x + ε))
      = msE y - msE x := by
    have h1 : (Real.sqrt (msE y + ε)) ^ 2 = msE y + ε :=
      Real.sq_sqrt (by linarith [msE_nonneg y, hε])
    have h2 : (Real.sqrt (msE x + ε)) ^ 2 = msE x + ε :=
      Real.sq_sqrt (by linarith [msE_nonneg x, hε])
    nlinarith [h1, h2, sq_nonneg (Real.sqrt (msE y + ε)),
      sq_nonneg (Real.sqrt (msE x + ε))]
  have hgp : (0:ℝ) < Real.sqrt (msE y + ε)
      + Real.sqrt (msE x + ε) := by positivity
  have habsd : |Real.sqrt (msE y + ε) - Real.sqrt (msE x + ε)|
      = |msE y - msE x| / (Real.sqrt (msE y + ε)
        + Real.sqrt (msE x + ε)) := by
    rw [eq_comm, div_eq_iff hgp.ne']
    have hA : |Real.sqrt (msE y + ε) - Real.sqrt (msE x + ε)|
        * (Real.sqrt (msE y + ε) + Real.sqrt (msE x + ε))
        = |msE y - msE x| := by
      rw [← abs_of_nonneg hgp.le, ← abs_mul, hsqd]
    exact hA.symm
  rw [ht1, ht2, hgd, habsd]
  have hE1 : (1 / Real.sqrt (msE x + ε)) * ‖x - y‖
      ≤ (1 / Real.sqrt ε) * ‖x - y‖ := by
    have h1 : (1:ℝ) / Real.sqrt (msE x + ε)
        ≤ (1:ℝ) / Real.sqrt ε := by
      rw [div_le_div_iff₀ hgx0 (Real.sqrt_pos.2 hε)]
      simpa using hgx
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hE2 : |msE y - msE x| / (Real.sqrt (msE y + ε)
      + Real.sqrt (msE x + ε))
      / (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε)) * ‖y‖
      ≤ (1 / Real.sqrt ε) * ‖x - y‖ := by
    have hstep2 : Real.sqrt n * |msE y - msE x|
        ≤ ‖y - x‖ * (Real.sqrt (msE y + ε)
          + Real.sqrt (msE x + ε)) := by
      have hxy : ‖y + x‖ ≤ Real.sqrt n * (Real.sqrt (msE y + ε)
          + Real.sqrt (msE x + ε)) := by
        refine le_trans (norm_add_le y x) ?_
        have h3 : ‖y‖ + ‖x‖ ≤ Real.sqrt n * Real.sqrt (msE y + ε)
            + Real.sqrt n * Real.sqrt (msE x + ε) :=
          add_le_add hyle hxle
        have hring : Real.sqrt n * Real.sqrt (msE y + ε)
            + Real.sqrt n * Real.sqrt (msE x + ε)
            = Real.sqrt n * (Real.sqrt (msE y + ε)
              + Real.sqrt (msE x + ε)) := by ring
        rw [← hring]
        exact h3
      by_cases hsn0 : Real.sqrt n = 0
      · rw [hsn0, zero_mul]
        positivity
      · have hsn0' : (0:ℝ) < Real.sqrt n :=
          (lt_or_eq_of_le hnn).resolve_right fun h => hsn0 h.symm
        have hAB : Real.sqrt n * (Real.sqrt n * |msE y - msE x|)
            ≤ Real.sqrt n * (‖y - x‖ * (Real.sqrt (msE y + ε)
              + Real.sqrt (msE x + ε))) := by
          calc Real.sqrt n * (Real.sqrt n * |msE y - msE x|)
              = (Real.sqrt n * Real.sqrt n) * |msE y - msE x| := by ring
            _ = n * |msE y - msE x| := by rw [hsqn]
            _ ≤ ‖y + x‖ * ‖y - x‖ := hsum
            _ ≤ (Real.sqrt n * (Real.sqrt (msE y + ε)
                + Real.sqrt (msE x + ε))) * ‖y - x‖ :=
                mul_le_mul_of_nonneg_right hxy (norm_nonneg _)
            _ = Real.sqrt n * (‖y - x‖ * (Real.sqrt (msE y + ε)
                + Real.sqrt (msE x + ε))) := by ring
        nlinarith [hAB, hsn0']
    have key : ‖y‖ * |msE y - msE x|
        ≤ (‖y - x‖ * (Real.sqrt (msE y + ε)
          + Real.sqrt (msE x + ε))) * Real.sqrt (msE y + ε) := by
      calc ‖y‖ * |msE y - msE x|
          ≤ (Real.sqrt n * Real.sqrt (msE y + ε)) * |msE y - msE x| :=
              mul_le_mul_of_nonneg_right hyle (abs_nonneg _)
        _ = Real.sqrt (msE y + ε) * (Real.sqrt n * |msE y - msE x|) := by
              ring
        _ ≤ Real.sqrt (msE y + ε) * (‖y - x‖ * (Real.sqrt (msE y + ε)
            + Real.sqrt (msE x + ε))) :=
              mul_le_mul_of_nonneg_left hstep2 hgy0.le
        _ = (‖y - x‖ * (Real.sqrt (msE y + ε)
            + Real.sqrt (msE x + ε))) * Real.sqrt (msE y + ε) := by
              ring
    have hform : |msE y - msE x| / (Real.sqrt (msE y + ε)
        + Real.sqrt (msE x + ε))
        / (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε)) * ‖y‖
        = (‖y‖ * |msE y - msE x|)
          / ((Real.sqrt (msE y + ε) + Real.sqrt (msE x + ε))
            * (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε))) := by
      field_simp
    rw [hform]
    have hrhs : (1 / Real.sqrt ε) * ‖x - y‖
        = ‖x - y‖ / Real.sqrt ε := by
      field_simp
    rw [hrhs, div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 hε)]
    have h1 : (‖y‖ * |msE y - msE x|) * Real.sqrt ε
        ≤ (‖y‖ * |msE y - msE x|) * Real.sqrt (msE x + ε) :=
      mul_le_mul_of_nonneg_left hgx
        (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    have h2 : (‖y‖ * |msE y - msE x|) * Real.sqrt (msE x + ε)
        ≤ ‖x - y‖ * ((Real.sqrt (msE y + ε)
          + Real.sqrt (msE x + ε))
          * (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε))) := by
      calc (‖y‖ * |msE y - msE x|) * Real.sqrt (msE x + ε)
          ≤ ((‖y - x‖ * (Real.sqrt (msE y + ε)
            + Real.sqrt (msE x + ε))) * Real.sqrt (msE y + ε))
            * Real.sqrt (msE x + ε) :=
              mul_le_mul_of_nonneg_right key hgx0.le
        _ = ‖x - y‖ * ((Real.sqrt (msE y + ε)
            + Real.sqrt (msE x + ε))
            * (Real.sqrt (msE x + ε) * Real.sqrt (msE y + ε))) := by
              rw [norm_sub_rev]
              ring
    exact le_trans h1 h2
  have hfin : (1 / Real.sqrt ε) * ‖x - y‖
      + (1 / Real.sqrt ε) * ‖x - y‖
      ≤ (2 / Real.sqrt ε) * ‖x - y‖ := by
    have hD : (0:ℝ) ≤ ‖x - y‖ := norm_nonneg _
    have hE : (0:ℝ) ≤ 1 / Real.sqrt ε := by positivity
    have h2 : (2 / Real.sqrt ε) * ‖x - y‖
        = (1 / Real.sqrt ε) * ‖x - y‖
          + (1 / Real.sqrt ε) * ‖x - y‖ := by
      have hsplit2 : (2:ℝ) / Real.sqrt ε
          = (1:ℝ) / Real.sqrt ε + (1:ℝ) / Real.sqrt ε := by
        field_simp
        ring
      rw [hsplit2]
      ring
    linarith
  exact le_trans (add_le_add hE1 hE2) hfin

theorem rnEpsEuc_lipschitz {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨2 / Real.sqrt ε, by positivity⟩ (rnEpsEuc (n := n) ε) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact rnEpsEuc_norm_sub_le hε x y




/-- Sum of a function supported on a two-point set `{a, b}`, `a ≠ b`. -/
private theorem sum_two_point {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (A B : ℝ) :
    ∑ i : Fin n, (if i = a then A else if i = b then B else 0) = A + B := by
  by_cases h : a = b
  · exact absurd h hab
  · rw [← Finset.sum_subset
      (Finset.subset_univ (s := ({a, b} : Finset (Fin n))))
      (fun i _ hi => by
        simp at hi
        rw [if_neg hi.1, if_neg hi.2])]
    have hns : a ∉ ({b} : Finset (Fin n)) := by simp [h]
    rw [Finset.sum_insert hns, Finset.sum_singleton,
      if_pos rfl, if_neg (Ne.symm h), if_pos rfl]

theorem rnEuc_not_lipschitz_with {n : ℕ} (hn : 2 ≤ n) (μ : NNReal) :
    ¬ LipschitzWith μ (rnEuc (n := n)) := by
  intro hlip
  obtain ⟨⟨a, b⟩, hab⟩ : ∃ p : Fin n × Fin n, p.1 ≠ p.2 :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
      intro he
      exact absurd (congrArg Fin.val he) (by simp)⟩
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set d : ℝ := Real.sqrt n / ((μ : ℝ) + 1) with hd
  have hdpos : 0 < d := by positivity
  have hdne : d ≠ 0 := by positivity
  set x : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => if i = a then d else 0) with hx
  set y : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => if i = b then d else 0) with hy
  have hx0 : x ≠ 0 := by
    intro h
    have h0 : (WithLp.ofLp x) a = d := by simp [hx]
    rw [h, WithLp.ofLp_zero] at h0
    simp at h0
    exact hdne h0.symm
  have hy0 : y ≠ 0 := by
    intro h
    have h0 : (WithLp.ofLp y) b = d := by simp [hy]
    rw [h, WithLp.ofLp_zero] at h0
    simp at h0
    exact hdne h0.symm
  have hmsx : msE x = d ^ 2 / n := by
    unfold msE ms
    simp [hx, Finset.sum_ite_eq, sq]
  have hmsy : msE y = d ^ 2 / n := by
    unfold msE ms
    simp [hy, Finset.sum_ite_eq, sq]
  have hsqd : Real.sqrt (d ^ 2 / n) = d / Real.sqrt n := by
    rw [Real.sqrt_div, Real.sqrt_sq hdpos.le]
    positivity
  have hrx : rnEuc x = WithLp.toLp 2
      (fun i => if i = a then Real.sqrt n else 0) := by
    have hmsx' : ms (WithLp.ofLp x) = d ^ 2 / n := hmsx
    ext i
    simp only [rnEuc, WithLp.ofLp_toLp, rnVec]
    by_cases h0 : i = a
    · have hvi : (WithLp.ofLp x) i = d := by
        rw [hx]; simp only [WithLp.ofLp_toLp]; split
        · rfl
        · next hneg => exact absurd h0 hneg
      rw [hvi, h0, hmsx', hsqd]
      field_simp [hdne]
      simp
    · simp [hx, h0, Ne.symm hab]
  have hry : rnEuc y = WithLp.toLp 2
      (fun i => if i = b then Real.sqrt n else 0) := by
    have hmsy' : ms (WithLp.ofLp y) = d ^ 2 / n := hmsy
    ext i
    simp only [rnEuc, WithLp.ofLp_toLp, rnVec]
    by_cases h0 : i = b
    · have hvi : (WithLp.ofLp y) i = d := by
        rw [hy]; simp only [WithLp.ofLp_toLp]; split
        · rfl
        · next hneg => exact absurd h0 hneg
      rw [hvi, h0, hmsy', hsqd]
      field_simp [hdne]
      simp
    · simp [hy, h0, Ne.symm hab]
  have hrxry : rnEuc x - rnEuc y = WithLp.toLp 2
      (fun i => if i = a then Real.sqrt n
        else if i = b then -Real.sqrt n else 0) := by
    ext i
    simp only [hrx, hry, WithLp.ofLp_toLp, WithLp.ofLp_sub,
      Pi.sub_apply, sub_apply]
    by_cases hia : i = a
    · simp [hia, hab]
    · by_cases hib : i = b
      · simp [hia, hib, Ne.symm hab]
      · simp [hia, hib]
  have hnxy : ‖x - y‖ ^ 2 = 2 * d ^ 2 := by
    have hxy : x - y = WithLp.toLp 2
        (fun i => if i = a then d else if i = b then -d else 0) := by
      ext i
      simp only [hx, hy, WithLp.ofLp_toLp, WithLp.ofLp_sub,
        Pi.sub_apply, sub_apply]
      by_cases hia : i = a
      · simp [hia, hab]
      · by_cases hib : i = b
        · simp [hia, hib, Ne.symm hab]
        · simp [hia, hib]
    have hpush : ∀ i : Fin n, (if i = a then d else if i = b then -d else 0) ^ 2
        = if i = a then d ^ 2 else if i = b then (-d) ^ 2 else 0 := by
      intro i
      by_cases h1 : i = a
      · simp [h1]
      · by_cases h2 : i = b
        · simp [h1, h2]
        · simp [h1, h2]
    rw [hxy, EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp,
      Finset.sum_congr rfl (fun i _ => hpush i),
      sum_two_point hab (d ^ 2) ((-d) ^ 2)]
    ring
  have hnrxry : ‖rnEuc x - rnEuc y‖ ^ 2 = 2 * n := by
    have hpush : ∀ i : Fin n, (if i = a then Real.sqrt n
        else if i = b then -Real.sqrt n else 0) ^ 2
        = if i = a then Real.sqrt n ^ 2
          else if i = b then (-(Real.sqrt n)) ^ 2 else 0 := by
      intro i
      by_cases h1 : i = a
      · simp [h1]
      · by_cases h2 : i = b
        · simp [h1, h2]
        · simp [h1, h2]
    rw [hrxry, EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_toLp,
      Finset.sum_congr rfl (fun i _ => hpush i),
      sum_two_point hab (Real.sqrt n ^ 2) ((-(Real.sqrt n)) ^ 2)]
    have hst : (-(Real.sqrt n)) ^ 2 = n := by
      linear_combination Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ n)]
    linarith [hst]
  have hle := LipschitzWith.norm_sub_le hlip x y
  have hN : (0:ℝ) ≤ ‖rnEuc x - rnEuc y‖ := norm_nonneg _
  have hD : (0:ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hB0 : (0:ℝ) ≤ (μ : ℝ) * ‖x - y‖ :=
    mul_nonneg (NNReal.coe_nonneg μ) hD
  have hsqA : ‖rnEuc x - rnEuc y‖ ^ 2 ≤ ((μ : ℝ) * ‖x - y‖) ^ 2 := by
    nlinarith [hle, hN, hB0]
  have hchain : (2:ℝ) * n ≤ (μ : ℝ) ^ 2 * (2 * d ^ 2) := by
    rw [← hnrxry]
    refine hsqA.trans ?_
    rw [mul_pow, hnxy]
  rw [hd, div_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ n)] at hchain
  have hkey : (μ : ℝ) ^ 2 < ((μ : ℝ) + 1) ^ 2 := by
    nlinarith [NNReal.coe_nonneg μ]
  have hc2 : (0:ℝ) < ((μ : ℝ) + 1) ^ 2 := by
    nlinarith [NNReal.coe_nonneg μ]
  field_simp at hchain
  nlinarith [hkey, hnp, hc2]



/-- Pointwise residual leak: if the residual-branch response at the
step `(x, dx)` is bounded by `c·‖dx‖` (no global Lipschitz needed),
the C300 leak bound holds with the composed constant `Lc·c`. -/
theorem residual_transfer_le_pointwise {X : Type*} [NormedAddCommGroup X]
    {f : X → X} {loss : X → ℝ} {Lc : NNReal} {c : ℝ}
    (hc : 0 ≤ c) (x dx : X)
    (hpt : ‖f (x + dx) - f x‖ ≤ c * ‖dx‖)
    (hloss : LipschitzWith Lc loss) :
    loss (resStep f (x + dx))
      ≤ loss (resStep f x + dx) + Lc * c * ‖dx‖ := by
  have hab : resStep f (x + dx) - (resStep f x + dx)
      = f (x + dx) - f x := by
    unfold resStep
    abel
  have h1 := hloss.norm_sub_le (resStep f (x + dx)) (resStep f x + dx)
  rw [hab] at h1
  have h3 : loss (resStep f (x + dx)) - loss (resStep f x + dx)
      ≤ ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖ :=
    le_abs_self _
  have key : ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖
      ≤ Lc * (c * ‖dx‖) := by
    calc ‖loss (resStep f (x + dx)) - loss (resStep f x + dx)‖
        ≤ Lc * ‖f (x + dx) - f x‖ := h1
      _ ≤ Lc * (c * ‖dx‖) :=
          mul_le_mul_of_nonneg_left hpt (NNReal.coe_nonneg Lc)
  linarith

/-- THE C309 RUNG: the C307 attention block theorem with the RMSNorm
premise `μn` DISCHARGED — the pure carrier RMSNorm `rnEuc` enters
with the honest region-bounded constant `μn(r) = 2√n/r` on the
step region `{z | r ≤ ‖z‖}` (both endpoints of the step). The
composed leak constant is `Lc·(μn(r)·μatt)` with
`μn(r) = 2√n/r` explicit. -/
theorem attention_block_transfer_rmsnorm {n : ℕ} {ι : Type*} [Fintype ι]
    {p : ι → ℝ} {v : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {loss : EuclideanSpace ℝ (Fin n) → ℝ} {μatt Lc : NNReal} {r : ℝ}
    (hr : 0 < r) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hv : ∀ i, LipschitzWith μatt (v i))
    (hloss : LipschitzWith Lc loss)
    (x dx : EuclideanSpace ℝ (Fin n))
    (hx : r ≤ ‖x‖) (hxdx : r ≤ ‖x + dx‖) :
    loss (resStep (fun y => attnBranch p v (rnEuc y)) (x + dx))
      ≤ loss (resStep (fun y => attnBranch p v (rnEuc y)) x + dx)
        + Lc * ((2 * Real.sqrt n / r) * (μatt : ℝ)) * ‖dx‖ := by
  have hb := attn_branch_lipschitz hp hp1 hv
  have h1 : ‖attnBranch p v (rnEuc (x + dx)) - attnBranch p v (rnEuc x)‖
      ≤ (μatt : ℝ) * ((2 * Real.sqrt n / r) * ‖x + dx - x‖) := by
    calc ‖attnBranch p v (rnEuc (x + dx)) - attnBranch p v (rnEuc x)‖
        ≤ (μatt : ℝ) * ‖rnEuc (x + dx) - rnEuc x‖ := by
            have hh := hb.norm_sub_le (rnEuc (x + dx)) (rnEuc x)
            simpa [dist_eq_norm] using hh
      _ ≤ (μatt : ℝ) * ((2 * Real.sqrt n / r) * ‖(x + dx) - x‖) :=
            mul_le_mul_of_nonneg_left
              (rn_lipschitz_region hr (x + dx) x hxdx hx)
              (NNReal.coe_nonneg μatt)
  rw [show (x + dx) - x = dx from by abel] at h1
  have h2 : (μatt : ℝ) * ((2 * Real.sqrt n / r) * ‖dx‖)
      = ((2 * Real.sqrt n / r) * (μatt : ℝ)) * ‖dx‖ := by ring
  rw [h2] at h1
  exact residual_transfer_le_pointwise (by positivity) x dx h1 hloss

/-- The ε-floored RMSNorm Lipschitz constant as an explicit NNReal
function of ε: `μn(ε) = 2/√ε`. -/
noncomputable def μnEps (ε : ℝ) (hε : 0 < ε) : NNReal :=
  ⟨2 / Real.sqrt ε, by positivity⟩

/-- The stack instance: the C307 stack descent theorem with the RMSNorm
premise DISCHARGED via the ε-floored variant — every block's pre-norm
is `rnEpsEuc ε` with the explicit global constant `μn(ε) = 2/√ε`
(the pure `rnEuc` admits NO global constant — `rnEuc_not_lipschitz_with`
— so the honest global discharge goes through the ε-floor). -/
theorem attention_stack_transfer_rmsnorm_eps {n : ℕ} {ι : Type*}
    [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (bs : List (AttnBlock (EuclideanSpace ℝ (Fin n)) ι))
    (hnb : ∀ b ∈ bs, b.n = rnEpsEuc ε)
    (hμb : ∀ b ∈ bs, b.μn = μnEps ε hε)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i) (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    {loss : EuclideanSpace ℝ (Fin n) → ℝ} {Lc : NNReal} {δ : ℝ}
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ (Fin n))
    (hdrop : loss (attnStack bs x + dx) ≤ loss (attnStack bs x) - δ) :
    loss (attnStack bs (x + dx)) ≤ loss (attnStack bs x) - δ
      + Lc * ((attnGain bs : ℝ) - 1) * ‖dx‖ := by
  refine attention_stack_transfer_descent bs ?_ hp hp1 hv hloss x dx hdrop
  intro b hb
  rw [hnb b hb, hμb b hb]
  exact rnEpsEuc_lipschitz hε

/-- Strict variant of the ε-discharged stack theorem. -/
theorem attention_stack_transfer_rmsnorm_eps_strict {n : ℕ} {ι : Type*}
    [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (bs : List (AttnBlock (EuclideanSpace ℝ (Fin n)) ι))
    (hnb : ∀ b ∈ bs, b.n = rnEpsEuc ε)
    (hμb : ∀ b ∈ bs, b.μn = μnEps ε hε)
    (hp : ∀ b ∈ bs, ∀ i, 0 ≤ b.p i) (hp1 : ∀ b ∈ bs, ∑ i, b.p i = 1)
    (hv : ∀ b ∈ bs, ∀ i, LipschitzWith b.μatt (b.v i))
    {loss : EuclideanSpace ℝ (Fin n) → ℝ} {Lc : NNReal} {δ : ℝ}
    (hloss : LipschitzWith Lc loss) (x dx : EuclideanSpace ℝ (Fin n))
    (hdrop : loss (attnStack bs x + dx) ≤ loss (attnStack bs x) - δ)
    (hstrict : (Lc : ℝ) * ((attnGain bs : ℝ) - 1) * ‖dx‖ < δ) :
    loss (attnStack bs (x + dx)) < loss (attnStack bs x) := by
  have h := attention_stack_transfer_rmsnorm_eps hε bs hnb hμb hp hp1 hv
    hloss x dx hdrop
  linarith

/-! ### Scalar nonvacuity anchors (4-dimensional) -/

/-- Anchor (n = 4): the region constant of the pure carrier is
`μn(r) = 2√4/r = 4/r`; at `r = 1` it is exactly `4`. -/
example : (2 * Real.sqrt (4 : ℝ) / 1) = 4 := by
  norm_num

/-- Anchor (n = 4, 3-4-5 triangle): `rnEuc` of the vector
`(3, 4, 0, 0)` has norm exactly `2 = √4` — the unit-RMS output of
RMSNorm on the Euclidean carrier. -/
example : ‖rnEuc (n := 4) (WithLp.toLp 2
    (![(3 : ℝ), 4, 0, 0] : Fin 4 → ℝ))‖ = 2 := by
  set w : EuclideanSpace ℝ (Fin 4) :=
    WithLp.toLp 2 (![(3 : ℝ), 4, 0, 0] : Fin 4 → ℝ) with hw
  have hw0 : (WithLp.ofLp w) 0 = 3 := by
    simp [hw, Matrix.cons_val_zero]
  have hvne : w ≠ 0 := by
    intro h
    rw [h] at hw0
    simp only [WithLp.ofLp_zero, Pi.zero_apply] at hw0
    exact absurd hw0 (by norm_num)
  have hn : ‖w‖ = 5 := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp ?_
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsum : ∑ i, ((WithLp.ofLp w) i) ^ 2 = 25 := by
      simp only [hw, WithLp.ofLp_toLp, Fin.sum_univ_four]
      norm_num
    rw [hsum]
    norm_num
  rw [rnEuc_eq hvne, hn]
  have hs4 : Real.sqrt (((4 : ℕ) : ℝ)) = 2 := by norm_num
  rw [hs4]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5), hn]
  norm_num

end Hagi.Model.RMSNormTransfer
