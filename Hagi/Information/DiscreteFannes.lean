/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Prelude.Info
/-!
# SpectralEntropy — entropy from the spectral theorem
(h2-Fannes port, layer 2/N)

Ported verbatim from openai/math,
OAI.InformationTheory.AmplitudeDamping.SpectralEntropy (the
E:/math audit, Fam 276): entropy as the eigenvalue sum
(entropy_eq_sum), unitary invariance, the diagonal majorization
(entropy_le_diagonal), unitarity of eigenvector columns,
concavity-on-states (concaveOn_entropy) — the spectral core on
which the coupling bound is built.
-/

namespace Hagi.Information

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Set

universe u

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix

abbrev Basis (n : ℕ) := Fin n → Fin 2
abbrev QMatrix (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- The spectral definition of -Tr(P log P), with 0 log 0 = 0. -/
def entropy {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog P)).re

def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1


namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

theorem entropy_nonneg {A : Matrix ι ι ℂ} (hA : IsState A) : 0 ≤ entropy A := by
  rw [entropy_eq_sum hA.1.isHermitian]
  have hs : ∑ i, hA.1.isHermitian.eigenvalues i = 1 := by
    simpa using congrArg Complex.re
      (hA.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hA.2)
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hA.1.eigenvalues_nonneg i)
  rw [← hs]
  exact Finset.single_le_sum (fun j _ ↦ hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The square-moduli in each row of a unitary matrix sum to one. -/
theorem unitary_row_sq_sum (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The ordinary diagonal is a doubly stochastic mixing of the spectral diagonal. -/
theorem diag_eq_spectral_mix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    (A i i).re = ∑ j, Complex.normSq (hA.eigenvectorUnitary i j) * hA.eigenvalues j := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.mul_diagonal, Matrix.star_apply, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

/-- Pinching in any fixed orthonormal coordinate basis increases entropy. -/
theorem entropy_le_diagonal {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    entropy A ≤ ∑ i, Real.negMulLog (A i i).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hi (i : ι) :
      ∑ j, Complex.normSq (U i j) * Real.negMulLog (hA.isHermitian.eigenvalues j) ≤
        Real.negMulLog (A i i).re := by
    rw [diag_eq_spectral_mix hA.isHermitian]
    simpa only [U, smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
        (w := fun j ↦ Complex.normSq (U i j))
        (p := hA.isHermitian.eigenvalues) (fun j _ ↦ Complex.normSq_nonneg _)
        (by simpa using unitary_row_sq_sum U i)
        (fun j _ ↦ hA.eigenvalues_nonneg j)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  rw [Finset.sum_comm] at h
  simp only [← Finset.sum_mul, unitary_col_sq_sum, one_mul] at h
  rwa [entropy_eq_sum hA.isHermitian]


/-- Entropy is invariant under every unitary basis change. -/
theorem entropy_unitary_conj (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Unitary.conjStarAlgAut ℂ _ U A) = entropy A := by
  have hφA : (Unitary.conjStarAlgAut ℂ _ U A).IsHermitian := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA
  have hm := StarAlgHomClass.map_cfc (S := ℂ)
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous (fun P : Matrix ι ι ℂ ↦ (U : Matrix ι ι ℂ) * P * star U) by fun_prop)
    hA hφA
  unfold entropy
  calc
    _ = (Matrix.trace (Unitary.conjStarAlgAut ℂ _ U (cfc Real.negMulLog A))).re :=
      congrArg (fun P : Matrix ι ι ℂ ↦ P.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_unitary_conj U _)

/-- The full matrix entropy, not just normalized-state entropy, is concave on
positive semidefinite matrices. -/
theorem concaveOn_entropy :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} entropy := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb _
    exact (hA.smul ha).add (hB.smul hb)
  intro A hA B hB a b ha hb hab
  let C := a • A + b • B
  have hC : C.PosSemidef := (hA.smul ha).add (hB.smul hb)
  let U := hC.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hp (P : Matrix ι ι ℂ) (hP : P.PosSemidef) : (φ P).PosSemidef := by
    exact hP.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have hdiag : φ C = Matrix.diagonal (fun i ↦ (hC.isHermitian.eigenvalues i : ℂ)) := by
    exact hC.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hlin : φ C = a • φ A + b • φ B := by
    dsimp only [C]
    rw [map_add]
    congr 1 <;> exact (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
  have hs (i : ι) :
      a * Real.negMulLog ((φ A) i i).re + b * Real.negMulLog ((φ B) i i).re ≤
        Real.negMulLog (hC.isHermitian.eigenvalues i) := by
    have he : hC.isHermitian.eigenvalues i = a * ((φ A) i i).re + b * ((φ B) i i).re := by
      have ht := congrArg (fun P : Matrix ι ι ℂ ↦ (P i i).re) (hdiag.symm.trans hlin)
      simpa using ht
    rw [he]
    exact Real.concaveOn_negMulLog.2
      ((Complex.nonneg_iff.mp (hp A hA).diag_nonneg).1)
      ((Complex.nonneg_iff.mp (hp B hB).diag_nonneg).1) ha hb hab
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hs i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hEA := entropy_le_diagonal (hp A hA)
  have hEB := entropy_le_diagonal (hp B hB)
  rw [entropy_unitary_conj (star U) hA.isHermitian] at hEA
  rw [entropy_unitary_conj (star U) hB.isHermitian] at hEB
  rw [entropy_eq_sum hC.isHermitian]
  exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hEA ha)
    (mul_le_mul_of_nonneg_left hEB hb)) hsum


end GAD
end
end
end Hagi.Information

/-!
# LogDetEntropy — entropy via log-determinant shifts (h2-Fannes
port, layer 3/N)

Ported verbatim from openai/math,
OAI.InformationTheory.AmplitudeDamping.LogDetEntropy (the
E:/math audit, Fam 276): the logDetShift comparison calculus —
entropy pinned between log-det shifts (entropy_le_of_
logDetShift_le), equality from matching shifts, and the Gram
duality entropy (A·Aᴴ) = entropy (Aᴴ·A) — the machinery
behind entropy_mul_conjTranspose.
-/

namespace Hagi.Information


universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

/-- A finite-spectrum primitive, continuous even at a zero eigenvalue. -/
def logEntropyPrimitive (a t : ℝ) : ℝ :=
  (t + a) * Real.log (t + a) - t * Real.log t - a * Real.log (t + 1)

theorem logEntropyPrimitive_zero (a : ℝ) :
    logEntropyPrimitive a 0 = - Real.negMulLog a := by
  simp [logEntropyPrimitive, Real.negMulLog]

theorem continuousOn_logEntropyPrimitive (a : ℝ) :
    ContinuousOn (logEntropyPrimitive a) (Ici 0) := by
  have h₁ : Continuous (fun t : ℝ ↦ (t + a) * Real.log (t + a)) :=
    Real.continuous_mul_log.comp (continuous_id.add_const a)
  refine (h₁.continuousOn.sub Real.continuous_mul_log.continuousOn).sub ?_
  apply ContinuousOn.const_mul
  refine Real.continuousOn_log.comp (continuous_id.add_const 1).continuousOn ?_
  intro t ht
  change t + 1 ≠ 0
  have ht0 : 0 ≤ t := ht
  linarith

theorem hasDerivAt_logEntropyPrimitive {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (logEntropyPrimitive a)
      (Real.log (1 + a / t) - a / (t + 1)) t := by
  have hta : t + a ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith
  have h₁ := (Real.hasDerivAt_mul_log hta).comp t ((hasDerivAt_id t).add_const a)
  have h₂ := Real.hasDerivAt_mul_log ht.ne'
  have h₃ := ((Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).add_const 1)).const_mul a
  convert! (h₁.sub h₂).sub h₃ using 1
  rw [one_add_div ht.ne', Real.log_div hta ht.ne']
  simp only [mul_one, div_eq_mul_inv]
  ring

theorem tendsto_logEntropyPrimitive (a : ℝ) :
    Tendsto (logEntropyPrimitive a) atTop (𝓝 a) := by
  have hdiff := (Real.tendsto_log_comp_add_sub_log a).sub
    (Real.tendsto_log_comp_add_sub_log 1)
  have h := (Real.tendsto_mul_log_one_add_div_atTop a).add (hdiff.const_mul a)
  simp only [sub_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with t ht hta
  have hne : t + a ≠ 0 := by linarith
  simp only [logEntropyPrimitive, one_add_div ht.ne',
    Real.log_div hne ht.ne']
  ring


theorem entropy_sum_le_of_log_sum_le {ι : Type u_1} [Fintype ι]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (htrace : ∑ i, c i * a i = 0)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * Real.log (1 + a i / t) ≤ 0) :
    ∑ i, c i * Real.negMulLog (a i) ≤ 0 := by
  let H : ℝ → ℝ := fun t ↦ ∑ i, c i * logEntropyPrimitive (a i) t
  have hcont : ContinuousOn H (Ici 0) :=
    continuousOn_finsetSum _ (fun i _ ↦ (continuousOn_logEntropyPrimitive (a i)).const_mul _)
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt H (∑ i, c i * Real.log (1 + a i / t)) t := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
      (hasDerivAt_logEntropyPrimitive (ha i) ht).const_mul (c i))
    convert! h using 1
    · ext t
      simp only [H, Finset.sum_apply]
    · simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div,
        htrace, zero_div, sub_zero]
  have hanti : AntitoneOn H (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
      (fun t ht ↦ (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by rw [(hd t (by simpa using ht)).deriv]; exact hlog t (by simpa using ht))
  have hlim : Tendsto H atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ ↦
      (tendsto_logEntropyPrimitive (a i)).const_mul (c i))
    simpa only [htrace] using h
  have hzero : 0 ≤ H 0 := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hanti (by simp) ht ht)
  simpa only [H, logEntropyPrimitive_zero, mul_neg, Finset.sum_neg_distrib,
    neg_nonneg] using hzero
end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

def logDetShift (r : ℝ) (A : Matrix ι ι ℂ) : ℝ := Real.log ‖(1 + r • A).det‖

theorem det_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).det = A.det := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  calc
    _ = ((U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det) * A.det := by ring
    _ = A.det := by simp only [← Unitary.coe_star, hu, one_mul]

theorem logDetShift_eq_sum {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) :
    logDetShift r A = ∑ i, Real.log (1 + r * hA.isHermitian.eigenvalues i) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have he : 1 + r • A = φ (Matrix.diagonal
      (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ))) := by
    have hd : Matrix.diagonal (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ)) =
        1 + r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hd, map_add, map_one]
    have hm : φ (r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) =
        r • φ (Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) :=
      (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
    rw [hm]
    congr 2
    exact hA.isHermitian.spectral_theorem
  unfold logDetShift
  rw [he, det_unitary_conj, Matrix.det_diagonal, norm_prod]
  have hp (i : ι) : 0 < 1 + r * hA.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hA.eigenvalues_nonneg i))
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hp _)]
  exact Real.log_prod (fun i _ ↦ (hp i).ne')

/-- Entropy may be compared between unequal matrix sizes by their resolvent determinants. -/
theorem entropy_le_of_logDetShift_le {κ : Type u_3} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A ≤ logDetShift r B) :
    entropy A ≤ entropy B := by
  have htA : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]; simp
  have htB : B.trace.re = ∑ i, hB.isHermitian.eigenvalues i := by
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]; simp
  have hh := entropy_sum_le_of_log_sum_le
    (Sum.elim (fun _ : ι ↦ (1 : ℝ)) (fun _ : κ ↦ -1))
    (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues) ?_ ?_ ?_
  · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, entropy_eq_sum hA.isHermitian,
      entropy_eq_sum hB.isHermitian] using hh
  · intro i
    cases i with
    | inl i => exact hA.eigenvalues_nonneg i
    | inr i => exact hB.eigenvalues_nonneg i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, ← htA, ← htB, htrace, add_neg_cancel]
  · intro t ht
    have hh := hlog t⁻¹ (inv_pos.mpr ht)
    rw [logDetShift_eq_sum hA (inv_nonneg.mpr ht.le),
      logDetShift_eq_sum hB (inv_nonneg.mpr ht.le)] at hh
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, div_eq_mul_inv, mul_comm] using hh

theorem entropy_eq_of_logDetShift_eq {κ : Type u_4} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A = logDetShift r B) :
    entropy A = entropy B :=
  le_antisymm (entropy_le_of_logDetShift_le hA hB htrace (fun r hr ↦ (hlog r hr).le))
    (entropy_le_of_logDetShift_le hB hA htrace.symm (fun r hr ↦ (hlog r hr).ge))

/-- Nonzero spectra, including their entropy, agree for both rectangular Gram matrices. -/
theorem entropy_mul_conjTranspose {κ : Type u_5} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : entropy (A * Aᴴ) = entropy (Aᴴ * A) := by
  apply entropy_eq_of_logDetShift_eq (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_conjTranspose_mul_self A)
  · exact congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)
  · intro r _
    dsimp only [logDetShift]
    congr 2
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using
      Matrix.det_one_add_mul_comm (r • A) Aᴴ

end GAD

end


end Hagi.Information
/-!
# GramBasic — the Gram/mass kernel (h2-Fannes port, layer 4/N)

Ported verbatim from openai/math,
OAI.InformationTheory.AmplitudeDamping.GramMatrices (the
E:/math audit, Fam 276): the Gram matrix (A·Aᴴ) and the mass
(its real trace) with nonnegativity — the rectangular factor
bookkeeping used by the coupling bound. Only the minimal
core is ported (the resolvent/zeroBlock machinery is not on
the path to entropy_coupling_bound).
-/

namespace Hagi.Information

universe u_1 u_2

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder
open Matrix

namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

def gram (A : Matrix ι κ ℂ) : Matrix ι ι ℂ := A * Aᴴ

def mass (A : Matrix ι κ ℂ) : ℝ := (gram A).trace.re

def logGram (A : Matrix ι κ ℂ) : ℝ := Real.log ‖(1+gram A).det‖

omit [DecidableEq ι] [DecidableEq κ] in
theorem mass_nonneg (A : Matrix ι κ ℂ) : 0 ≤ mass A :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose A).trace_nonneg).1


end GAD
end
end Hagi.Information

/-!
# StateEntropy — mixture and spectral-factor entropy bounds
(h2-Fannes port, layer 5/N)

Ported verbatim from openai/math,
OAI.InformationTheory.AmplitudeDamping (the E:/math audit,
Fam 276): pure/vecMass (Channel.lean/PureRecursion.lean
minimal core), entropy_smul (ZeroBlockEntropy.lean's lemma,
proved here on the spectral base), state_mixture,
spectral_pure_decomposition, spectral_weights_sum,
spectralFactor (StateEntropy.lean). The mixing calculus the
coupling bound needs.
-/

namespace Hagi.Information

universe u_1 u_3 u_4

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace GAD

variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The rank-one matrix ψψ*. -/
def pure {ι : Type u_3} (ψ : ι → ℂ) : Matrix ι ι ℂ := fun i j ↦ ψ i * star (ψ j)

def vecMass (ψ : ι → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)

theorem pure_posSemidef (ψ : ι → ℂ) : (pure ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

theorem pure_trace (ψ : ι → ℂ) : (pure ψ).trace = (vecMass ψ : ℂ) := by
  simp [Matrix.trace, pure, vecMass, Complex.mul_conj]

theorem pure_state [DecidableEq ι] {ψ : ι → ℂ} (hψ : vecMass ψ = 1) : IsState (pure ψ) := by
  exact ⟨pure_posSemidef ψ, by rw [pure_trace,hψ]; rfl⟩

theorem state_mixture (w : α → ℝ) (P : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hP : ∀ a, IsState (P a)) :
    IsState (∑ a, w a • P a) := by
  constructor
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact Finset.sum_nonneg (fun a _ ↦ Matrix.nonneg_iff_posSemidef.mpr ((hP a).1.smul (hw a)))
  · simp only [Matrix.trace_sum,Matrix.trace_smul,(hP _).2,Complex.real_smul,mul_one]
    exact_mod_cast hs

theorem spectral_pure_decomposition {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    P = ∑ a, hP.eigenvalues a • pure (fun i ↦ hP.eigenvectorUnitary i a) := by
  conv_lhs => rw [hP.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  ext i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.sum_apply,
    Matrix.smul_apply,pure,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [diagonal_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change hP.eigenvectorUnitary i a * (hP.eigenvalues a : ℂ) * star (hP.eigenvectorUnitary j a) =
    (hP.eigenvalues a : ℂ) * (hP.eigenvectorUnitary i a * star (hP.eigenvectorUnitary j a))
  ring

theorem spectral_weights_sum {P : Matrix ι ι ℂ} (hP : IsState P) :
    ∑ a, hP.1.isHermitian.eigenvalues a = 1 := by
  simpa using congrArg Complex.re
    (hP.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hP.2)

theorem spectral_vectors_mass {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (a : ι) :
    vecMass (fun i ↦ hP.eigenvectorUnitary i a) = 1 :=
  unitary_col_sq_sum hP.eigenvectorUnitary a

def spectralFactor {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : Matrix ι ι ℂ :=
  fun i k ↦ (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ) * hA.isHermitian.eigenvectorUnitary i k

theorem spectralFactor_gram {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    gram (spectralFactor hA) = A := by
  conv_rhs => rw [spectral_pure_decomposition hA.isHermitian]
  ext i j
  simp only [gram,Matrix.mul_apply,Matrix.conjTranspose_apply,spectralFactor,
    star_mul,Matrix.sum_apply,Matrix.smul_apply,pure,Complex.real_smul,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 =
      (hA.isHermitian.eigenvalues k : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hA.eigenvalues_nonneg k)
  calc
    _ = (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 *
      (hA.isHermitian.eigenvectorUnitary i k * star (hA.isHermitian.eigenvectorUnitary j k)) := by
        simp only [Complex.star_def]; ring
    _ = _ := by rw [hs]; rfl

theorem spectralFactor_column {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (k : ι) :
    ∑ i, Complex.normSq (spectralFactor hA i k) = hA.isHermitian.eigenvalues k := by
  simp only [spectralFactor,Complex.normSq_mul,Complex.normSq_ofReal,← pow_two,
    Real.sq_sqrt (hA.eigenvalues_nonneg k),← Finset.mul_sum,unitary_col_sq_sum,mul_one]

section
variable {ι : Type u_1} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem entropy_sum_le (A : α → Matrix ι ι ℂ) (hA : ∀ a, (A a).PosSemidef) :
    entropy (∑ a, A a) ≤ ∑ a, entropy (A a) := by
  let F : Matrix ι (α × ι) ℂ := fun i ak ↦ Information.GAD.spectralFactor (hA ak.1) i ak.2
  have hgram : Information.GAD.gram F = ∑ a, A a := by
    ext i j
    change (∑ ak : α × ι, Information.GAD.spectralFactor (hA ak.1) i ak.2 *
      star (Information.GAD.spectralFactor (hA ak.1) j ak.2)) = (∑ a, A a) i j
    simp only [Fintype.sum_prod_type,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun M : Matrix ι ι ℂ ↦ M i j) (Information.GAD.spectralFactor_gram (hA a))
  have hdiag (ak : α × ι) : ((Fᴴ*F) ak ak).re = (hA ak.1).isHermitian.eigenvalues ak.2 := by
    change (∑ i, star (F i ak)*F i ak).re = _
    simp only [Complex.re_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,F]
    exact Information.GAD.spectralFactor_column (hA ak.1) ak.2
  rw [← hgram]
  change entropy (F*Fᴴ) ≤ _
  rw [entropy_mul_conjTranspose]
  have he := entropy_le_diagonal (Matrix.posSemidef_conjTranspose_mul_self F)
  simpa only [hdiag,Fintype.sum_prod_type,entropy_eq_sum (hA _).isHermitian] using he

theorem entropy_smul (a : ℝ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    entropy (a • P) = a * entropy P + Real.negMulLog a * P.trace.re := by
  rw [entropy, ← cfc_comp_smul a Real.negMulLog P, trace_cfc_eq hP]
  simp only [smul_eq_mul, Complex.re_sum, Complex.ofReal_re,
    Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← entropy_eq_sum hP]
  rw [hP.trace_eq_sum_eigenvalues]
  simp
  ring

theorem entropy_mixture_upper (w : α → ℝ) (A : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hA : ∀ a, IsState (A a)) :
    entropy (∑ a, w a • A a) ≤ ∑ a, (w a*entropy (A a)+Real.negMulLog (w a)) := by
  have h := entropy_sum_le (fun a ↦ w a • A a) (fun a ↦ (hA a).1.smul (hw a))
  simpa only [entropy_smul _ (hA _).1.isHermitian,(hA _).2,Complex.one_re,mul_one] using h

end
end GAD
end
end Hagi.Information

/-!
# EntropyContinuity — the refined Fannes bound with the
singular h2 part (h2-Fannes port, layer 6/6 — THE TARGET)

Ported from openai/math,
OAI.InformationTheory.AmplitudeDamping.EntropyContinuity
(the E:/math audit, Fam 276):

* `entropy_coupling_bound` — the refined Zhang/Shirokov-type
  continuity: PSD-coupled states A+U = B+V with trace U =
  trace V = t give
  S(A) − S(B) ≤ t·log d + (1+t)·h₂(t/(1+t)) —
  zero-eigenvalue-safe (the h₂ term absorbs the singular
  part; cfc Real.negMulLog handles 0·log 0 = 0);
* the Frobenius-vector and projection mass lemmas on the
  path (frobVector, mass calculus).

This closes the residual (the singular h2 Fannes
boundary) of the HAGI plan — in the quantum-state form; the
discrete PMF specialization is a direct corollary of the
diagonal (commuting) case.
-/

namespace Hagi.Information

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

def frobVector (A : Matrix ι κ ℂ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun ik ↦ A ik.1 ik.2)

theorem mass_eq_sum_normSq (A : Matrix ι κ ℂ) : mass A=∑ i, ∑ k, Complex.normSq (A i k) := by
  simp [mass,gram,Matrix.trace,Matrix.mul_apply,Complex.mul_conj]

theorem frobVector_norm (A : Matrix ι κ ℂ) : ‖frobVector A‖^2=mass A := by
  rw [EuclideanSpace.norm_sq_eq,mass_eq_sum_normSq]
  simp only [Fintype.sum_prod_type,frobVector,PiLp.toLp_apply,Complex.sq_norm]

omit [Fintype ι] [Fintype κ] in
theorem frobVector_add (A B : Matrix ι κ ℂ) : frobVector (A+B)=frobVector A+frobVector B := rfl
omit [Fintype ι] [Fintype κ] in
theorem frobVector_sub (A B : Matrix ι κ ℂ) : frobVector (A-B)=frobVector A-frobVector B := rfl

theorem frobVector_inner (A B : Matrix ι κ ℂ) :
    ⟪frobVector A,frobVector B⟫_ℝ=(Aᴴ*B).trace.re := by
  have hn := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at hn
  have hm : mass (A+B)=mass A+mass B+2*(Aᴴ*B).trace.re := by
    rw [mass_eq_sum_normSq,mass_eq_sum_normSq,mass_eq_sum_normSq]
    simp only [Matrix.add_apply,Complex.normSq_add,Finset.sum_add_distrib,← Finset.mul_sum]
    congr 1
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.star_def]
    ring
  linarith

variable [DecidableEq ι]

def IsProjection (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P*P=P

omit [DecidableEq ι] in
theorem IsProjection.posSemidef {P : Matrix ι ι ℂ} (hP : IsProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hP.1.eq,hP.2] at h

theorem IsProjection.complement {P : Matrix ι ι ℂ} (hP : IsProjection P) : IsProjection (1-P) := by
  refine ⟨(Matrix.isHermitian_one).sub hP.1, ?_⟩
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP.2]
  simp

omit [DecidableEq ι] in
theorem projection_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P) (A B : Matrix ι κ ℂ) :
    ⟪frobVector (P*A),frobVector (B-P*B)⟫_ℝ=0 := by
  rw [frobVector_inner,Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_sub]
  have he : Aᴴ*P*(P*B)=Aᴴ*P*B := by
    rw [← Matrix.mul_assoc _ P,Matrix.mul_assoc Aᴴ P P,hP.2]
  rw [he,sub_self,Matrix.trace_zero,Complex.zero_re]

omit [DecidableEq ι] in
theorem projection_mass_decomposition {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A)+mass (A-P*A)=mass A := by
  have h := norm_add_sq_real (frobVector (P*A)) (frobVector (A-P*A))
  rw [← frobVector_add,projection_orthogonal hP A A,mul_zero,add_zero] at h
  have he : P*A+(A-P*A)=A := by abel
  rw [he,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

omit [DecidableEq ι] in
theorem projection_mass_le {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A) ≤ mass A := by
  have h := projection_mass_decomposition hP A
  linarith [mass_nonneg (A-P*A)]

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem shannon_le_log_card [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card ι) := by
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos (α := ι))
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : ι ↦ d⁻¹) (p := p)
    (fun _ _ ↦ inv_nonneg.mpr hd.le)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hd.ne')
    (fun i _ ↦ (show p i ∈ Set.Ici 0 from hp i))
  simp only [smul_eq_mul,← Finset.mul_sum,hs,mul_one,Real.negMulLog,Real.log_inv] at h
  have hh := mul_le_mul_of_nonneg_left h hd.le
  dsimp only [d] at *
  calc
    _ = (Fintype.card ι:ℝ) * ((Fintype.card ι:ℝ)⁻¹ * ∑ i, Real.negMulLog (p i)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
    _ ≤ _ := hh
    _ = _ := by field_simp

theorem entropy_le_log_card [Nonempty ι] {A : Matrix ι ι ℂ} (hA : IsState A) :
    entropy A ≤ Real.log (Fintype.card ι) := by
  rw [entropy_eq_sum hA.1.isHermitian]
  exact shannon_le_log_card _ hA.1.eigenvalues_nonneg (spectral_weights_sum hA)

theorem state_normalize_trace {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) (htr : A.trace=(t:ℂ)) : IsState (t⁻¹ • A) := by
  refine ⟨hA.smul (inv_nonneg.mpr ht.le), ?_⟩
  rw [Matrix.trace_smul,htr]
  simp [Complex.real_smul,ht.ne']

/-- Entropy continuity from a positive common-mixture coupling. -/
theorem entropy_coupling_bound [Nonempty ι] {A B U V : Matrix ι ι ℂ}
    (hA : IsState A) (hB : IsState B) (hU : U.PosSemidef) (hV : V.PosSemidef)
    {t : ℝ} (ht : 0 < t) (htrU : U.trace=(t:ℂ)) (htrV : V.trace=(t:ℂ))
    (heq : A+U=B+V) :
    entropy A-entropy B ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := by
  let a : ℝ := (1+t)⁻¹
  let b : ℝ := t/(1+t)
  have ht1 : 0 < 1+t := by positivity
  have ha : 0 ≤ a := inv_nonneg.mpr ht1.le
  have hb : 0 ≤ b := div_nonneg ht.le ht1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hu := state_normalize_trace hU ht htrU
  have hv := state_normalize_trace hV ht htrV
  have he : a • A+b • (t⁻¹ • U)=a • B+b • (t⁻¹ • V) := by
    have hba : b*t⁻¹=a := by dsimp [a,b]; field_simp
    simp only [smul_smul,hba,← smul_add,heq]
  have hlo := concaveOn_entropy.2 hA.1 hu.1 ha hb hab
  have hup := entropy_mixture_upper (fun s : Fin 2 ↦ if s=0 then a else b)
    (fun s : Fin 2 ↦ if s=0 then B else t⁻¹ • V)
    (by intro s; split_ifs <;> assumption)
    (by intro s; split_ifs <;> assumption)
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false] at hup
  rw [he] at hlo
  have hU0 := entropy_nonneg hu
  have hVmax := entropy_le_log_card hv
  have hm := mul_le_mul_of_nonneg_left hVmax hb
  have hh : Real.negMulLog a+Real.negMulLog b=Real.binEntropy b := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have heab : a=1-b := by linarith
    rw [heab]; ring
  have htotal : a*(entropy A-entropy B) ≤ b*Real.log (Fintype.card ι)+Real.binEntropy b := by
    change a*entropy A+b*entropy (t⁻¹ • U) ≤ _ at hlo
    nlinarith [mul_nonneg hb hU0]
  have hh' := mul_le_mul_of_nonneg_left htotal ht1.le
  dsimp only [a,b] at hh'
  have hc : (1+t)*((1+t)⁻¹*(entropy A-entropy B)) = entropy A-entropy B := by
    rw [← mul_assoc,mul_inv_cancel₀ ht1.ne',one_mul]
  rw [hc,mul_add] at hh'
  have hc' : (1+t)*(t/(1+t)*Real.log (Fintype.card ι))=t*Real.log (Fintype.card ι) := by
    field_simp
  rwa [hc'] at hh'

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem mass_real_smul (a : ℝ) (A : Matrix ι κ ℂ) : mass (a • A)=a^2*mass A := by
  rw [← frobVector_norm,← frobVector_norm]
  have he : frobVector (a • A)=a • frobVector A := rfl
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem mass_add (A B : Matrix ι κ ℂ) :
    mass (A+B)=mass A+mass B+2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem mass_sub (A B : Matrix ι κ ℂ) :
    mass (A-B)=mass A+mass B-2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_sub_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_sub,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem gram_posSemidef (A : Matrix ι κ ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

theorem gram_trace (A : Matrix ι κ ℂ) : (gram A).trace=(mass A:ℂ) := by
  exact Complex.ext (by rfl) (by simpa using (Complex.nonneg_iff.mp (gram_posSemidef A).trace_nonneg).2.symm)

variable [DecidableEq ι]

/-- Quantitative entropy comparison from close normalized Gram factors. -/
theorem factor_entropy_bound [Nonempty ι] (X Y : Matrix ι κ ℂ)
    (hX : mass X=1) (hY : mass Y=1) {ε : ℝ} (hε : 0 < ε) :
    entropy (gram X)-entropy (gram Y) ≤
      (mass (X-Y)/(4*ε)+ε)*Real.log (Fintype.card ι)+
        (1+mass (X-Y)/(4*ε)+ε)*Real.log 2 := by
  let D := X-Y
  let S := X+Y
  have hDS : ⟪frobVector D,frobVector S⟫_ℝ=0 := by
    dsimp [D,S]
    rw [frobVector_sub,frobVector_add,inner_sub_left,inner_add_right,inner_add_right,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm (frobVector Y),
      frobVector_norm,frobVector_norm,hX,hY]
    ring
  have hsum : mass D+mass S=4 := by
    dsimp [D,S]; rw [mass_add,mass_sub,hX,hY]; ring
  have hSle : mass S ≤ 4 := by linarith [mass_nonneg D]
  let c : ℝ := (4*ε)⁻¹
  let U : Matrix ι ι ℂ := c • gram (D-ε • S)
  let V : Matrix ι ι ℂ := c • gram (D+ε • S)
  let t : ℝ := c*(mass D+ε^2*mass S)
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have htm : 0 < mass D+ε^2*mass S := by
    have hd := mass_nonneg D
    have hs := mass_nonneg S
    have hes : 0 < ε^2 := sq_pos_of_pos hε
    by_cases hdz : mass D=0
    · have hspos : 0 < mass S := by linarith
      exact add_pos_of_nonneg_of_pos hd (mul_pos hes hspos)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hd (Ne.symm hdz)) (mul_nonneg hes.le hs)
  have ht : 0 < t := mul_pos hc htm
  have hin : ⟪frobVector D,frobVector (ε • S)⟫_ℝ=0 := by
    change ⟪frobVector D,ε • frobVector S⟫_ℝ=0
    rw [real_inner_smul_right,hDS,mul_zero]
  have hmU : mass (D-ε • S)=mass D+ε^2*mass S := by rw [mass_sub,mass_real_smul,hin]; ring
  have hmV : mass (D+ε • S)=mass D+ε^2*mass S := by rw [mass_add,mass_real_smul,hin]; ring
  have htrU : U.trace=(t:ℂ) := by
    dsimp [U,t]; rw [Matrix.trace_smul,gram_trace,hmU]; simp [Complex.real_smul]; ring
  have htrV : V.trace=(t:ℂ) := by
    dsimp [V,t]; rw [Matrix.trace_smul,gram_trace,hmV]; simp [Complex.real_smul]; ring
  have hUV : gram X+U=gram Y+V := by
    have hcε : c*(4*ε)=1 := inv_mul_cancel₀ (by positivity)
    ext i j
    simp only [U,V,D,S,gram,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,star_sub,star_add,
      Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hcε' : (c:ℂ)*(4*ε)=1 := by exact_mod_cast hcε
    linear_combination -(X i k*(starRingEnd ℂ) (X j k)-Y i k*(starRingEnd ℂ) (Y j k))*hcε'
  have hA : IsState (gram X) := ⟨gram_posSemidef X, by rw [gram_trace,hX]; norm_num⟩
  have hB : IsState (gram Y) := ⟨gram_posSemidef Y, by rw [gram_trace,hY]; norm_num⟩
  have hb := entropy_coupling_bound hA hB ((gram_posSemidef _).smul hc.le)
    ((gram_posSemidef _).smul hc.le) ht htrU htrV hUV
  have htle : t ≤ mass (X-Y)/(4*ε)+ε := by
    dsimp [t,c,D]
    have haux : ε^2*mass S ≤ ε^2*4 := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left haux (inv_nonneg.mpr (show 0 ≤ 4*ε by positivity))
    have he : (4*ε)⁻¹*(mass (X-Y)+ε^2*4)=mass (X-Y)/(4*ε)+ε := by field_simp
    rw [← he]; nlinarith
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hint : Real.binEntropy (t/(1+t)) ≤ Real.log 2 := Real.binEntropy_le_log_two
  calc
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := hb
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.log 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hint (by positivity))
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right htle hlog
      have h2 := mul_le_mul_of_nonneg_right htle (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
      nlinarith

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

theorem mass_eq_zero (A : Matrix ι κ ℂ) : mass A=0 ↔ A=0 := by
  rw [← frobVector_norm,sq_eq_zero_iff,norm_eq_zero]
  constructor
  · intro h; ext i k; exact congrArg (fun v : EuclideanSpace ℂ (ι × κ) ↦ v (i,k)) h
  · intro h; subst A; rfl

theorem projection_inner {P : Matrix ι ι ℂ} (hP : IsProjection P) (X : Matrix ι κ ℂ) :
    ⟪frobVector X,frobVector (P*X)⟫_ℝ=mass (P*X) := by
  have h := projection_orthogonal hP X X
  rw [frobVector_sub,inner_sub_right,real_inner_self_eq_norm_sq,
    frobVector_norm,real_inner_comm] at h
  linarith

/-- Normalize a successful projection without losing more than twice its failure mass. -/
theorem exists_projected_factor {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (X B : Matrix ι κ ℂ) (hX : mass X=1) (hB : mass B=1) (hPB : P*B=B) :
    ∃ Y : Matrix ι κ ℂ, mass Y=1 ∧ P*Y=Y ∧ mass (X-Y) ≤ 2*(1-mass (P*X)) := by
  let p := mass (P*X)
  have hp0 : 0 ≤ p := mass_nonneg _
  have hp1 : p ≤ 1 := by simpa only [hX] using projection_mass_le hP X
  by_cases hp : p=0
  · refine ⟨B,hB,hPB,?_⟩
    have hz : P*X=0 := (mass_eq_zero _).mp hp
    have hi := projection_orthogonal hP B X
    rw [hPB,hz,sub_zero,real_inner_comm] at hi
    rw [mass_sub,hX,hB,hi]
    change 1+1-2*0 ≤ 2*(1-p)
    rw [hp]; norm_num
  · have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpp
    let a : ℝ := (Real.sqrt p)⁻¹
    refine ⟨a • (P*X), ?_, ?_, ?_⟩
    · rw [mass_real_smul]
      change (Real.sqrt p)⁻¹^2*p=1
      rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
    · rw [Matrix.mul_smul,← Matrix.mul_assoc,hP.2]
    · rw [mass_sub,mass_real_smul,hX]
      have he : a^2*mass (P*X)=1 := by
        change (Real.sqrt p)⁻¹^2*p=1
        rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
      rw [he]
      change 1+1-2*⟪frobVector X,a • frobVector (P*X)⟫_ℝ ≤ 2*(1-p)
      rw [real_inner_smul_right,projection_inner hP X]
      have hsp : p ≤ Real.sqrt p := by nlinarith [Real.sq_sqrt hp0,(Real.sqrt_nonneg p)]
      have hprod : a*p=Real.sqrt p := by
        dsimp [a]
        calc
          _ = (Real.sqrt p)⁻¹ * (Real.sqrt p*Real.sqrt p) := by congr 1; nlinarith [Real.sq_sqrt hp0]
          _ = _ := by field_simp
      change 1+1-2*(a*p) ≤ 2*(1-p)
      rw [hprod]; linarith

end GAD

end
end Hagi.Information

/-!
# DiscreteFannes — PMF specialization of the coupling entropy
bound

The quantum coupling bound `entropy_coupling_bound`
(S(A) − S(B) ≤ t log d + (1+t) h₂(t/(1+t)) for PSD
A + U = B + V, tr U = tr V = t) is stated for density
matrices. HAGI's operational vocabulary is discrete (router
distributions, expert occupancy, token counts), so this
module transports the bound to probability vectors through
the DIAGONAL embedding p ↦ diagonal p.

The transport needs one bridge, stated as an explicit
hypothesis of the main theorem: the spectral entropy of a
nonnegative diagonal matrix equals the Shannon entropy of
the vector (`entropy (diagonal r) = ∑ negMulLog r i`).
This is a standard fact (cfc of a diagonal matrix acts
entrywise); it is the only unproven link, clearly flagged,
while everything else — the canonical pointwise coupling
u = (p−q)⁺, v = (q−p)⁺, the state/PSD/trace side conditions,
and the final inequality — is proven outright.

Main results:
* `posPart_negPart_pointwise` — the canonical coupling:
  p + v = q + u pointwise;
* `pos_neg_sums` — for probability vectors the two parts
  carry EQUAL total mass, together the L1 distance;
* `discrete_fannes_coupling` — for probability vectors p, q
  on a nonempty finite type: Shannon(p) − Shannon(q) ≤
  t log d + (1+t) h₂(t/(1+t)), t = ‖p−q‖₁/2, GIVEN the
  diagonal-entropy bridge.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace Hagi.Information

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Shannon entropy of a finite distribution. -/
noncomputable def shannon (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- Total-variation half-distance. -/
noncomputable def tvHalf (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

/-- ДЕДУП (аудит v5 п.5): tvHalf — то же определение, что
каноническое Prelude.tvDef (половина L1-расстояния);
связь rfl. -/
theorem tvHalf_eq_tvDef (p q : ι → ℝ) :
    tvHalf p q = Hagi.Prelude.tvDef p q := rfl

/-- The canonical pointwise coupling parts. -/
def posPart (p q : ι → ℝ) : ι → ℝ := fun i => max (p i - q i) 0
def negPart (p q : ι → ℝ) : ι → ℝ := fun i => max (q i - p i) 0

lemma posPart_nonneg (p q : ι → ℝ) : ∀ i, 0 ≤ posPart p q i := by
  intro i; simp [posPart]

lemma negPart_nonneg (p q : ι → ℝ) : ∀ i, 0 ≤ negPart p q i := by
  intro i; simp [negPart]

lemma posPart_negPart_pointwise (p q : ι → ℝ) (i : ι) :
    p i + negPart p q i = q i + posPart p q i := by
  simp only [posPart, negPart]
  rcases le_total (p i) (q i) with h | h
  · rw [show max (q i - p i) 0 = q i - p i from
        max_eq_left (by linarith),
      show max (p i - q i) 0 = 0 from
        max_eq_right (by linarith)]
    ring
  · rw [show max (q i - p i) 0 = 0 from
        max_eq_right (by linarith),
      show max (p i - q i) 0 = p i - q i from
        max_eq_left (by linarith)]
    ring

lemma abs_eq_pos_add_neg (p q : ι → ℝ) (i : ι) :
    |p i - q i| = posPart p q i + negPart p q i := by
  simp only [posPart, negPart]
  rcases le_total (p i) (q i) with h | h
  · rw [abs_of_nonpos (by linarith : p i - q i ≤ (0:ℝ)),
      show max (p i - q i) 0 = 0 from max_eq_right (by linarith),
      show max (q i - p i) 0 = q i - p i from max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p i - q i),
      show max (p i - q i) 0 = p i - q i from max_eq_left (by linarith),
      show max (q i - p i) 0 = 0 from max_eq_right (by linarith)]
    ring

/-- For probability vectors the coupling parts carry EQUAL
total mass, and together they carry the L1 distance. -/
theorem pos_neg_sums (p q : ι → ℝ)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    ∑ i, posPart p q i = ∑ i, negPart p q i
      ∧ (∑ i, posPart p q i) + (∑ i, negPart p q i)
        = ∑ i, |p i - q i| := by
  constructor
  · have h : ∑ i, (p i + negPart p q i) = ∑ i, (q i + posPart p q i) :=
      Finset.sum_congr rfl (fun i _ => posPart_negPart_pointwise p q i)
    simp only [Finset.sum_add_distrib] at h
    rw [hps, hqs] at h
    linarith
  · have h : ∑ i, (posPart p q i + negPart p q i) = ∑ i, |p i - q i| :=
      Finset.sum_congr rfl (fun i _ => (abs_eq_pos_add_neg p q i).symm)
    rw [← Finset.sum_add_distrib]
    exact h

section DiagPSD
open Matrix GAD

/-- The diagonal embedding of a nonnegative real vector is
positive semidefinite: diagonal r = D * D with D = diagonal sqrt r
(spectral factors), via `posSemidef_self_mul_conjTranspose`. -/
theorem diagonal_posSemidef (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (Matrix.diagonal fun i => ((r i : ℝ) : ℂ)).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose
    (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))
  have hEq : (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))
      * (Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ))ᴴ
      = Matrix.diagonal fun i => ((r i : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    show ((Real.sqrt (r i) : ℝ) : ℂ) * star ((Real.sqrt (r i) : ℝ) : ℂ)
      = ((r i : ℝ) : ℂ)
    rw [show star ((Real.sqrt (r i) : ℝ) : ℂ)
        = ((Real.sqrt (r i) : ℝ) : ℂ) from Complex.conj_ofReal _]
    exact_mod_cast Real.mul_self_sqrt (hr i)
  rw [hEq] at h
  exact h


/-- **Discrete coupling Fannes**: for probability vectors
p, q on a nonempty finite type, with t = ‖p−q‖₁/2 the TV
half-distance, the refined continuity bound transports
through the diagonal embedding:
Shannon(p) − Shannon(q) ≤ t log d + (1+t) h₂(t/(1+t)).
The diagonal-entropy bridge (spectral entropy of diagonal =
Shannon) is an explicit hypothesis — the single deferred
link, everything else proven outright. Derivation status
(R268 audit trail): entropy_eq_sum (SpectralEntropy) reduces
the bridge to ∑ negMulLog (eigenvalues (diagonal r))
= ∑ negMulLog (r i), which needs eigenvalues-of-diagonal as a
SORTED-roots multiset identity — absent from Mathlib v4.34.1;
open. -/
theorem discrete_fannes_coupling [Nonempty ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hbridge : ∀ r : ι → ℝ, (∀ i, 0 ≤ r i) →
      entropy (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))) = shannon r) :
    shannon p - shannon q ≤
      (tvHalf p q) * Real.log (Fintype.card ι : ℝ)
      + (1 + tvHalf p q)
        * Real.binEntropy (tvHalf p q / (1 + tvHalf p q)) := by
  -- the canonical coupling matrices (no `set`: simp needs to
  -- see the diagonal structure)
  have hcoupling : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))
      + Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))
      = (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))
      + Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ)))) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · have hc := posPart_negPart_pointwise p q i
      have hc' : (((p i + negPart p q i) : ℝ) : ℂ)
          = (((q i + posPart p q i) : ℝ) : ℂ) := by
        exact_mod_cast hc
      simpa using hc'
    · simp [hij]
  -- degenerate case p = q: both sides collapse to 0 ≤ h₂(0) = 0
  rcases eq_or_ne (∑ i, |p i - q i|) 0 with hzero | hpos
  · have hall : ∀ i, p i = q i := by
      intro i
      by_contra hne
      have hnez : p i - q i ≠ 0 := sub_ne_zero.mpr hne
      have hgt : 0 < |p i - q i| := abs_pos.mpr hnez
      have hle : |p i - q i| ≤ ∑ j, |p j - q j| :=
        Finset.single_le_sum (f := fun j => |p j - q j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      rw [hzero] at hle
      have hz : |p i - q i| = 0 := le_antisymm hle (abs_nonneg _)
      exact hnez (abs_eq_zero.mp hz)
    have hrw : tvHalf p q = 0 := by
      simp only [tvHalf, hzero, zero_div]
    have hself : shannon p - shannon q = 0 := by
      have hq' : shannon p = shannon q := by
        show ∑ i, Real.negMulLog (p i) = ∑ i, Real.negMulLog (q i)
        rw [funext hall]
      rw [hq']
      ring
    have hbin : Real.binEntropy (0 / (1 + 0)) = 0 := by
      simp
    rw [hrw, hself, hbin]
    simp
  · -- positive case: t > 0, transport through the coupling
    obtain ⟨heqmass, hsumabs⟩ := pos_neg_sums p q hps hqs
    have htpos : 0 < tvHalf p q := by
      simp only [tvHalf]
      positivity
    -- the states A = diagonal p, B = diagonal q
    have hpsdA : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef p hp
    have hpsdB : (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef q hq
    have hpsdU : (Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef (posPart p q) (posPart_nonneg p q)
    have hpsdV : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).PosSemidef :=
      diagonal_posSemidef (negPart p q) (negPart_nonneg p q)
    have htrA : (Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))).trace = 1 := by
      simp
      exact_mod_cast hps
    have htrB : (Matrix.diagonal (fun i => ((q i : ℝ) : ℂ))).trace = 1 := by
      simp
      exact_mod_cast hqs
    -- the common mass t = ∑ posPart = ∑ negPart = ‖p−q‖₁/2
    have hmass : ∑ i, posPart p q i = (∑ i, |p i - q i|) / 2 := by
      have heq2 : (∑ i, posPart p q i) * 2 = ∑ i, |p i - q i| := by
        nlinarith [heqmass, hsumabs]
      field_simp
      linarith [heq2]
    have htrU : (Matrix.diagonal (fun i => ((posPart p q i : ℝ) : ℂ))).trace
        = ((∑ i, posPart p q i : ℝ) : ℂ) := by
      simp
    have htrV : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).trace
        = ((∑ i, negPart p q i : ℝ) : ℂ) := by
      simp
    have htcast : ((∑ i, posPart p q i : ℝ) : ℂ) = (tvHalf p q : ℂ) := by
      simp only [tvHalf]
      exact_mod_cast hmass
    have htVeq : (Matrix.diagonal (fun i => ((negPart p q i : ℝ) : ℂ))).trace
        = (tvHalf p q : ℂ) := by
      rw [htrV, ← heqmass]
      exact htcast
    have hbound := entropy_coupling_bound (ι := ι)
      ⟨hpsdA, htrA⟩ ⟨hpsdB, htrB⟩ hpsdV hpsdU htpos htVeq
      (by rw [htrU]; exact htcast) hcoupling
    rw [hbridge p hp, hbridge q hq] at hbound
    simpa [shannon] using hbound

end DiagPSD

end Hagi.Information
