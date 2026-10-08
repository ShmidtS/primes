/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Information.LogDetEntropy
import Hagi.Information.GramBasic

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

namespace Hagi.Quantum

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
  let F : Matrix ι (α × ι) ℂ := fun i ak ↦ GAD.spectralFactor (hA ak.1) i ak.2
  have hgram : GAD.gram F = ∑ a, A a := by
    ext i j
    change (∑ ak : α × ι, GAD.spectralFactor (hA ak.1) i ak.2 *
      star (GAD.spectralFactor (hA ak.1) j ak.2)) = (∑ a, A a) i j
    simp only [Fintype.sum_prod_type,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun M : Matrix ι ι ℂ ↦ M i j) (GAD.spectralFactor_gram (hA a))
  have hdiag (ak : α × ι) : ((Fᴴ*F) ak ak).re = (hA ak.1).isHermitian.eigenvalues ak.2 := by
    change (∑ i, star (F i ak)*F i ak).re = _
    simp only [Complex.re_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,F]
    exact GAD.spectralFactor_column (hA ak.1) ak.2
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
end Hagi.Quantum
