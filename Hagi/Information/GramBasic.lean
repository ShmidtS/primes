/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

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

namespace Hagi.Quantum

universe u_1 u_2

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix

namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

def gram (A : Matrix ι κ ℂ) : Matrix ι ι ℂ := A * Aᴴ

def mass (A : Matrix ι κ ℂ) : ℝ := (gram A).trace.re

def logGram (A : Matrix ι κ ℂ) : ℝ := Real.log ‖(1+gram A).det‖


end GAD
end
end Hagi.Quantum
