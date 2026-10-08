/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# EntropyDefs — the spectral entropy kernel (h2-Fannes port,
layer 1/N)

Ported verbatim from openai/math,
OAI.InformationTheory.AmplitudeDamping.Model (the E:/math
audit, Fam 276): the spectral definition of entropy
−Tr(P log P) with 0·log 0 = 0 (cfc Real.negMulLog), the
IsState predicate, and the QMatrix/Basis abbreviations.
The downstream target of the campaign is
`entropy_coupling_bound` (the refined Fannes/Zhang–Shirokov
bound with the singular h₂ part) in the top layer.
-/

namespace Hagi.Quantum

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

end
end Hagi.Quantum
