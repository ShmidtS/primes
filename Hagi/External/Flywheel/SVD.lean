import Hagi.External.Flywheel.SVDCore
import Hagi.External.Flywheel.SVDEigenvalues
import Hagi.External.Flywheel.SVDDiagonal
import Hagi.External.Flywheel.SVDTruncated
import Hagi.External.Flywheel.SVDReal
import Hagi.External.Flywheel.SVDRectangular
import Hagi.External.Flywheel.SVDRectangularOrdering
import Hagi.External.Flywheel.SVDRectangularNorms
import Hagi.External.Flywheel.SVDRectangularDecomposition
import Hagi.External.Flywheel.SVDRectangularCoherence

/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Singular Value Decomposition

Singular values σᵢ(A) := √λᵢ(Aᴴ A). Standard factorisation A = UΣVᴴ.

## References

[1] Horn, R.A. & Johnson, C.R. (2012). Matrix Analysis, 2nd ed.
    Cambridge University Press. Ch. 7 (Positive Definite Matrices).
[2] Golub, G.H. & Van Loan, C.F. (2013). Matrix Computations, 4th ed.
    Johns Hopkins University Press. §2.5.
[3] Mathlib4 spectral theorem: `Matrix.IsHermitian.spectral_theorem`

## Implementation Notes

We build SVD from the spectral decomposition of the Gram matrix Aᴴ A which
is postive semidefinite hence admits real non-negative eigenvalues. The left
singular vectors are then constructed via polar decomposition (CFC.sqrt).
-/

namespace Hagi.External.Flywheel
end Hagi.External.Flywheel
