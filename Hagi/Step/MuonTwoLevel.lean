/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# MuonTwoLevel — точная ортогонализация против NS-аппроксимации

Уровень 1 (контракт, не доказан здесь): идеальный шаг
`O = U·Vᵀ` (SVD градиента) ортогонален — спектральная
норма 1.

Уровень 2 (доказан): `ns_gap_scaled` —
`Σᵢ (p(σᵢ) − 1)² ≤ r·maxᵢ (p(σᵢ) − 1)²`:
бюджет отклонения факторизуется в ранг × худшую поточечную
ошибку полинома. Frobenius-тождество, коэффициенты полинома
и сходимость NS-итераций — не доказаны.
-/

namespace Hagi

open Finset

/-- При `0 ≤ M` и `(dev i)² ≤ M` для всех i:
`Σ_i (dev i)² ≤ r·M` (бюджет отклонения = ранг ×
худший поточечный член). -/
theorem ns_gap_scaled (r : ℕ) (dev : Fin r → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hdev : ∀ i, (dev i)^2 ≤ M) :
    ∑ i, (dev i)^2 ≤ r * M := by
  have h1 : ∑ i, (dev i)^2 ≤ ∑ _i, M :=
    Finset.sum_le_sum fun i _ => hdev i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  exact h1


end Hagi
