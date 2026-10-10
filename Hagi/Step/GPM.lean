/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.SafeQP
set_option linter.style.header false

/-!
# GPM — SafeQP ↔ GPM мост: точная ортогональность шага

Модель: линейный слой `y = W·x`; старые задачи — входы
`xs k`; `actSigma xs = Σ_k outer(x_k, x_k)` — ковариация
активаций (PSD).

* `gpm_zero_forgetting`: при ортогональности строк ΔW всем
  старым входам (`gpmOrth`) —
  `(W + ΔW)·x_k = W·x_k` для всех k и любого W
  (ΔL_old = 0 точно);
* `sigma_orth_zero`: `ΔW·x_k = 0` для всех k ⇒
  `ΔW·Σ = 0`;
* `sigma_orth_necessary`: если для каждой строки сумма
  квадратов `Σ_k ⟨ΔW·i, x_k⟩² = 0`, то
  `ΔW·x_k = 0` для всех k — вместе с предыдущим:
  шаг в ker Σ ⟺ нулевой residual response.

Точная ортогональность — предельный случай ε-бюджета
SafeQP при ε → 0; для глубоких сетей нужна телескопическая
граница (ErrorProp); Σ оценивается по конечным активациям.
-/

open Finset
open scoped Matrix

namespace Hagi.Step

variable {m n K : ℕ}

/-- Внешнее произведение: `outerP v w = v·wᵀ`. -/
def outerP (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => v i * w j

/-- Ковариация активаций старых задач:
`actSigma xs l j = Σ_k x_k(l)·x_k(j)` (PSD по построению). -/
def actSigma (xs : Fin K → (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun l j => ∑ k, xs k l * xs k j

/-- `gpmOrth ΔW xs`: каждая строка ΔW ортогональна всем
старым входам (`dotProduct` строки и `xs k` равен 0). -/
def gpmOrth (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) : Prop :=
  ∀ i k, dotProduct (ΔW i) (xs k) = 0

/-- `(M *ᵥ v) i = dotProduct (M i) v`. -/
theorem mulVec_eq_dotProduct (M : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (i : Fin m) :
    (M *ᵥ v) i = dotProduct (M i) v := by
  classical
  simp [Matrix.mulVec, dotProduct]

/-- При `gpmOrth ΔW xs` и любом W:
`(W + ΔW) *ᵥ (xs k) = W *ᵥ (xs k)` — нулевой residual
response на каждом старом входе. -/
theorem gpm_zero_forgetting (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (horth : gpmOrth ΔW xs) (k : Fin K) :
    (W + ΔW) *ᵥ (xs k) = W *ᵥ (xs k) := by
  have hzero : ΔW *ᵥ (xs k) = 0 := by
    funext i
    rw [mulVec_eq_dotProduct]
    exact horth i k
  rw [Matrix.add_mulVec, hzero, add_zero]

/-- Если `ΔW *ᵥ (xs k) = 0` для всех k, то
`ΔW * actSigma xs = 0`. -/
theorem sigma_orth_zero (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (hzero : ∀ k, ΔW *ᵥ (xs k) = 0) :
    ΔW * actSigma xs = 0 := by
  funext i j
  have hexpand : (ΔW * actSigma xs) i j
      = ∑ k, dotProduct (ΔW i) (xs k) * xs k j := by
    simp only [Matrix.mul_apply, actSigma, Matrix.of_apply, dotProduct]
    rw [Finset.sum_congr rfl (fun l _ => by rw [mul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => by
      rw [Finset.sum_congr rfl (fun l _ => by ring : ∀ l ∈ Finset.univ,
        ΔW i l * (xs k l * xs k j)
          = (ΔW i l * xs k l) * xs k j)]
      rw [← Finset.sum_mul]
  rw [hexpand]
  refine Finset.sum_eq_zero ?_
  intro k _
  have h := congrFun (hzero k) i
  rw [mulVec_eq_dotProduct, Pi.zero_apply] at h
  rw [h, zero_mul]

/-- Если для каждой строки i выполнено
`Σ_k (dotProduct (ΔW i) (xs k))² = 0`, то
`ΔW *ᵥ (xs k) = 0` для всех k. Вместе с `sigma_orth_zero`:
шаг в ker Σ ⟺ нулевой residual response. Условие
измеримо (суммы квадратов на активациях) — применимо как
certified-гейт без явного Σ. -/
theorem sigma_orth_necessary (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (hquad : ∀ i, ∑ k, (dotProduct (ΔW i) (xs k))
        * (dotProduct (ΔW i) (xs k)) = 0)
    (k : Fin K) :
    ΔW *ᵥ (xs k) = 0 := by
  funext i
  rw [mulVec_eq_dotProduct]
  simp only [Pi.zero_apply]
  by_contra hne
  have hpos : (0:ℝ) < (dotProduct (ΔW i) (xs k))
      * (dotProduct (ΔW i) (xs k)) := by
    have h2 := sq_pos_of_ne_zero hne
    have h3 : (dotProduct (ΔW i) (xs k)) ^ 2
        = (dotProduct (ΔW i) (xs k))
          * (dotProduct (ΔW i) (xs k)) := by ring
    linarith
  have hge : (dotProduct (ΔW i) (xs k)) * (dotProduct (ΔW i) (xs k))
      ≤ ∑ k', (dotProduct (ΔW i) (xs k'))
        * (dotProduct (ΔW i) (xs k')) := by
    have hrest := Finset.sum_erase_add (Finset.univ)
      (fun k' => (dotProduct (ΔW i) (xs k'))
        * (dotProduct (ΔW i) (xs k'))) (Finset.mem_univ k)
    have hnn : (0:ℝ) ≤ ∑ k' ∈ Finset.univ.erase k,
        (dotProduct (ΔW i) (xs k')) * (dotProduct (ΔW i) (xs k')) :=
      Finset.sum_nonneg fun k' _ => mul_self_nonneg _
    have := hquad i
    linarith [hrest, hnn, this]
  have h0 := hquad i
  linarith

end Hagi.Step

namespace Hagi
export Hagi.Step (outerP actSigma gpmOrth mulVec_eq_dotProduct gpm_zero_forgetting sigma_orth_zero sigma_orth_necessary)
end Hagi
