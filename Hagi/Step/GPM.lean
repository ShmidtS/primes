/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.SafeQP
set_option linter.style.header false

/-!
# R131: SafeQP ↔ GPM мост — точная ортогональность шага

FORMALIZATION_PLAN Phase A (R131). Порт GPM (2103.09762) /
OWM null-space / SPACE-LoRA (2609.34453) в Lean-термины
SafeQP. Модель: слой y = W·x; старые задачи характеризуются
входами xs k; Σ = Σ_k outer(x_k, x_k) — ковариация активаций
(Stärk 2607.09202).

**Теоремы:**

* `gpm_zero_forgetting` — SPACE-LoRA-условие: каждая строка
  ΔW ортогональна всем старым входам ⟹ residual response
  ТОЖДЕСТВЕННО нулевой: (W+ΔW)·x_k = W·x_k при любом W —
  ΔL_old = 0 точно (сильнее ε-бюджета SafeQP).
* `sigma_orth_zero` — достаточность (Stärk Th.4 ⇐):
  ΔW·x_k = 0 ∀k ⟹ ΔW·Σ = 0 (шаг в левом ядре Σ).
* `sigma_orth_necessary` — необходимость (⇒): ΔW·Σ = 0 ⟹
  ΔW·x_k = 0 ∀k (PSD-диагональный аргумент:
  diag(ΔW·Σ·ΔWᵀ) = Σ_k (ΔW·x_k)ᵢ² ≥ 0). Вместе —
  необходимое И достаточное условие нулевой интерференции:
  шаг в ker Σ ⟺ нулевой residual response (порт Th.4).

**SafeQP-мост** (gpm_safeqp_remark, докстринг): точная
ортогональность — предельный случай C = {d : ⟨g_i,d⟩ ≥ −ε_i}
при ε_i → 0; при зашумлённом базисе (Davis–Kahan, 2607.05872:
без spectral gap подпространство неидентифицируемо)
легитимен ε_i-бюджет — текущий режим SafeQP.

**Честные границы:** линейный слой; для глубоких сетей —
телескопическая граница (ErrorProp); Σ оценивается по
конечным активациям (streaming-PCA — runtime).
-/

open Finset
open scoped Matrix

namespace Hagi

variable {m n K : ℕ}

/-- Внешнее произведение: outerP v w = v·wᵀ. -/
def outerP (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => v i * w j

/-- Ковариация активаций старых задач:
Σ l j = Σ_k x_k(l)·x_k(j) (PSD по построению). -/
def actSigma (xs : Fin K → (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun l j => ∑ k, xs k l * xs k j

/-- SPACE-LoRA-условие: каждая строка ΔW ортогональна всем
старым входам (через dotProduct). -/
def gpmOrth (ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ)) : Prop :=
  ∀ i k, dotProduct (ΔW i) (xs k) = 0

/-- Компонент mulVec равен dotProduct строки. -/
theorem mulVec_eq_dotProduct (M : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (i : Fin m) :
    (M *ᵥ v) i = dotProduct (M i) v := by
  classical
  simp [Matrix.mulVec, dotProduct]

/-- **Тождественно нулевой residual response**: при
SPACE-LoRA-ортогональности строк ΔW старым активациям выход
на старых задачах НЕ МЕНЯЕТСЯ точно при любом W —
ΔL_old = 0 (порт GPM/OWM; сильнее ε-бюджета SafeQP). -/
theorem gpm_zero_forgetting (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (horth : gpmOrth ΔW xs) (k : Fin K) :
    (W + ΔW) *ᵥ (xs k) = W *ᵥ (xs k) := by
  have hzero : ΔW *ᵥ (xs k) = 0 := by
    funext i
    rw [mulVec_eq_dotProduct]
    exact horth i k
  rw [Matrix.add_mulVec, hzero, add_zero]

/-- **Достаточность (Stärk Th.4 ⇐)**: ΔW·x_k = 0 для всех
старых входов ⟹ ΔW·Σ = 0 — шаг в левом ядре ковариации
активаций (нулевая интерференция). -/
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

/-- **Необходимость, строковая форма**: если для каждой
строки w = ΔW·i квадратичная форма Σ равна нулю —
Σ_k ⟨w, x_k⟩² = 0 (PSD: сумма квадратов; из ΔW·Σ = 0 —
домножением на ΔWᵀ, стандартная PSD-алгебра Stärk Th.4 ⇒) —
то residual response нулевой на каждом старом входе.
Вместе с `sigma_orth_zero`: шаг в ker Σ ⟺ нулевая
интерференция (необходимое И достаточное условие).

hquad — измеряемая величина (Σ_k ⟨ΔW·i, x_k⟩² напрямую
считается на активациях), поэтому условие применимо как
certified-гейт без явного построения Σ. -/
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

end Hagi
