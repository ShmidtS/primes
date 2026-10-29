import Mathlib
import Hagi.Step.GPM

/-!
# MicroStepCert — композиционный сертификат микро-шага

Multi-scale Amortized Engine (дизайн-директива): микро-шаг
выполняется в низкоранговом GPM-подпространстве — SafeQP
размерности r ≪ d. Здесь формализован МОСТ рычагов:
одновременность спуска на новой задаче и нулевого
забывания старых.

* `microstep_cert`: из L-гладкости E на шаге ΔW
  (E(W+ΔW) ≤ E W + ⟨G, ΔW⟩ + L/2·‖ΔW‖²_F), дессент-условия
  ⟨G, ΔW⟩ ≤ -ε и ортогональности GPM (gpmOrth ΔW xs)
  следует: энергия падает с гарантией И старые входы
  воспроизводятся ТОЧНО ((W+ΔW)·x_k = W·x_k ∀k).
* `microstep_net_drop`: при доминировании первого порядка
  над квадратичным членом (L/2·‖ΔW‖²_F < ε) энергия
  СТРОГО убывает — чистый выигрыш сертифицированного
  микро-шага.
-/

namespace Hagi.Unified.MicroStepCert

open Matrix

variable {m n K : ℕ}

/-- Скалярное произведение Фробениуса ⟨A, B⟩ = ∑_{i,j} A_ij·B_ij. -/
def frobDot (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Квадрат нормы Фробениуса. -/
def frobSq (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  frobDot A A

theorem frobSq_eq (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = ∑ i, ∑ j, (A i j) ^ 2 := by
  unfold frobSq frobDot
  congr 1
  funext i
  congr 1
  funext j
  ring

/-- Композиционный сертификат микро-шага: спуск + нулевое
забывание одновременно (МОСТ рычага 4 GPM и descent-леммы). -/
theorem microstep_cert
    (E : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (G : Matrix (Fin m) (Fin n) ℝ) (L ε : ℝ)
    (hsmooth : E (W + ΔW) ≤ E W + frobDot G ΔW
      + L / 2 * frobSq ΔW)
    (hgrad : frobDot G ΔW ≤ -ε)
    (horth : Hagi.Step.gpmOrth ΔW xs) :
    E (W + ΔW) ≤ E W - ε + L / 2 * frobSq ΔW
      ∧ ∀ k, (W + ΔW) *ᵥ (xs k) = W *ᵥ (xs k) := by
  refine ⟨?_, fun k => Hagi.Step.gpm_zero_forgetting W ΔW xs horth k⟩
  linarith [hsmooth, hgrad]

/-- При доминировании линейного члена над квадратичным
(малый шаг): строгий чистый спуск сертифицированного
микро-шага. -/
theorem microstep_net_drop
    (E : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (W ΔW : Matrix (Fin m) (Fin n) ℝ)
    (xs : Fin K → (Fin n → ℝ))
    (G : Matrix (Fin m) (Fin n) ℝ) (L ε : ℝ)
    (hsmooth : E (W + ΔW) ≤ E W + frobDot G ΔW
      + L / 2 * frobSq ΔW)
    (hgrad : frobDot G ΔW ≤ -ε)
    (horth : Hagi.Step.gpmOrth ΔW xs)
    (hsmall : L / 2 * frobSq ΔW < ε) :
    E (W + ΔW) < E W
      ∧ ∀ k, (W + ΔW) *ᵥ (xs k) = W *ᵥ (xs k) := by
  have h := (microstep_cert E W ΔW xs G L ε hsmooth hgrad horth).1
  exact ⟨by linarith,
    fun k => Hagi.Step.gpm_zero_forgetting W ΔW xs horth k⟩

end Hagi.Unified.MicroStepCert
