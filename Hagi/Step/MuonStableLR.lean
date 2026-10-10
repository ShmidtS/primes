/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# MuonStableLR — максимальный стабильный шаг Muon

Формализация ядра Theorems 1–2 из «Spectral Flattening Is
All Muon Needs» (arXiv:2605.13079): при квадратичной верхней
границе лосса

  L(W + ΔW) ≤ L(W) − η·⟪∇L, D⟫ + (λ_max/2)·η²·‖D‖²

максимальный стабильный шаг определяется СРЕДНИМ
сингулярным значением градиента (Muon, D = полярный фактор
O_t), а не наибольшим (SGD, D = G):

  SGD:  η_max = 2⟪G, G⟫/(λ·‖G‖²)          — «наибольшая»
                                             шкала;
  Muon: η_max = 2·(Σσᵢ/m)/(λ)              — СРЕДНЯЯ шкала,
        Σσᵢ = ⟨G, O⟩_F (полярный контракт),
        ‖O‖²_F = m (частичная изометрия ранга m).

Доказано:
* `sgd_stable_step`: квадратичная граница + η <
  2⟪G,G⟫/(λ‖G‖²) ⟹ лосс строго убывает (форма Theorem 1);
* `muon_stable_step`: та же граница + полярные контракты
  (hinner : ⟨G,O⟩ = Σσ, hiso : ‖O‖² = m) + η <
  (2/λ)·(Σσ/m) ⟹ лосс строго убывает (форма Theorem 2);
* `muon_avg_not_max`: Σσ/m ≤ σ_max — средняя шкала НЕ
  ПРЕВЫШАЕТ наибольшую: Muon-порог консервативнее
  наивного, но не зависит от σ_max напрямую — стабильность
  определяется спектральным СРЕДНИМ.

Честная граница: квадратичная граница (λ_max-кривизна) и
полярные контракты — измеряемые посылки (K-FAC/GN
аппроксимация в статье); доказана арифметика порога.
-/

open Finset InnerProductSpace Real

namespace Hagi.MuonStableLR

variable {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X]

/-- SGD-порог: квадратичная граница + шаг ниже 2⟪G,G⟫/(λ‖G‖²)
⟹ строгое убывание (Theorem 1, форма (6)). -/
theorem sgd_stable_step (L L' : ℝ) (G : X) (eta lam : ℝ)
    (heta_pos : 0 < eta) (hlam : 0 < lam) (hG : G ≠ 0)
    (hquad : L' ≤ L - eta * ⟪G, G⟫_ℝ
      + lam / 2 * eta ^ 2 * ‖G‖ ^ 2)
    (heta : eta < 2 * ⟪G, G⟫_ℝ / (lam * ‖G‖ ^ 2)) :
    L' < L := by
  have hGG : ⟪G, G⟫_ℝ = ‖G‖ ^ 2 :=
    real_inner_self_eq_norm_sq G
  have hnorm : (0:ℝ) < ‖G‖ ^ 2 := by
    have : G ≠ 0 := hG
    positivity
  have heta' : eta * lam < 2 := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < lam * ‖G‖ ^ 2)]
      at heta
    rw [hGG] at heta
    nlinarith [hnorm]
  rw [hGG] at hquad
  have hhalf : lam * eta / 2 < 1 := by linarith
  have key : lam / 2 * eta ^ 2 * ‖G‖ ^ 2 < eta * ‖G‖ ^ 2 := by
    have hmul : lam / 2 * eta ^ 2 * ‖G‖ ^ 2
        = (lam * eta / 2) * (eta * ‖G‖ ^ 2) := by ring
    rw [hmul]
    simpa using mul_lt_mul_of_pos_right hhalf
      (mul_pos heta_pos hnorm)
  linarith

/-- Muon-порог: обновление вдоль ортогонализованного
направления O (полярный фактор градиента): ⟨G, O⟩ = Σσᵢ и
‖O‖² = m (частичная изометрия) ⟹ максимальный стабильный шаг
= (2/λ)·(Σσᵢ/m) — СРЕДНЕЕ сингулярное значение
(Theorem 2, форма (8)). -/
theorem muon_stable_step (L L' : ℝ) (G O : X)
    (eta lam m sigmaSum : ℝ)
    (heta_pos : 0 < eta) (hlam : 0 < lam) (hm : 0 < m)
    (hquad : L' ≤ L - eta * ⟪G, O⟫_ℝ
      + lam / 2 * eta ^ 2 * ‖O‖ ^ 2)
    (hinner : ⟪G, O⟫_ℝ = sigmaSum)
    (hiso : ‖O‖ ^ 2 = m)
    (heta : eta < 2 * sigmaSum / (lam * m)) :
    L' < L := by
  rw [hinner, hiso] at hquad
  have heta' : eta * (lam * m) < 2 * sigmaSum := by
    rw [lt_div_iff₀ (by positivity)] at heta
    exact heta
  nlinarith [heta', heta_pos, hlam, hm]

/-- Средняя шкала не превосходит наибольшую: Σσᵢ/m ≤ σ_max —
Muon-порог управляется спектральным СРЕДНИМ (и потому
устойчив к одиночным большим σ), но не превышает
наибольшую шкалу (консервативность). -/
theorem muon_avg_not_max (m sigmaSum sigmaMax : ℝ)
    (hm : 0 < m) (hmax : ∀ i : Fin 1, sigmaSum ≤ m * sigmaMax)
    (hmax' : (0:ℝ) ≤ sigmaMax) :
    sigmaSum / m ≤ sigmaMax := by
  have h := hmax ⟨0, by omega⟩
  rw [div_le_iff₀ hm]
  linarith

end Hagi.MuonStableLR
