import Mathlib.Tactic
import Hagi.Learning.HadamardComplete

set_option linter.style.header false

/-!
# HadamardParseval — энергетическое разложение (цикл 26)

PARSEVAL для доменного разложения HRCN: энергия сигнала
равна сумме энергий доменных компонент:
  ⟨v, v⟩ = Σ_w ‖P_w v‖².
Следствие полноты (charProjR_sum_eq_self, цикл 25) и
ортогональности (charProjR_orthog, цикл 7): разложение —
ортогональная прямая сумма, энергия точно делится по доменам
БЕЗ перекрёстных членов. Gauge-эффект одного домена не
изменяет энергию остальных; битовый бюджет домена w
контролирует только ‖P_w v‖² — энергетическая форма
компромисса объём↔качество на уровне архитектуры.
-/

open Finset Hagi.Core

namespace Hagi.Learning.HadamardParseval

open Hagi.Learning.HadamardProjectors Hagi.Learning.HadamardComplete

variable {k : ℕ}

/-! ### Вспомогательные тождества -/

/-- Линейность: dotProduct (c • a) b = c · (a ⬝ᵥ b). -/
theorem dotProduct_smul_left (c : ℝ)
    (a b : (Fin k → ZMod 2) → ℝ) :
    dotProduct (c • a) b = c * dotProduct a b := by
  unfold dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc]
  rw [Finset.mul_sum]
  ring

/-- Сумма в первом аргументе: ⟨Σ_w f w, v⟩ = Σ_w ⟨f w, v⟩. -/
theorem dotProduct_sum_left (f : (Fin k → ZMod 2)
      → ((Fin k → ZMod 2) → ℝ)) (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (∑ w, f w) v = ∑ w, dotProduct (f w) v := by
  unfold dotProduct
  simp only [Finset.sum_apply]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-! ### Доменная энергия -/

/-- P_w v — скалярное кратное характера:
P_w v = (⟨χ_w, v⟩ / 2^k) • χ_w. -/
theorem charProjR_eq_smul (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    ∃ c : ℝ, charProjR w v = c • charRowR w ∧
      c * (2 ^ k : ℕ) = dotProduct (charRowR w) v := by
  refine ⟨dotProduct (charRowR w) v / (2 ^ k : ℕ), rfl, ?_⟩
  have h2 : ((2:ℕ)^k : ℝ) ≠ 0 := by positivity
  field_simp

/-- Норма доменной компоненты:
‖P_w v‖² = ⟨χ_w, v⟩² / 2^k. -/
theorem charProjR_norm_sq (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (charProjR w v) (charProjR w v)
      = (dotProduct (charRowR w) v) ^ 2 / (2 ^ k : ℕ) := by
  obtain ⟨c, hproj, hcscale⟩ := charProjR_eq_smul w v
  have hsmul_right : dotProduct (charRowR w) (c • charRowR w)
      = c * dotProduct (charRowR w) (charRowR w) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    have hreg : ∀ i : Fin k → ZMod 2,
        charRowR w i * (c * charRowR w i)
          = c * (charRowR w i * charRowR w i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hreg i),
      Finset.mul_sum]
  rw [hproj, dotProduct_smul_left, hsmul_right]
  have hnorm := charRowR_norm w
  rw [hnorm]
  have hc : c = dotProduct (charRowR w) v / (2^k:ℕ) := by
    rw [eq_div_iff (by positivity : ((2^k:ℕ):ℝ) ≠ 0)]
    exact hcscale
  rw [hc]
  field_simp

/-- Перекрёстная энергия нулевая: ⟨P_w v, P_u v⟩ = 0 при
w ≠ u (ортогональность проекторов). -/
theorem charProjR_cross_zero {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (charProjR w v) (charProjR u v) = 0 := by
  obtain ⟨cw, hpw, _⟩ := charProjR_eq_smul w v
  obtain ⟨cu, hpu, _⟩ := charProjR_eq_smul u v
  have hsmul_right : dotProduct (charRowR w) (cu • charRowR u)
      = cu * dotProduct (charRowR w) (charRowR u) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    have hreg : ∀ i : Fin k → ZMod 2,
        charRowR w i * (cu * charRowR u i)
          = cu * (charRowR w i * charRowR u i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hreg i),
      Finset.mul_sum]
  rw [hpw, hpu, dotProduct_smul_left, hsmul_right]
  have horth := charRowR_orthog hwu
  rw [horth, mul_zero, mul_zero]

/-! ### ГЛАВНАЯ ТЕОРЕМА: PARSEVAL -/

/-- PARSEVAL для доменного разложения: полная энергия сигнала
равна сумме энергий доменных компонент. Прямое следствие
полноты базиса (цикл 25): ⟨v, v⟩ = ⟨Σ_w P_w v, v⟩ = Σ_w ‖P_w v‖².
Перекрёстных членов НЕТ (ортогональность). Энергия делится
по доменам точно — изоляция доменов энергетически честна. -/
theorem parseval (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct v v
      = ∑ w : Fin k → ZMod 2,
          dotProduct (charProjR w v) (charProjR w v) := by
  have hcomp : v ⬝ᵥ v = (∑ w, charProjR w v) ⬝ᵥ v := by
    rw [charProjR_sum_eq_self v]
  rw [hcomp, dotProduct_sum_left]
  refine Finset.sum_congr rfl fun w _ => ?_
  -- ⟨P_w v, v⟩ = ‖P_w v‖²: v = P_w v + ортодополнение,
  -- ⟨P_w v, орто⟩ = 0. Прямое вычисление:
  have h1 : dotProduct (charProjR w v) v
      = (dotProduct (charRowR w) v) ^ 2 / (2 ^ k : ℕ) := by
    obtain ⟨c, hproj, hcscale⟩ := charProjR_eq_smul w v
    rw [hproj, dotProduct_smul_left]
    have hc : c = dotProduct (charRowR w) v / (2^k:ℕ) := by
      rw [eq_div_iff (by positivity : ((2^k:ℕ):ℝ) ≠ 0)]
      exact hcscale
    rw [hc]
    field_simp
  rw [h1, charProjR_norm_sq]

end Hagi.Learning.HadamardParseval
