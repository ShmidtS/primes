import Mathlib.Tactic
import Hagi.Model.StageSemantics
import Hagi.Foundations.Telescope

set_option linter.style.header false

/-!
# Model.CycleCertificate — сертификат полного цикла

Единый локальный сертификат перехода (аудит 4, §6.3): все
глобальные гарантии системы выводятся из композиции
независимых компонентов сертификата — прогресс, потенциал,
риск, бюджет. Компоненты логически независимы: режим без
роста, без риска или без затрат доказывает только свои
поля.

Главный результат — `cycle_certificate_composition`: один
сертификат на горизонте T даёт сразу три глобальных факта
(точный рост, телескоп потенциала, точный бюджетный ledger).
Инстанс `growSeq_cycle_certificate` подключает честную
платную траекторию (`StageSemantics.growSeq`) к сертификатному
слою — первый мост «механизм → сертификат» (аудит 4, этап 6).
-/

namespace Hagi.Model

open Hagi.Foundations Finset

/-- **Сертификат полного цикла** на горизонте `T` для
последовательностей capability `C`, потенциала `Φ` и бюджета
`B`. Независимые компоненты (аудит 4 §6.3, схема):

* прогресс: `C (t+1) = C t + gain t` — точный закон прироста;
* потенциал: `Φ (t+1) ≤ Φ t − drop t + risk t` — спуск с шумом;
* бюджет: `B (t+1) = B t − spend t` — точный ledger.

Каждый компонент доказывается своим механизмом; часть полей
может быть нулевой (режим без роста / без риска / без затрат). -/
structure CycleCertificate (T : ℕ) (C Φ B : ℕ → ℝ) where
  /-- Измеренный прирост capability за цикл t. -/
  gain : ℕ → ℝ
  /-- Прирост честен (неотрицателен) в горизонте. -/
  h_gain_nonneg : ∀ t < T, 0 ≤ gain t
  /-- Точный закон прогресса: capability растёт ровно на gain. -/
  cap_step : ∀ t < T, C (t + 1) = C t + gain t
  /-- Сертифицированное убывание потенциала за цикл. -/
  drop : ℕ → ℝ
  /-- Шум/риск-компонента шага потенциала. -/
  risk : ℕ → ℝ
  h_risk_nonneg : ∀ t < T, 0 ≤ risk t
  /-- Локальный сертификат спуска потенциала. -/
  pot_descent : ∀ t < T, Φ (t + 1) ≤ Φ t - drop t + risk t
  /-- Расход бюджета за цикл t. -/
  spend : ℕ → ℝ
  /-- Расход честен (неотрицателен) в горизонте. -/
  h_spend_nonneg : ∀ t < T, 0 ≤ spend t
  /-- Точный бюджетный ledger. -/
  budget_ledger : ∀ t < T, B (t + 1) = B t - spend t

/-- **Композиция сертификата**: один `CycleCertificate` на
горизонте `T` даёт одновременно

* точный рост: `C T = C 0 + Σ gain`;
* телескоп потенциала: `Φ T ≤ Φ 0 − Σ drop + Σ risk`
  (`lyapunov_gain_noise`);
* точный бюджет: `B T = B 0 − Σ spend`.

Глобальные свойства выводятся из локального контракта —
схема «локальные сертификаты → глобальные гарантии» аудита 4. -/
theorem cycle_certificate_composition (T : ℕ) (C Φ B : ℕ → ℝ)
    (cert : CycleCertificate T C Φ B) :
    C T = C 0 + ∑ t ∈ Finset.range T, cert.gain t
      ∧ Φ T ≤ Φ 0 - ∑ t ∈ Finset.range T, cert.drop t
        + ∑ t ∈ Finset.range T, cert.risk t
      ∧ B T = B 0 - ∑ t ∈ Finset.range T, cert.spend t := by
  -- точный аддитивный телескоп, горизонто-ограниченный
  have hC : ∀ T' : ℕ, T' ≤ T →
      C T' = C 0 + ∑ t ∈ Finset.range T', cert.gain t := by
    intro T' hle
    induction T' with
    | zero => simp
    | succ n ih =>
        have hn : n < T := by omega
        have hstep := cert.cap_step n hn
        rw [Finset.sum_range_succ, hstep, ih (by omega)]
        ring
  have hB : ∀ T' : ℕ, T' ≤ T →
      B T' = B 0 - ∑ t ∈ Finset.range T', cert.spend t := by
    intro T' hle
    induction T' with
    | zero => simp
    | succ n ih =>
        have hn : n < T := by omega
        have hstep := cert.budget_ledger n hn
        rw [Finset.sum_range_succ, hstep, ih (by omega)]
        ring
  exact ⟨hC T (le_refl T), lyapunov_gain_noise cert.pot_descent,
    hB T (le_refl T)⟩

/-! ### Инстанс: честная платная траектория -/

/-- Capability неотрицательна вдоль честной траектории при
неотрицательном старте (сохранение `0 ≤ C` переходом с
`α ≥ 0`). -/
theorem growSeq_capability_nonneg (alpha mu : ℝ)
    (hmu : 0 ≤ mu) (hα1 : 0 ≤ 1 + alpha) (hα : 0 ≤ alpha)
    (S0 : {s : GrowthState ℝ // 0 ≤ mu * s.capability})
    (hC0 : 0 ≤ S0.val.capability) (t : ℕ) :
    0 ≤ (growSeq alpha mu hmu hα1 S0 t).val.capability := by
  induction t with
  | zero => exact hC0
  | succ t ih =>
      have hcap := growAdvance_capability alpha mu
        (growSeq alpha mu hmu hα1 S0 t).val
        (growSeq alpha mu hmu hα1 S0 t).property
      simp only [growSeq]
      rw [hcap]
      linarith [mul_nonneg hα ih]

/-- **Честная платная траектория даёт сертификат цикла**:
каждый переход `growSeq` (эффекты, вычисленные из текущего
состояния) доставляет `CycleCertificate` с приростом
`gain t = α·C t`, расходом `spend t = μ·C t`, постоянной
энергией (drop = risk = 0) и точным бюджетом. Первый мост
«механизм → сертификат»: глобальные гарантии
(`cycle_certificate_composition`) применимы к траектории без
дополнительных гипотез. -/
noncomputable def growSeq_cycle_certificate (alpha mu : ℝ)
    (hmu : 0 ≤ mu) (hα1 : 0 ≤ 1 + alpha) (hα : 0 ≤ alpha)
    (S0 : {s : GrowthState ℝ // 0 ≤ mu * s.capability})
    (hC0 : 0 ≤ S0.val.capability) (T : ℕ) :
    CycleCertificate T
      (fun t => (growSeq alpha mu hmu hα1 S0 t).val.capability)
      (fun _ => S0.val.energy)
      (fun t => (growSeq alpha mu hmu hα1 S0 t).val.budget) where
  gain t := alpha * (growSeq alpha mu hmu hα1 S0 t).val.capability
  h_gain_nonneg t _ := mul_nonneg hα
    (growSeq_capability_nonneg alpha mu hmu hα1 hα S0 hC0 t)
  cap_step t _ := by
    simp only [growSeq]
    exact (growAdvance_capability alpha mu
      (growSeq alpha mu hmu hα1 S0 t).val
      (growSeq alpha mu hmu hα1 S0 t).property).symm
  drop _ := 0
  risk _ := 0
  h_risk_nonneg _ _ := le_refl 0
  pot_descent t _ := by
    show (fun _ => S0.val.energy) (t + 1)
      ≤ (fun _ => S0.val.energy) t - 0 + 0
    simp only []
    ring_nf
    exact le_refl _
  spend t := mu * (growSeq alpha mu hmu hα1 S0 t).val.capability
  h_spend_nonneg t _ := (growSeq alpha mu hmu hα1 S0 t).property
  budget_ledger t _ := by
    simp only [growSeq]
    exact growAdvance_budget alpha mu
      (growSeq alpha mu hmu hα1 S0 t).val
      (growSeq alpha mu hmu hα1 S0 t).property

/-- Энергия постоянна вдоль честной траектории
(stateGrowthEffects не трогает энергию). -/
theorem growSeq_energy_const (alpha mu : ℝ)
    (hmu : 0 ≤ mu) (hα1 : 0 ≤ 1 + alpha)
    (S0 : {s : GrowthState ℝ // 0 ≤ mu * s.capability}) (t : ℕ) :
    (growSeq alpha mu hmu hα1 S0 t).val.energy = S0.val.energy := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have h1 : (advance (growSeq alpha mu hmu hα1 S0 t).val
          (growInput alpha mu (growSeq alpha mu hmu hα1 S0 t).val
            (growSeq alpha mu hmu hα1 S0 t).property)).energy
          = (growSeq alpha mu hmu hα1 S0 t).val.energy := rfl
      show (advance (growSeq alpha mu hmu hα1 S0 t).val
          (growInput alpha mu (growSeq alpha mu hmu hα1 S0 t).val
            (growSeq alpha mu hmu hα1 S0 t).property)).energy
          = S0.val.energy
      rw [h1, ih]

/-- **Сквозная гарантия из сертификата**: композиция
сертификата честной траектории даёт три глобальных факта
ОДНОЙ теоремой — точный рост (в частности
`C 0 ≤ C T` при `α ≥ 0`), невозрастание энергии (drop=0,
risk=0) и точный бюджетный ledger. Формы «механизм →
локальный контракт → глобальная гарантия» аудита 4. -/
theorem honest_trajectory_global (alpha mu : ℝ)
    (hmu : 0 ≤ mu) (hα1 : 0 ≤ 1 + alpha) (hα : 0 ≤ alpha)
    (S0 : {s : GrowthState ℝ // 0 ≤ mu * s.capability})
    (hC0 : 0 ≤ S0.val.capability) (T : ℕ) :
    (growSeq alpha mu hmu hα1 S0 T).val.capability
      = (growSeq alpha mu hmu hα1 S0 0).val.capability
        + ∑ t ∈ Finset.range T, alpha *
          (growSeq alpha mu hmu hα1 S0 t).val.capability
      ∧ (growSeq alpha mu hmu hα1 S0 T).val.energy
        ≤ (growSeq alpha mu hmu hα1 S0 0).val.energy
      ∧ (growSeq alpha mu hmu hα1 S0 T).val.budget
        = (growSeq alpha mu hmu hα1 S0 0).val.budget
          - ∑ t ∈ Finset.range T, mu *
            (growSeq alpha mu hmu hα1 S0 t).val.capability := by
  have hcomp := cycle_certificate_composition T _ _ _
    (growSeq_cycle_certificate alpha mu hmu hα1 hα S0 hC0 T)
  simp only [growSeq_cycle_certificate] at hcomp
  obtain ⟨h1, h2, h3⟩ := hcomp
  refine ⟨h1, ?_, h3⟩
  rw [growSeq_energy_const, growSeq_energy_const]

end Hagi.Model
