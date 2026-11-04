import Mathlib.Tactic
import Hagi.Optimization.MomentumHB
import Hagi.Learning.TrainingTransition
import Hagi.Learning.BitBudget
import Hagi.Learning.RegCovPD

set_option linter.style.header false

/-!
# OptimalConfig — замкнутый вывод конфигурации (цикл 22)

Сведение теории воедино: НИ ОДИН параметр модели не
подбирается наугад — все параметры РАССЧИТЫВАЮТСЯ как функции
двух целевых величин:

  * ρ ∈ (0,1) — целевая скорость сходимости (фактор за шаг);
  * ε > 0 — целевой допуск ошибки квантования.

Выводимые параметры (конструктивные функции от (ρ, ε)):

  * β = ρ²            — momentum (heavy-ball): по критическому
                        режиму hb_rate_critical |λ*| = √β = ρ;
  * η = (1−ρ)²        — скорость обучения: критическое
                        демпфирование hb_critical_discriminant
                        (двойной корень λ²−(1+β−η)λ+β при
                        η=(1−√β)²);
  * N ≤ (2ε)²         — максимум тернарных весов слоя
                        (m·r ≤ 4ε²): обратная сторона
                        ternary_bit_error_bound — ошибка слоя
                        ≤ ε·‖x‖.

Теоремы: cfg_rate (√β = ρ), cfg_stability (условия hb_stability
выполнены автоматически), cfg_descent (шаг TrainingTransition
с η=(1−ρ)² строго убывает — условия 0<η, T·η<2 автоматны при
T=1), cfg_bits (бюджет весов ↔ допуск ε).
-/

open Finset Hagi.Optimization.MomentumHB

namespace Hagi.Unified.OptimalConfig

/-- Целевая конфигурация: ВСЕ параметры — вычислимые функции
целевых величин ρ (скорость) и ε (допуск), подбора нет. -/
structure OptimalConfig (rho eps : ℝ) where
  /-- Momentum: β = ρ² (из |λ*| = √β = ρ). -/
  beta : ℝ := rho ^ 2
  /-- Скорость обучения: η = (1−ρ)² (критическое демпфирование). -/
  eta : ℝ := (1 - rho) ^ 2
  /-- Максимум тернарных весов слоя: (2ε)² (из битовой границы). -/
  maxTrits : ℝ := (2 * eps) ^ 2

/-- Конфигурация по умолчанию: конструктор от (ρ, ε),
все поля вычислены. -/
def mkConfig (rho eps : ℝ) : OptimalConfig rho eps :=
  ⟨rho ^ 2, (1 - rho) ^ 2, (2 * eps) ^ 2⟩

/-- Momentum как функция цели: β(ρ) = ρ². -/
def cfgBeta (rho : ℝ) : ℝ := rho ^ 2

/-- Скорость обучения как функция цели: η(ρ) = (1−ρ)². -/
def cfgEta (rho : ℝ) : ℝ := (1 - rho) ^ 2

/-- Бюджет тернарных весов как функция допуска: N(ε) = (2ε)². -/
def cfgMaxTrits (eps : ℝ) : ℝ := (2 * eps) ^ 2

/-! ### 1. Скорость: momentum выводится из целевого ρ -/

/-- β = ρ² даёт фактический фактор сходимости критического
режима √β = ρ: целевая скорость ДОСТИГАЕТСЯ по построению. -/
theorem cfg_rate (rho : ℝ) (h0 : 0 < rho) :
    Real.sqrt (cfgBeta rho) = rho := by
  show Real.sqrt (rho ^ 2) = rho
  exact Real.sqrt_sq h0.le

/-! ### 2. Устойчивость: условия heavy-ball автоматны -/

/-- При 0 < ρ < 1 выведенные (β, η) = (ρ², (1−ρ)²) автоматически
удовлетворяют условиям hb_stability: 0 ≤ β < 1 и 0 < η ≤ 1−β.
Проверка η ≤ 1−β: (1−ρ)² ≤ 1−ρ² ⇔ 1−ρ ≤ 1+ρ. -/
theorem cfg_stability (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1) :
    0 ≤ cfgBeta rho ∧ cfgBeta rho < 1 ∧ 0 < cfgEta rho
      ∧ cfgEta rho ≤ 1 - cfgBeta rho := by
  unfold cfgBeta cfgEta
  refine ⟨sq_nonneg rho, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg rho, h0, h1]
  · have hp : 0 < 1 - rho := by linarith
    nlinarith [sq_nonneg (1 - rho), sq_nonneg rho, hp]
  · have hle : 1 - rho ≤ 1 + rho := by linarith
    have hnn : 0 ≤ 1 - rho := sub_nonneg.mpr h1.le
    have hkey : (1 - rho) ^ 2 ≤ (1 - rho) * (1 + rho) := by
      nlinarith
    have hfac : (1 - rho) * (1 + rho) = 1 - rho ^ 2 := by ring
    linarith

/-! ### 3. Спуск: скорость обучения η = (1−ρ)² автоматически
удовлетворяет условиям однозадачного градиентного шага -/

/-- Для одной задачи (T = 1) выведенная η = (1−ρ)² при 0<ρ<1
автоматно даёт строгий спуск энергии (условия 0 < η и
T·η < 2 теоремы taskStep_energy_descent выполнены без
подбора). -/
theorem cfg_descent {k : ℕ} (S : Hagi.Learning.TrainingTransition.TaskState k 1)
    (rho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (hgrad : ∑ j, Hagi.Learning.TrainingTransition.taskGrad S j ^ 2 ≠ 0) :
    Hagi.Learning.TrainingTransition.taskEnergy
      (Hagi.Learning.TrainingTransition.taskStep S (cfgEta rho))
      < Hagi.Learning.TrainingTransition.taskEnergy S := by
  have hρnn : 0 ≤ rho := by linarith
  have hη0 : 0 < 1 - rho := by linarith
  have hηpos : 0 < cfgEta rho := by
    unfold cfgEta
    nlinarith [sq_nonneg (1 - rho), hη0]
  have hη2 : (1:ℝ) * cfgEta rho < 2 := by
    have hρ1 : rho ≥ 0 ∧ rho ≤ 1 := ⟨hρnn, by linarith⟩
    have hsq : (1 - rho) ^ 2 ≤ 1 := by
      have hnn : 0 ≤ 1 - rho := by linarith
      have hle2 : 1 - rho ≤ 2 := by linarith
      nlinarith [sq_nonneg (1 - rho), hnn]
    unfold cfgEta
    norm_num
    linarith
  have hη2' : ((1:ℕ):ℝ) * cfgEta rho < 2 := by
    have := hη2
    push_cast at this ⊢
    linarith
  exact Hagi.Learning.TrainingTransition.taskStep_energy_descent S _
    hηpos hη2' hgrad

/-! ### 4. Объём: бюджет тернарных весов выводится из ε -/

/-- Обратная сторона ternary_bit_error_bound: слой с числом
весов m·r ≤ (2ε)² имеет ошибку квантования ≤ ε·‖x‖
(√(m·r)/2 ≤ ε ⇔ m·r ≤ 4ε²). Допуск на качество определяет
максимальный объём — компромисс объём↔качество замкнут. -/
theorem cfg_bits (m r : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hmr : (m:ℝ) * (r:ℝ) ≤ (2 * eps) ^ 2)
    (R QR : Matrix (Fin m) (Fin r) ℝ) (x : Fin r → ℝ)
    (hq : ∀ i j, abs (QR i j - R i j) ≤ 1/2) :
    Hagi.Learning.TernaryPert.outNorm
        (fun i => Hagi.Learning.TernaryPert.rowVec (QR - R) i ⬝ᵥ x)
      ≤ eps * Hagi.Learning.TernaryPert.eunorm x := by
  have h := Hagi.Learning.BitBudget.ternary_bit_error_bound R QR x hq
  have hb := Hagi.Learning.BitBudget.bitsPerTrit_pos
  have hmr2 : Hagi.Learning.BitBudget.layerBits m r
      / Hagi.Learning.BitBudget.bitsPerTrit = (m:ℝ) * (r:ℝ) := by
    unfold Hagi.Learning.BitBudget.layerBits
    field_simp
  have hkey : Real.sqrt ((m:ℝ) * (r:ℝ)) ≤ 2 * eps := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith [heps]
    · exact hmr
  have hhalf : Real.sqrt (Hagi.Learning.BitBudget.layerBits m r
      / Hagi.Learning.BitBudget.bitsPerTrit) / 2 ≤ eps := by
    rw [hmr2]
    have hs : 0 ≤ Real.sqrt ((m:ℝ) * (r:ℝ)) := Real.sqrt_nonneg _
    nlinarith [hkey]
  calc Hagi.Learning.TernaryPert.outNorm
        (fun i => Hagi.Learning.TernaryPert.rowVec (QR - R) i ⬝ᵥ x)
      ≤ (Real.sqrt (Hagi.Learning.BitBudget.layerBits m r
          / Hagi.Learning.BitBudget.bitsPerTrit) / 2)
          * Hagi.Learning.TernaryPert.eunorm x := h
    _ ≤ eps * Hagi.Learning.TernaryPert.eunorm x :=
        mul_le_mul_of_nonneg_right hhalf
          (Real.sqrt_nonneg _)


/-! ### 5. Регуляризация FOOF: λ выводится из целевой кривизны -/

/-- Регуляризация как функция цели: λ(μ) = μ — целевой порог
минимальной кривизны. Не подбирается: равен порогу. -/
def cfgLam (mu : ℝ) : ℝ := mu

/-- ВЫВОД λ: при λ = μ > 0 предобусловленная ковариация
C = XXᵀ + λI гарантирует кривизну vᵀCv ≥ μ·‖v‖² в ЛЮБОМ
направлении (ν-сильная выпуклость на спектральном пороге).
Следствия (уже доказаны): C обратим (regCov_det_unit —
посылка λ>0 стала теоремой), FOOF-шаг определён и единственен
(foofW_unique). Вместе с cfgEta/cfgBeta: НИ ОДИН числовой
параметр HAGI не подбирается. -/
theorem cfg_curvature (X : Matrix (Fin d) (Fin T) ℝ) (mu : ℝ)
    (hmu : 0 < mu) (v : Fin d → ℝ) :
    dotProduct v ((Hagi.Learning.FOOF.regCov X (cfgLam mu)).mulVec v)
      ≥ mu * (∑ j, v j ^ 2) := by
  rw [Hagi.Learning.RegCovPD.regCov_quad]
  have h1 : (0:ℝ) ≤ ∑ i, (∑ j, X j i * v j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold cfgLam
  linarith

end Hagi.Unified.OptimalConfig
