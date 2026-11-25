import Hagi.Theory.NegativeTransfer
import Hagi.Theory.FunctionPreservingGrowth
import Hagi.Theory.GrowSnap
import Hagi.Theory.CoverageReading

/-!
# DerivedConfig — выводимая конфигурация обучения (C683)

Сборка доказанных оптимумов в одну структуру. Каждый компонент
`optimalConfig` подставляется в СУЩЕСТВУЮЩУЮ теорему напрямую
(переформулировки нет — Freeze identity). Числовые входы и
сравнение с кодом hagi @ca52eb4 — `scripts/derive_config.py` и
`docs/DERIVED-CONFIG.md`.

* `TrainingConfig`, `optimalConfig`, `optimalConfig_spec`.
-/

namespace Hagi.Theory.DerivedConfig

open scoped BigOperators
open Classical in
/-- `w` — оптимальная вещественная ширина окна. -/
structure TrainingConfig where
  γ : ℝ
  η : ℝ
  snapK : ℕ
  w : ℝ
  deriving Inhabited

open Classical in
/-- Формулы: γ* = 1/L, η* = −4a/R² (a < 0 — residual-сигнал),
k* = ⌈log₂(L·d/ε)⌉ − 1, w* = √(a/c). Буква `a` в `w` — стоимость
окна (НЕ residual-сигнал `a` в `η`), у теорем имена свои. -/
noncomputable def optimalConfig (L _G a R d ε ac c : ℝ) : TrainingConfig :=
  { γ := 1 / L
    , η := -4 * a / R ^ 2
    , snapK := Nat.ceil (Real.logb 2 (L * d / ε)) - 1
    , w := Real.sqrt (ac / c) }

open Classical in
/-- Каждый компонент — оптимум по своей теореме: drop максимален
(`nlDrop_le_optimal`), парабола `linDrop` в максимуме
(`useful_first_step`), certified err ≤ ε и минимальность
(`snap_k_eq_ceil` + `snap_k_min`), стоимость окна в минимуме
(`mixedCost_lower`: total-cost ≥ 2n√(a·c), равенство при w = w*). -/
theorem optimalConfig_spec {L G a R d ε ac c : ℝ}
    (hL : 0 < L) (hR : R ≠ 0) (hε : 0 < ε) (hLd : ε < L * d)
    (hac : 0 < ac) (hc : 0 < c) (n w : ℕ) (hw : 0 < w) :
    (∀ γ : ℝ, Hagi.Theory.NegativeTransfer.nlDrop γ L G
        ≤ Hagi.Theory.NegativeTransfer.nlDrop (optimalConfig L G a R d ε ac c).γ L G)
    ∧ Hagi.Theory.FunctionPreservingGrowth.linDrop a R
        (optimalConfig L G a R d ε ac c).η = 2 * a ^ 2 / R ^ 2
    ∧ (L * d * (2:ℝ)
          ^ (-(((optimalConfig L G a R d ε ac c).snapK : ℕ) : ℝ) - 1) ≤ ε
        ∧ (Hagi.Theory.GrowSnap.snapAdmissible L d ε w →
          (optimalConfig L G a R d ε ac c).snapK ≤ w))
    ∧ 2 * (n : ℝ) * Real.sqrt (ac * c)
        ≤ ((n + w - 1) / w : ℕ) * (ac + c * (w : ℝ) ^ 2) := by
  have hLd0 : (0:ℝ) ≤ L * d := by linarith
  have hsnap : (optimalConfig L G a R d ε ac c).snapK
      = Hagi.Theory.GrowSnap.snapK L d ε hε hLd0 := by
    simp only [optimalConfig]
    exact (Hagi.Theory.GrowSnap.snap_k_eq_ceil L d ε hε hLd).symm
  refine ⟨fun γ => Hagi.Theory.NegativeTransfer.nlDrop_le_optimal L G γ hL,
    Hagi.Theory.FunctionPreservingGrowth.useful_first_step (a := a) hR, ?_,
    Hagi.Theory.WindowTradeoff.mixedCost_lower hac hc hw⟩
  · refine ⟨by
      rw [hsnap]
      exact (Hagi.Theory.GrowSnap.snap_admissible_iff L d ε hε _).mp
        (Hagi.Theory.GrowSnap.snap_k_admissible L d ε hε hLd0), fun hk => ?_⟩
    rw [hsnap]
    exact Hagi.Theory.GrowSnap.snap_k_min L d ε hε hLd0 w hk

end Hagi.Theory.DerivedConfig
