import Hagi.Architecture.AlignedMerge
import Hagi.Architecture.ConfigurationCost
import Hagi.Architecture.ConfigurationRouting
import Hagi.Architecture.CortexFiber
import Hagi.Architecture.FactorRank
import Hagi.Architecture.FactorizedMerge
import Hagi.Architecture.Heterarchy
import Hagi.Architecture.LiveDelta
import Hagi.Architecture.OrthoInjection
import Hagi.Architecture.ResidualSplit

/-!
# Unified.ArchitectureCore — фасад архитектурного блока

Слой-6 фасад: архитектурные принципы HAGI — ортогональные
волокна (нет взаимных помех), конфигурационная экономия
(разреженная маршрутизация дешевле плотной), гетерархичность
(нет глобального ранжирования модулей).
-/

open Finset Matrix

namespace Hagi.Unified

export Hagi.Architecture (fiberSplitOrtho fiberActionNoInterference
  config_storage_beats_dense no_global_ranking cycle_breaks_ranking
  routed_eval_exact orthoNorm)

/-- АРХИТЕКТУРНЫЙ ПРИНЦИП (сводка): (1) ортогональная
инъекция не создаёт помех — проекция исчерпывает действие
(fiberSplitOrtho); (2) конфигурация r≪d экономит память
строго (config_storage_beats_dense). Архитектура HAGI
одновременно инвариантна (волокна) и экономна. -/
theorem architecture_invariant_and_economical
    {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : Hagi.Architecture.IsOrthoCol U) (A : Matrix (Fin d) (Fin r) ℝ)
    (dd nn : ℕ) (h : nn * r < dd) (hd : 0 < dd) :
    Uᵀ * (A - U * (Uᵀ * A)) = 0
      ∧ (nn * r) * dd < dd * dd :=
  ⟨fiberSplitOrtho U hU A,
    config_storage_beats_dense dd r nn h hd⟩

end Hagi.Unified
