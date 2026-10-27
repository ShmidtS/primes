import Hagi.Model.CycleCertificate
import Hagi.Model.HypothesisCompetition
import Hagi.Model.MemoryConsolidation
import Hagi.Model.MoeExpansion
import Hagi.Model.Sidon
import Hagi.Model.SoftmaxStep
import Hagi.Pretraining.Dust
import Hagi.Pretraining.DustAlign
import Hagi.Pretraining.ProbeError
import Hagi.Pretraining.Speedrun
import Hagi.Pretraining.SyntheticPretrain
import Hagi.Pretraining.TrustRegion
import Hagi.Energy.PreNorm
import Hagi.Energy.STEStep

/-!
# Unified.ModelPretrain — фасад модели и предобучения

Слой-6 фасад: сертификаты цикла, конкуренция гипотез,
консолидация памяти, MoE-расширение, сидон-множества;
пылевые оценки, зонное выравнивание, синтетическое
предобучение, trust region.
-/

namespace Hagi.Unified

export Hagi.Model (consolidation_bits_cap cycle_certificate_composition)
export Hagi.Pretraining (time_to_capability_correct)

/-- ПАМЯТЬ И ВРЕМЯ (сводка): (1) консолидация ограничена
битами записи (F ≤ B/cUnit); (2) время до capability
корректно определено (первый достижимый момент, монотонный
хвост). Ресурсы и горизонты согласованы. -/
theorem memory_capped_and_time_correct
    (B cUnit F : ℝ) (hcUnit : 0 < cUnit)
    (h_emp_memwrite : cUnit * F ≤ B)
    (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n)
    (hmono : ∀ t, C t ≤ C (t + 1)) :
    F ≤ B / cUnit
      ∧ τ ≤ C (Hagi.Pretraining.TimeToCapability τ C hreach)
        ∧ (∀ k < Hagi.Pretraining.TimeToCapability τ C hreach, C k < τ) :=
  ⟨consolidation_bits_cap B cUnit F hcUnit h_emp_memwrite,
    (time_to_capability_correct τ C hreach hmono).1,
    (time_to_capability_correct τ C hreach hmono).2.1⟩

end Hagi.Unified
