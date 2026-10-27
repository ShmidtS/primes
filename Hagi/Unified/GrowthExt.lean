import Hagi.Growth.ChainUnification
import Hagi.Growth.NoiseDisentangle
import Hagi.Growth.NonlinearCone
import Hagi.Growth.PlasticityLedger
import Hagi.Growth.RecursiveSelfDevelopment
import Hagi.Growth.RoundViability
import Hagi.Growth.RsiCriterion
import Hagi.Growth.SeedOnly
import Hagi.Growth.T3Ignition
import Hagi.Growth.Thermostat

/-!
# Unified.GrowthExt — фасад расширений роста

Слой-6 фасад: обновление возможностей (self-development),
затухание посевного цикла, нелинейный конус, пластичность,
термостат, T3-зажигание.
-/

namespace Hagi.Unified

export Hagi.Growth (opportunity_renewal cycle_decay_mono
  round_exhausted thermostat_stop kl_le_log_card
  training_core_is_measurement_tail orthogonal_noise_averaging)

/-- САМОРАЗВИТИЕ (сводка): (1) при конусной динамике с полом
возможностей фронт строго растёт (D + ΔO ≤ D'); (2)
посевной капитал затухает монотонно, оставаясь
неотрицательным. Саморазвитие возобновляет ресурс и не
истощает посев. -/
theorem growth_renews_and_seed_survives
    (D D' C rho beta xi deltaO : ℝ)
    (hdyn : rho * D + beta * C - xi ≤ D')
    (hfloor : (1 - rho) * D + deltaO ≤ beta * C - xi)
    (F k s : ℝ) (hs : 0 ≤ s) (hF : 0 < F)
    (hk : 0 < k) (hklt : k < F + s) :
    D + deltaO ≤ D'
      ∧ F * (1 - k/(F + s)) < F
        ∧ 0 ≤ F * (1 - k/(F + s)) :=
  ⟨opportunity_renewal D D' C rho beta xi deltaO hdyn hfloor,
    cycle_decay_mono F k s hs hF hk hklt⟩

end Hagi.Unified
