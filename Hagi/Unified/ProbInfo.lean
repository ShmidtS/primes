import Hagi.Information.GainRecoverability
import Hagi.Information.RoutingCapacity
import Hagi.Probability.ExpChord
import Hagi.Probability.NoiseTemperature
import Hagi.Probability.PMFBridge
import Hagi.Probability.SphericalAngle
import Hagi.Probability.StationaryFlatness
import Hagi.Probability.ThermoAxes
import Hagi.Probability.ThermoBridge
import Hagi.Probability.WSqD

/-!
# Unified.ProbInfo — фасад вероятностно-информационного блока

Слой-6 фасад: восстановимость усиления, маршрутизационная
ёмкость, экспоненциальная хорда, ось шума/температуры,
мосты ПМФ/термодинамики.
-/

namespace Hagi.Unified

export Hagi.Information (no_free_recovery devEnergyF_pos_iff)
export Hagi.Probability (noise_axes_coincide prodE_as_expQ
  tail_sum_identity)

/-- ПРИНЦИП ИНФОРМАЦИИ (сводка): (1) бесплатного
восстановления нет — хорошая пара encode/decode на одном
слове даёт witnesses-код; (2) энергия девиации строго
положительна ⟺ девиация ненулевая (обнаружимость).
Информация измерима и не бесплатна. -/
theorem info_not_free_and_detectable
    {A Q : Type} (encode : A → Q)
    (decode : Q → A) (good : A → A → Prop) (w : A)
    (h : good (decode (encode w)) w)
    {N d : ℕ} (dev : Fin N → Fin d → ℝ) :
    (∃ q : Q, good (decode q) w)
      ∧ (0 < Hagi.Information.devEnergyF dev
          ↔ ∃ k : Fin N, dev k ≠ 0) :=
  ⟨no_free_recovery encode decode good w h,
    devEnergyF_pos_iff dev⟩

end Hagi.Unified
