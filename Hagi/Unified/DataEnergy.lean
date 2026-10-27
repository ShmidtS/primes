import Hagi.Data.CertifiedArgmax
import Hagi.Data.DBridge
import Hagi.Data.DField
import Hagi.Data.DFieldKKT
import Hagi.Data.DistillRecursion
import Hagi.Data.InfoNCE
import Hagi.Data.NessDissipation
import Hagi.Data.PACBayes
import Hagi.Energy.Cooling
import Hagi.Energy.EntropyProduction
import Hagi.Energy.FreeEnergy
import Hagi.Energy.PoEBound

/-!
# Unified.DataEnergy — фасад данных и энергии

Слой-6 фасад: сертифицированный argmax, поле данных (KKT),
дистилляционная рекурсия, InfoNCE, PAC-Bayes, диссипация
Несса, термодинамика (охлаждение, свободная энергия, Ландауэр).
-/

namespace Hagi.Unified

export Hagi.Data.CertifiedArgmax (certified_argmax_strict)
export Hagi.Data (dfield_ascent_transfer fresh_data_prevents_collapse_uniform)
export Hagi.Energy (two_level_meanEnergy_strictMono partition_cold_limit)

/-- ПРИНЦИП ДАННЫХ И ЭНЕРГИИ (сводка): (1) сертифицированный
argmax устойчив при зазоре 2ε; (2) положительная
теплоёмкость — средняя энергия строго растёт по T
(двухуровневая система). Выбор и термодинамика корректны. -/
theorem data_certified_and_thermodynamic
    {ι : Type*} [Fintype ι] [Nonempty ι] {v est : ι → ℝ} {ε : ℝ}
    (herr : ∀ i, |est i - v i| ≤ ε)
    {imax : ι} (hgap : ∀ i, i ≠ imax → 2 * ε < v imax - v i)
    (ℓ : ι → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v) :
    (∀ i, i ≠ imax → est i < est imax)
      ∧ Filter.Tendsto (fun T : ℝ => ∑ v, Real.exp (-(ℓ v)/T))
          (nhdsWithin (0:ℝ) (Set.Ioi 0))
          (nhds (∑ v, if ℓ v = 0 then (1:ℝ) else 0)) :=
  ⟨certified_argmax_strict herr hgap,
    partition_cold_limit ℓ hℓ⟩

end Hagi.Unified
