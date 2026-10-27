import Hagi.Ensemble.MergeIdentity
import Hagi.Ensemble.MergeMixture
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.MergeScaling
import Hagi.Ensemble.CompressionCert
import Hagi.Ensemble.PolicyCompatibility
import Hagi.Ensemble.SigmaKernel
import Hagi.Ensemble.UniformCert

/-!
# Unified.EnsembleTheory — фасад теории ансамблей

Слой-6 фасад: слияние и маршрутизация — shift-инвариантность
softmax, точность смешанной продукции, квадратичная цена
слияния, sigma-ядро, совместимость политик.
-/

open Matrix Finset

namespace Hagi.Unified

export Hagi.Ensemble (softmax_shift_invariance
  geometric_mean_logit_mean merged_output_exact routing_drift_bound
  merge_price_quad uniform_good_mass integration_net_gain_pos)

/-- ПРИНЦИП СЛИЯНИЯ (сводка): (1) softmax-маршрутизация
инвариантна к сдвигу логитов (выбор не зависит от калибровки);
(2) смешанная продукция точна (линейность по построению). -/
theorem merge_calibrated_and_exact {V : Type} [Fintype V]
    (z : V → ℝ) (c : ℝ) {m d : ℕ} (w : Fin m → ℝ)
    (x : Fin d → ℝ)
    {W : Fin m → Matrix (Fin d) (Fin d) ℝ} :
    (fun v => Real.exp (z v + c) / ∑ u, Real.exp (z u + c))
      = (fun v => Real.exp (z v) / ∑ u, Real.exp (z u))
      ∧ (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) :=
  ⟨Hagi.Ensemble.softmax_shift_invariance V z c,
    merged_output_exact W w x⟩

end Hagi.Unified
