import Hagi.Unified.TopLevel
import Hagi.Foundations.PerronCone

/-!
# Unified.QuantizedCone — склейка (e) аудита v5

Квантизация внутри конусного инварианта: выигрыш роста
проходит через квантованные веса; штраф квантования
(quant_energy_bridge: dE ≤ κ·√n·s/2) вычитается из чистого
выигрыша. Конус γ·k·C ≤ G сохраняется при margin-условии:
штраф ≤ γ·(D − k·C) — избыток фронтира над конусом.
-/

namespace Hagi.Unified

/-- НИЖНЯЯ ГРАНИЦА ЧИСТОГО ВЫИГРЫША после квантования:
γ·D ≤ Graw и штраф Graw − G ≤ p дают γ·D − p ≤ G. -/
theorem quantized_net_gain (gamma D Graw G p : ℝ)
    (hgain : gamma * D ≤ Graw) (hquant : Graw - G ≤ p) :
    gamma * D - p ≤ G := by linarith

/-- КОНУС ПРИ КВАНТИЗАЦИИ: если конус k·C ≤ D выполнен и
штраф квантования p поглощается избытком фронтира
(p ≤ γ·(D − k·C)), то конусное условие усиления
γ·k·C ≤ G сохраняется НА КВАНТОВАННОМ шаге. -/
theorem quantized_cone_gain (gamma k C D Graw G p : ℝ)
    (hcone : k * C ≤ D) (hnn : 0 ≤ gamma)
    (hgain : gamma * D ≤ Graw) (hquant : Graw - G ≤ p)
    (hmargin : p ≤ gamma * (D - k * C)) :
    gamma * k * C ≤ G := by
  have h1 : gamma * k * C ≤ gamma * D := by
    have := mul_le_mul_of_nonneg_left hcone hnn
    ring_nf at this ⊢
    exact this
  have h2 : gamma * D - p ≤ G := quantized_net_gain gamma D Graw G p
    hgain hquant
  have hsub : gamma * (D - k * C)
      = gamma * D - gamma * k * C := by ring
  rw [hsub] at hmargin
  ring_nf at h1 h2 hmargin ⊢
  linarith

end Hagi.Unified
