import Mathlib.Tactic
import Hagi.Learning.RCDL
import Hagi.Learning.HadamardProjectors

set_option maxHeartbeats 1000000 in

set_option linter.style.header false

/-!
# HRCN — Hybrid Retrieval-Cortex Network слой (исследовательский цикл 8)

Композиция синтеза RCDL+HAGI:
y(x) = W_base x + Σ_m P_m (s_{D_m}(x)).

Главные теоремы (чистые, без эмпирики):
- `domainTerm_gauge_shift`: gauge-сдвиг базы значений домена w
  меняет его вклад ровно на P_w(b);
- `hrcn_cross_talk_zero`: этот сдвиг-gauge-эффект домена w имеет
  НУЛЕВУЮ проекцию на характер любого другого домена u ≠ w —
  формальная гарантия отсутствия катастрофической
  интерференции доменов памяти HRCN.
-/

open Finset

namespace Hagi.Learning.HRCN

open Hagi.Learning.RCDL Hagi.Learning.HadamardProjectors

variable {k N : ℕ}

/-- Вклад домена w: проектор характера, применённый к
взвешенному софтмаксу базы. -/
noncomputable def domainTerm (w : Fin k → ZMod 2)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  charProjR w (weightedSoftmax ks ws vs q)

/-- Gauge-эффект домена w — ровно проекция сдвига. -/
theorem domainTerm_gauge_shift (w : Fin k → ZMod 2)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) (b : (Fin k → ZMod 2) → ℝ)
    (hden : (∑ i, expw (ks i) q * ws i) ≠ 0) :
    domainTerm w ks ws (fun i => vs i + ws i • b) q
      = domainTerm w ks ws vs q + charProjR w b := by
  unfold domainTerm
  change charProjR w (weightedSoftmax ks ws (fun i => vs i + ws i • b) q)
      = charProjR w (weightedSoftmax ks ws vs q) + charProjR w b
  rw [gauge_shift (ι := Fin k → ZMod 2) ks ws vs q b hden,
    charProjR_add]

/-- НУЛЕВОЙ CROSS-TALK: gauge-эффект домена w ортогонален
характеру любого другого домена u ≠ w. -/
theorem hrcn_cross_talk_zero {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) (b : (Fin k → ZMod 2) → ℝ)
    (hden : (∑ i, expw (ks i) q * ws i) ≠ 0) :
    charProjR u (domainTerm w ks ws (fun i => vs i + ws i • b) q
      - domainTerm w ks ws vs q) = 0 := by
  rw [domainTerm_gauge_shift w ks ws vs q b hden]
  have h1 : charProjR u (domainTerm w ks ws vs q
      + charProjR w b - domainTerm w ks ws vs q)
      = charProjR u (charProjR w b) := by
    congr 1
    rw [add_comm (domainTerm w ks ws vs q) (charProjR w b), add_sub_cancel_right]
  rw [h1]
  exact charProjR_orthog (Ne.symm hwu) b

end Hagi.Learning.HRCN
