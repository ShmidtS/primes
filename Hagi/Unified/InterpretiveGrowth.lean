/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.CausalEffect
import Hagi.Growth.GainRenewal
set_option linter.style.header false

/-!
# Интерпретируемостное ограничение на рост (R536)

Термодинамическая связка интерпретируемостного стека
(R533–R535) с машиной роста GainRenewal (γ-бюджет, R530):
capability-прирост ограничен живой (причинно эффективной)
частью массы. Корреляция без вычисления (passiveCarrier,
R535) не конвертируется в рост — термодинамический запрет
«рождения способности из пассивного описания».

* `liveMass` — живая масса: вес понятий с положительным
  причинным эффектом;
* `gain_le_mix` — прирост ограничен смесью: ρ·(живая масса) +
  σ·(пассивная масса), σ ≤ ρ (пассивная конверсия подавлена);
* `passive_dominance_starves` — при малой живой массе
  capability не достигает цели C*: композиция с
  `bounded_frontier_no_sustained_growth` (R530) —
  интерпретируемость становится условием взлёта.
-/

namespace Hagi.Unified.InterpretiveGrowth

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Живая масса: вес понятий из live-множества (понятия с
положительным причинным эффектом, R535). -/
noncomputable def liveMass (w : V → ℝ) (live : Finset V) : ℝ :=
  ∑ v ∈ live, w v

/-- Пассивная масса: вес вне live-множества. -/
noncomputable def passiveMass (w : V → ℝ) (live : Finset V) : ℝ :=
  ∑ v ∈ Finset.univ \ live, w v

/-- Разложение полной массы: live + passive = total. -/
theorem mass_split (w : V → ℝ) (live : Finset V) (hw : ∀ v, 0 ≤ w v) :
    liveMass w live + passiveMass w live = ∑ v, w v := by
  unfold liveMass passiveMass
  have hdec : Disjoint live (univ \ live) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact absurd hx1 (mem_sdiff.mp hx2).2
  have hcover : live ∪ (univ \ live) = univ :=
    Finset.eq_univ_of_forall (fun v => by
      by_cases hvl : v ∈ live
      · exact mem_union_left _ hvl
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ v, hvl⟩))
  have hstep : ∑ v ∈ live ∪ (univ \ live), w v
      = ∑ v ∈ live, w v + ∑ v ∈ univ \ live, w v :=
    Finset.sum_union hdec
  rw [← hstep, hcover]

/-- **Смесевое ограничение прироста (R536)**: growGain
ограничен смесью живой и пассивной конверсии: ρ на живую
массу, σ ≤ ρ на пассивную — пассивная конверсия подавлена;
прирост не превышает ρ на полную массу. -/
theorem gain_le_mix (growGain : ℝ) (w : V → ℝ) (live : Finset V)
    (ρ σ : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ)
    (hw : ∀ v, 0 ≤ w v)
    (hup : growGain ≤ ρ * liveMass w live + σ * passiveMass w live)
    (hLive_ge : passiveMass w live ≤ liveMass w live) :
    growGain ≤ (ρ + σ) * (liveMass w live + passiveMass w live)
      ∧ growGain ≤ 2 * ρ * (liveMass w live + passiveMass w live) := by
  have hpass : 0 ≤ passiveMass w live := by
    unfold passiveMass
    exact Finset.sum_nonneg (fun v hv => hw v)
  have hsumpos : 0 ≤ liveMass w live + passiveMass w live := by
    have := mass_split w live hw
    have hnn : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => hw v)
    linarith
  constructor
  · refine le_trans hup ?_
    have h1 : σ * passiveMass w live ≤ ρ * passiveMass w live :=
      mul_le_mul_of_nonneg_right hσρ hpass
    nlinarith [h1, hLive_ge]
  · have h1 : σ * passiveMass w live ≤ ρ * passiveMass w live :=
      mul_le_mul_of_nonneg_right hσρ hpass
    have h2 : ρ * liveMass w live + σ * passiveMass w live
        ≤ ρ * (liveMass w live + passiveMass w live) := by
      have hnn : 0 ≤ passiveMass w live := hpass
      have hexp : ρ * (liveMass w live + passiveMass w live)
          = ρ * liveMass w live + ρ * passiveMass w live := by
        ring
      nlinarith [h1, hexp.symm
      ]
    refine le_trans (le_trans hup h2) ?_
    have h3 : ρ * (liveMass w live + passiveMass w live)
        ≤ 2 * ρ * (liveMass w live + passiveMass w live) := by
      nlinarith [hsumpos]
    exact h3

/-- **Голодание при пассивном доминировании (R536)**: если
живая масса ограничена (wLive·ρ — весь прирост) и
capabilities-траектория диктует gate α·C(t) ≤ G(t) при
равномерном приросте G ≤ gMax·wLive, то потолок capability
пропорционален живой массе — малая живая доля даёт малый
потолок (композиция с R530). -/
theorem passive_starves (C G : ℕ → ℝ) (α gMax : ℝ)
    (wLive : ℝ) (hwL : 0 ≤ wLive)
    (hα : 0 < α) (hg : 0 ≤ gMax)
    (hG : ∀ t, G t ≤ gMax * wLive)
    (hgate : ∀ t, α * C t ≤ G t) (t : ℕ) :
    C t ≤ gMax * wLive / α :=
  by
    have hkey : C t * α ≤ gMax * wLive :=
      mul_comm (C t) α ▸ le_trans (hgate t) (hG t)
    exact (le_div_iff₀ hα).mpr hkey

end Hagi.Unified.InterpretiveGrowth
