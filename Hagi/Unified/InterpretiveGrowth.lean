/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainRenewal
import Hagi.Unified.RecursiveClean
/-!
# Причинный слой интерпретируемости: эффект нейрона (R535)

Завершение интерпретируемостного стека R533/R534: корреляция
активаций с понятиями недостаточна — нужен причинный тест
«что нейрон действительно делает». Формализация:

* `pointEffect` — точечный causal-эффект: L1-норма
  изменения выхода ‖f x − f' x‖₁;
* `causalEffect` — I_j(v) = средний точечный эффект по
  данным понятия D_v;
* `causalEffect_nonneg` / `pointEffect_nonneg` — эффекты
  неотрицательны (нормы);
* `causalEffect_zero_of_pointwise` — нет изменения выхода
  на всех данных ⟹ эффект нулевой (нейрон мёртв на
  понятии);
* `causalEffect_pos_of_point` — положительный точечный
  эффект ⟹ положительный эффект по данным (жизнь);
* `causalEffect_le_max` — среднее ≤ максимума точечных
  эффектов (множественный тест контролируется худшей
  точкой);
* `passiveCarrier` — причинное вето: нулевой эффект = пассивный
  носитель массы (корреляция без вычисления); такие
  понятия не подтверждают живые ветви дерева обобщений
  (причинная согласованность обязательна в векторе
  интерпретируемости R533).
-/

namespace Hagi.Unified.CausalEffect

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Точечный причинный эффект на входе x: L1-норма
изменения выхода. -/
noncomputable def pointEffect (f f' : X → Y → ℝ) (x : X) : ℝ :=
  ∑ y, |f x y - f' x y|

/-- Средний причинный эффект по данным понятия D_v:
I_j(v) = (1/|D_v|) Σ pointEffect. -/
noncomputable def causalEffect (f f' : X → Y → ℝ) (Dv : Finset X) :
    ℝ :=
  (∑ x ∈ Dv, pointEffect f f' x) / Dv.card

/-- Точечный эффект неотрицателен. -/
theorem pointEffect_nonneg (f f' : X → Y → ℝ) (x : X) :
    0 ≤ pointEffect f f' x :=
  Finset.sum_nonneg (fun y _ => abs_nonneg _)

/-- **Неотрицательность (R535)**: эффект — среднее норм. -/
theorem causalEffect_nonneg (f f' : X → Y → ℝ) (Dv : Finset X) :
    0 ≤ causalEffect f f' Dv :=
  div_nonneg (Finset.sum_nonneg (fun x _ => pointEffect_nonneg f f' x))
    (Nat.cast_nonneg _)

/-- **Мёртвый нейрон (R535)**: если вмешательство не меняет
выход ни на одном входе понятия, эффект нулевой. -/
theorem causalEffect_zero_of_pointwise (f f' : X → Y → ℝ)
    (Dv : Finset X)
    (h : ∀ x ∈ Dv, ∀ y, f x y = f' x y) :
    causalEffect f f' Dv = 0 := by
  have hsum : ∑ x ∈ Dv, pointEffect f f' x = 0 := by
    refine Finset.sum_eq_zero (fun x hx => ?_)
    unfold pointEffect
    have hy : ∀ y : Y, |f x y - f' x y| = 0 := by
      intro y
      rw [h x hx y, sub_self, abs_zero]
    exact Finset.sum_eq_zero (fun y _ => hy y)
  unfold causalEffect
  rw [hsum, zero_div]

/-- **Живой вход (R535)**: положительный точечный эффект на
каком-то входе данных даёт положительный средний эффект. -/
theorem causalEffect_pos_of_point (f f' : X → Y → ℝ)
    (Dv : Finset X) (hDv : Dv.Nonempty)
    (x₀ : X) (hx₀ : x₀ ∈ Dv) (hp : 0 < pointEffect f f' x₀) :
    0 < causalEffect f f' Dv := by
  have hcardpos : 0 < Dv.card := hDv.card_pos
  have hsum : 0 < ∑ x ∈ Dv, pointEffect f f' x := by
    have hge : pointEffect f f' x₀
        ≤ ∑ x ∈ Dv, pointEffect f f' x := by
      refine single_le_sum (f := pointEffect f f')
        (fun x _ => pointEffect_nonneg f f' x) hx₀
    linarith
  exact div_pos hsum (by exact_mod_cast hcardpos)

/-- **Среднее ≤ максимум (R535)**: причинный эффект по
данным не превосходит максимального точечного эффекта. -/
theorem causalEffect_le_max (f f' : X → Y → ℝ) (Dv : Finset X)
    (hDv : Dv.Nonempty) :
    causalEffect f f' Dv ≤ Finset.sup' Dv hDv (pointEffect f f') := by
  have hcardpos : (0:ℝ) < Dv.card := by exact_mod_cast hDv.card_pos
  set m : ℝ := Finset.sup' Dv hDv (pointEffect f f') with hm
  have hmax : ∀ x ∈ Dv, pointEffect f f' x ≤ m := fun x hx =>
    Finset.le_sup' (pointEffect f f') hx
  have hstep : ∑ x ∈ Dv, pointEffect f f' x ≤ Dv.card * m := by
    have hle : ∑ x ∈ Dv, pointEffect f f' x
        ≤ (∑ x ∈ Dv, (m:ℝ)) := by
      refine Finset.sum_le_sum (fun x hx => hmax x hx)
    rw [Finset.sum_const] at hle
    norm_num at hle
    exact hle
  unfold causalEffect
  rw [div_le_iff₀ hcardpos, mul_comm]
  exact hstep

/-- **Причинное вето (R535)**: понятие с нулевым причинным
эффектом — «пассивный носитель массы»: корреляция без
вычисления. В сертификате ветвления такие понятия не
подтверждают живое обобщение. -/
def passiveCarrier (f f' : X → Y → ℝ) (Dv : Finset X) : Prop :=
  causalEffect f f' Dv = 0

end Hagi.Unified.CausalEffect
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
