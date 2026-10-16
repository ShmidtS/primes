/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Unified.RecursiveClean
set_option linter.style.header false

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
