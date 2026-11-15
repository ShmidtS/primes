/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Learning.SoftRouterMix
import Hagi.Optimization.MirrorHedgeSurvivor

set_option linter.style.header false

/-!
# SoftRouterTotal — сквозной regret-бандл мягкого роутера (цикл 20)

Композиция C320: `soft_router_ce_bound` (C319, по-раундовая
калибровка смеси логитов) + регрет-носитель Hedge
(`Hagi.Optimization.MirrorHedgeRouting.router_regret_bound` с
выведенной посылкой выживания `Hagi.Optimization.MirrorHedgeSurvivor.
hsurv_derived`). Итог — `soft_router_total_bound`: за T раундов
мягкий роутинг с Hedge-весами wᵗ = ewNorm CE-потерь конкурентен
ЛЮБОМУ одиночному эксперту в ретроспективе (total mixture CE ≤
best-expert total CE + log N/η + η·T/2), причём калиброванный CE
гарантирован на КАЖДОМ шаге (C319). Новая математики нет — только
суммирование-склейка; обе стороны процитированы.

Challenge-pins (честные границы, все три в докстрингах):

* ИДЕНТИФИКАЦИЯ ПОТЕРЬ: Hedge-носитель (`hedge_step`) требует
  потерь экспертов в [0, 1]. CE ≥ 0 всегда (кирпич
  `ceOneHot_nonneg`: lse z ≥ z t, сумма exp доминирует целевой
  член), но CE ≤ 1 — РЕАЛЬНАЯ посылка (режим exact-expert
  abstention: эксперты с CE > 1 — уверенно неверные уровня wz2 —
  исключены; для них нужен масштабированный η, не заявлено).
* ИНДЕКС ЭКСПЕРТОВ: носитель `ewNorm` фиксирован во вселенной
  `Type` 0, а C319 индексирует экспертов `Fin N` — композиция
  заявлена на `Fin N` с `[Nonempty (Fin N)]`, оба носителя
  применяются дословно.
* GUARD / SLEEPING EXPERTS: у носителя Hedge НЕТ механизма
  спящих экспертов (веса обновляются по всем экспертам каждый
  раунд). Честная версия: бандл верен относительно ЛЮБОГО
  одиночного эксперта i (параметрически) — в частности любого
  guard-доступного; анти-лок-ин носителя
  (`ewNorm_survivor_lower`) не даёт роутеру навсегда shut out
  эксперта. Regret относительно лучшей ПОСЛЕДОВАТЕЛЬНОСТИ
  доступных экспертов (настоящий sleeping-experts regret) НЕ
  заявлен — gap зафиксирован.

Honest scope: без drift/адаптивности (логиты и метки —
адверсариальные последовательности), константа регрета ровно как
у носителя (log N/η + η·T/2), без подобранного η. Якорь
`total_bound_anchor`: 2 эксперта, 3 раунда, η = 1/2 — числовая
проверка композиции (веса раунда 0 равномерны 1/2, 1/2, смесь
строго положительного CE; итог < 4·L + 3 при L = log(1+e⁻²)).
-/

namespace Hagi.Learning.SoftRouterTotal

open Hagi.Core Hagi.Learning.SoftRouterMix Hagi.Autonomy

/-- CE неотрицателен: lse z ≥ z t, ибо сумма exp содержит целевой
член (нужен как посылка 0 ≤ l для Hedge-носителя). -/ 
theorem ceOneHot_nonneg {k : Type*} [Fintype k] [Nonempty k]
    (t : k) (z : k → ℝ) : 0 ≤ ceOneHot t z := by
  unfold ceOneHot lse
  have h1 : Real.exp (z t) ≤ ∑ v, Real.exp (z v) :=
    Finset.single_le_sum (f := fun v => Real.exp (z v))
      (fun v _ => Real.exp_nonneg _) (Finset.mem_univ t)
  have h2 : Real.log (Real.exp (z t)) ≤ Real.log (∑ v, Real.exp (z v)) :=
    Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  linarith

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ C320 — сквозной бандл: за T раундов с
Hedge-весами wᵗ = ewNorm CE-потерь (η ∈ (0,1]) и посылкой CE ≤ 1
(exact-expert abstention) суммарный CE мягкой смеси не превосходит
суммарный CE ЛЮБОГО одиночного эксперта плюс константу регрета
носителя log N/η + η·T/2. Композиция: по-раундовая калибровка
`soft_router_ce_bound` (C319) + агрегация `hsurv_derived` +
`router_regret_bound` (Hedge-носитель); новые факты — только
неотрицательность CE и суммирование. Эксперты — `Fin N` (вселенная
носителя Type 0, C319 индексирует Fin N); sleeping-experts regret не
заявлен (см. докстринг модуля). -/ 
theorem soft_router_total_bound {k : Type*} [Fintype k] [Nonempty k]
    {N : ℕ} [Nonempty (Fin N)]
    (eta : ℝ) (heta : 0 < eta ∧ eta ≤ 1) (T : ℕ)
    (lab : ℕ → k) (z : ℕ → Fin N → k → ℝ)
    (hce : ∀ t ∈ Finset.range T, ∀ i, ceOneHot (lab t) (z t i) ≤ 1)
    (i : Fin N) :
    ∑ t ∈ Finset.range T, ceOneHot (lab t)
        (fun v => ∑ j, ewNorm (fun t j => ceOneHot (lab t) (z t j)) eta t j
          * z t j v)
      ≤ ∑ t ∈ Finset.range T, ceOneHot (lab t) (z t i)
        + Real.log (Fintype.card (Fin N)) / eta + eta * T / 2 := by
  set l : ℕ → Fin N → ℝ := fun t j => ceOneHot (lab t) (z t j) with hll
  have hl : ∀ t ∈ Finset.range T, ∀ j, 0 ≤ l t j ∧ l t j ≤ 1 := by
    intro t ht j
    exact ⟨ceOneHot_nonneg (lab t) (z t j), hce t ht j⟩
  -- по-раундовая калибровочная склейка (C319)
  have hround : ∀ t ∈ Finset.range T,
      ceOneHot (lab t) (fun v => ∑ j, ewNorm l eta t j * z t j v)
        ≤ ∑ j, ewNorm l eta t j * l t j := by
    intro t _
    exact soft_router_ce_bound (lab t) (ewNorm l eta t)
      (ewNorm_nonneg l eta t) (ewNorm_sum l eta t) (z t)
  -- суммарный CE смеси ≤ потери алгоритма A
  have hA : ∑ t ∈ Finset.range T, ceOneHot (lab t)
      (fun v => ∑ j, ewNorm l eta t j * z t j v)
      ≤ ∑ t ∈ Finset.range T, ∑ j, ewNorm l eta t j * l t j :=
    Finset.sum_le_sum fun t ht => hround t ht
  -- регрет-носитель (hsurv_derived + router_regret_bound)
  have hsurv := hsurv_derived l eta T i
    (fun t ht j => hl t (Finset.mem_range.mpr ht) j) ⟨heta.1.le, heta.2⟩
  have hrrb := router_regret_bound (Fintype.card (Fin N)) T eta
    (∑ t ∈ Finset.range T, ∑ j, ewNorm l eta t j * l t j)
    (∑ t ∈ Finset.range T, l t i) (Fintype.card_pos) heta.1 hsurv
  have hkey : (∑ t ∈ Finset.range T, ∑ j, ewNorm l eta t j * l t j)
      - (∑ t ∈ Finset.range T, l t i) ≤ Real.log (Fintype.card (Fin N))
      / eta + eta * T / 2 := hrrb
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by
    simp [Fintype.card_fin]
  rw [hcard] at hkey
  have hstar : ∑ t ∈ Finset.range T, l t i
      = ∑ t ∈ Finset.range T, ceOneHot (lab t) (z t i) := by
    rw [hll]
  rw [hstar] at hkey
  linarith

section Anchor

/-- Якорные эксперты (Fin 2): эксперт 0 = `wz1` (уверенно прав на
метке 0, CE = log(1+e⁻²) ≈ 0.13), эксперт 1 = константа 1
(откалиброванный сиделец на заборе, CE = log 2 ≈ 0.69). Оба CE ≤ 1
— посылка exact-expert abstention выполнена. -/
noncomputable def az : ℕ → Fin 2 → Fin 2 → ℝ := fun _ i v =>
  if i = 0 then (if v = 0 then 2 else 0) else 1

/-- Точное значение CE якорных экспертов: ветка 0 — log(1+e⁻²),
ветка 1 — log 2 (lse константы 1 равен log 2 + 1). -/
theorem az_ce (t : ℕ) (i : Fin 2) :
    ceOneHot 0 (az t i) = if i = 0
      then Real.log (1 + Real.exp (-(2:ℝ))) else Real.log 2 := by
  by_cases h : i = 0
  · have heq : az t i = wz1 := by
      funext v; subst h; cases v <;> simp [az, wz1]
    have hlse : lse wz1 = Real.log (Real.exp (2:ℝ) + 1) := by
      rw [lse_wz wz1 2 0 ⟨rfl, rfl⟩, Real.exp_zero]
    have hprod : Real.exp (2:ℝ) * Real.exp (-(2:ℝ)) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hinv : (Real.exp (2:ℝ))⁻¹ = Real.exp (-(2:ℝ)) := by
      rw [inv_eq_one_div, div_eq_iff (Real.exp_ne_zero 2), mul_comm,
        ← Real.exp_add]
      norm_num
    have hval : Real.log (1 + Real.exp (-(2:ℝ)))
        = Real.log (Real.exp (2:ℝ) + 1) - 2 := by
      have h1 : (1:ℝ) + Real.exp (-(2:ℝ))
          = (Real.exp (2:ℝ) + 1) / Real.exp 2 := by
        rw [add_div, div_self (Real.exp_ne_zero 2), one_div, hinv]
      rw [h1, Real.log_div (by positivity) (by positivity), Real.log_exp]
    have hz0 : wz1 0 = 2 := rfl
    rw [heq, if_pos h]
    unfold ceOneHot
    rw [hlse, hz0, hval]
  · have hfun : az t i = fun _ => (1:ℝ) := by
      funext v; cases v <;> simp [az, h]
    have hlse : lse (fun _ : Fin 2 => (1:ℝ)) = Real.log 2 + 1 := by
      unfold lse
      rw [Fin.sum_univ_two, ← two_mul (Real.exp 1),
        Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    rw [hfun, if_neg h]
    unfold ceOneHot
    rw [hlse]
    ring

/-- Посылка hce для якоря: оба эксперта в диапазоне [0,1]
(log 2 < 1 и log(1+e⁻²) ≤ log 2 — границы из `Real.log_two_lt_d9`
и монотонности exp). -/
theorem az_ce_le_one (t : ℕ) (i : Fin 2) :
    ceOneHot 0 (az t i) ≤ 1 := by
  have hlt : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hle : Real.exp (-(2:ℝ)) ≤ 1 := by
    have h0 := Real.exp_le_exp.mpr (by norm_num : (-(2:ℝ)) ≤ 0)
    rw [Real.exp_zero] at h0
    exact h0
  rw [az_ce]
  by_cases h : i = 0
  · rw [if_pos h]
    have h1 : (1:ℝ) + Real.exp (-(2:ℝ)) ≤ 2 := by linarith
    have h3 : Real.log (1 + Real.exp (-(2:ℝ))) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) h1
    linarith
  · rw [if_neg h]
    linarith

/-- Смесь якоря на раунде t с Hedge-весами (η = 1/2). -/
noncomputable def anchorMix (t : ℕ) : ℝ := ceOneHot 0
  (fun v => ∑ i : Fin 2,
    ewNorm (fun t i => ceOneHot 0 (az t i)) (1/2) t i * az t i v)

/-- ЧИСЛОВАЯ ПРОВЕРКА КОМПОЗИЦИИ (2 эксперта, 3 раунда, η = 1/2):
(а) НЕВАКУУНСТВО — на раунде 0 Hedge-веса равномерны (1/2, 1/2),
смесь (3/2, 1/2) даёт СТРОГО положительный CE log(e^(3/2)+e^(1/2)) −
3/2 > 0; (б) ИТОГ — инстанциация `soft_router_total_bound` даёт
total ≤ 3·L + 2·log 2 + 3/4 (regret-константа log 2/(1/2) + (1/2)·3/2
при N = 2, T = 3), численно < 4·L + 3 при L = log(1+e⁻²). -/
theorem total_bound_anchor :
    (0:ℝ) < ∑ t ∈ Finset.range 3, anchorMix t
      ∧ ∑ t ∈ Finset.range 3, anchorMix t
        < 4 * Real.log (1 + Real.exp (-(2:ℝ))) + 3 := by
  constructor
  · have hpos0 : (0:ℝ) < anchorMix 0 := by
      have hw : ewNorm (fun t i => ceOneHot 0 (az t i)) (1/2) 0
          = fun _ => (1/2 : ℝ) := by
        funext i
        unfold ewNorm ewPot ewWeight
        simp [Fin.sum_univ_two]
      have hmix : (fun v => ∑ i : Fin 2,
          ewNorm (fun t i => ceOneHot 0 (az t i)) (1/2) 0 i * az 0 i v)
          = fun v => if v = 0 then (3/2:ℝ) else (1/2:ℝ) := by
        funext v
        rw [hw, Fin.sum_univ_two]
        fin_cases v <;> simp [az] <;> norm_num
      unfold anchorMix
      rw [hmix]
      unfold ceOneHot lse
      have h4 : (∑ v : Fin 2, Real.exp (if v = 0 then (3/2:ℝ) else 1/2))
          = Real.exp (3/2:ℝ) + Real.exp (1/2:ℝ) := by
        rw [Fin.sum_univ_two]; simp
      rw [h4]
      have h1 : Real.exp (3/2:ℝ)
          < Real.exp (3/2:ℝ) + Real.exp (1/2:ℝ) := by
        linarith [Real.exp_pos (1/2:ℝ)]
      have h2 : Real.log (Real.exp (3/2:ℝ))
          < Real.log (Real.exp (3/2:ℝ) + Real.exp (1/2:ℝ)) :=
        Real.log_lt_log (by positivity) h1
      rw [Real.log_exp] at h2
      simp only [if_pos rfl, if_true]
      linarith
    have hrest : ∀ t ∈ Finset.range 3, (0:ℝ) ≤ anchorMix t :=
      fun t _ => ceOneHot_nonneg 0 _
    exact Finset.sum_pos' (fun t ht => hrest t (by simpa using ht))
      ⟨0, Finset.mem_range.mpr (by omega), hpos0⟩
  · have hmain := soft_router_total_bound (k := Fin 2) (N := 2)
      (1/2) ⟨by norm_num, by norm_num⟩ 3 (fun _ => 0) az
      (fun t ht i => az_ce_le_one t i) 0
    have hL0 : ∑ t ∈ Finset.range 3, ceOneHot 0 (az t 0)
        = 3 * Real.log (1 + Real.exp (-(2:ℝ))) := by
      have hmem : ∀ t ∈ Finset.range 3, ceOneHot 0 (az t 0)
          = Real.log (1 + Real.exp (-(2:ℝ))) := by
        intro t _; rw [az_ce]; simp
      rw [Finset.sum_congr rfl fun t ht => hmem t ht]
      simp
    have hcard : Fintype.card (Fin 2) = 2 := rfl
    rw [hcard, hL0] at hmain
    push_cast at hmain
    have hsplit : Real.log 2 / (1/2:ℝ) = 2 * Real.log 2 := by field_simp
    rw [hsplit] at hmain
    rw [show ((1/2:ℝ) * 3) / 2 = 3/4 by norm_num] at hmain
    have hlog2 : Real.log 2 < 7/10 :=
      Real.log_two_lt_d9.trans (by norm_num)
    have hLpos : (0:ℝ) ≤ Real.log (1 + Real.exp (-(2:ℝ))) :=
      Real.log_nonneg (by
        have := Real.exp_nonneg (-(2:ℝ)); linarith)
    have hnum : 2 * Real.log 2 + 3/4
        < Real.log (1 + Real.exp (-(2:ℝ))) + 3 := by nlinarith
    have hS : ∑ t ∈ Finset.range 3, anchorMix t
        ≤ 3 * Real.log (1 + Real.exp (-(2:ℝ))) + 2 * Real.log 2 + 3/4 :=
      hmain
    linarith

end Anchor

end Hagi.Learning.SoftRouterTotal
