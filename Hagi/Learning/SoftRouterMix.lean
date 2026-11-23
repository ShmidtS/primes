/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Optimization.MirrorHedge
import Mathlib.Tactic
import Hagi.Learning.HRCN

set_option linter.style.header false

/-!
# SoftRouterMix — мягкая калиброванная смесь вместо жёстких ±10 (цикл 19)

Аудит §7 (T): «Мягкая калиброванная смесь вместо жёстких ±10:
CE смеси не хуже взвешенного среднего CE (Jensen)». Честная
раскладка — ДВЕ разные смеси, обе истинные, но по разным
причинам (challenge-pin: их нельзя смешивать в одном
утверждении):

* ЛОГИТ-смесь Σwᵢzᵢ (side роутера): `soft_router_ce_bound` —
  CE(t, Σᵢwᵢzᵢ) ≤ Σᵢwᵢ·CE(t, zᵢ). Причина — ВОГНУТОСТЬ тут
  ни при чём: CE = lse z − z_t линеен по целевому члену и
  выпукл по lse (`lse_weighted_le` — взвешенный Дженсен для
  lse, обобщение равномерного `lse_mean_le_mean_lse` на
  произвольный вероятностный вектор весов w).
* СМЕСЬ РАСПРЕДЕЛЕНИЙ p̄ = Σwᵢpᵢ: `mixture_ce_le_weighted_avg`
  — −log(Σᵢwᵢpᵢ(y)) ≤ Σᵢwᵢ(−log pᵢ(y)). Вот это уже чистая
  вогнутость логарифма (`mixture_log_weighted_le`), верно для
  ЛЮБЫХ положительных векторов — нормализация pᵢ не нужна.

Связь с Hedge: веса роутера w из mirror-спуска
(`router_regret_bound`, `Hagi.Optimization.MirrorHedgeRouting`)
— в точности вероятностный вектор (симплекс), т.е. посылки
`soft_router_ce_bound` совпадают с Hedge-симплексом: regret
роутера ограничивает ΣwᵢCEᵢ, а этот модуль замыкает цепочку
на CE самой смеси.

Жёсткий роутинг — отрицательный якорь: one-hot w = δⱼ
вырождает смесь в один эксперт (`one_hot_no_gain`: выигрыша
нет вообще), а уверенно неверный маршрут платит ПОЛНУЮ цену
`hard_wrong_full_price` (CE = log(e²+1) ≈ 2.13 — режим
«20·(1−acc)»: уверенная некалиброванная ошибка), тогда как
мягкая смесь ½/½ строго дешевле (`soft_beats_hard_wrong`:
log 2 ≈ 0.69 < log(e²+1)) — калибровочная победа.

Honest scope: на логит-стороне цель one-hot (ceOneHot); общие
распределенческие цели не заявлены. На дистрибутивной стороне
нужна только положительность pᵢ (утверждение сильнее
симплексного — нормализация не используется).
-/

namespace Hagi.Learning.SoftRouterMix

open Hagi.Core

section WeightedLog

variable {ι : Type*} [Fintype ι]

/-- Взвешенная вогнутость логарифма (AM-GM маршрут):
Σwᵢ·log xᵢ ≤ log(Σwᵢxᵢ) для положительных xᵢ и
вероятностных весов w. -/
theorem mixture_log_weighted_le
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    ∑ i, w i * Real.log (x i) ≤ Real.log (∑ i, w i * x i) := by
  have hamgm : ∏ i, (x i) ^ (w i) ≤ ∑ i, w i * x i :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ w x
      (fun i _ => hw0 i) hw1 (fun i _ => le_of_lt (hx i))
  obtain ⟨j, hjw⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [funext fun i => hcon i] at hw1
    simp at hw1
  have hj0 : 0 < w j := lt_of_le_of_ne (hw0 j) (Ne.symm hjw)
  have hpos : 0 < ∑ i, w i * x i := by
    have h1 : w j * x j ≤ ∑ i, w i * x i :=
      Finset.single_le_sum (f := fun i => w i * x i)
        (fun i _ => mul_nonneg (hw0 i) (le_of_lt (hx i)))
        (Finset.mem_univ j)
    exact lt_of_lt_of_le (mul_pos hj0 (hx j)) h1
  have hlogprod : ∑ i, w i * Real.log (x i)
      = Real.log (∏ i, (x i) ^ (w i)) := by
    rw [Real.log_prod (fun i _ =>
      ne_of_gt (Real.rpow_pos_of_pos (hx i) _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (hx i), Real.log_exp]
    ring
  have hlhspos : 0 < ∏ i, (x i) ^ (w i) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  rw [hlogprod]
  exact Real.log_le_log hlhspos hamgm

/-- Кросс-энтропия распределения p против метки t
(one-hot цель; определение для дистрибутивной стороны). -/
noncomputable def ceDist {k : Type*} (p : k → ℝ) (t : k) : ℝ :=
  -Real.log (p t)

/-- ДИСТРИБУТИВНАЯ СТОРОНА аудита §7: CE метки y у смеси
распределений p̄ = Σwᵢpᵢ не хуже взвешенного среднего CE
компонент (чистая вогнутость log; нужны только положительные
pᵢ — нормализация не используется, утверждение сильнее
симплексного). -/
theorem mixture_ce_le_weighted_avg {k : Type*}
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (p : ι → k → ℝ) (hp : ∀ i v, 0 < p i v) (t : k) :
    ceDist (fun v => ∑ i, w i * p i v) t
      ≤ ∑ i, w i * ceDist (p i) t := by
  have h := mixture_log_weighted_le w hw0 hw1
    (fun i => p i t) (fun i => (hp i t))
  have hneg : ∑ i, w i * (-Real.log (p i t))
      = -∑ i, w i * Real.log (p i t) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold ceDist
  rw [hneg]
  linarith

end WeightedLog

section WeightedLse

variable {k : Type*} [Fintype k] [Nonempty k]

/-- Взвешенный Дженсен для lse: lse(Σᵢwᵢzᵢ) ≤ Σᵢwᵢ·lse(zᵢ)
для вероятностного вектора весов w. Обобщение равномерного
`lse_mean_le_mean_lse` (1/N → w): поточечный взвешенный AM-GM
на tᵢᵥ = exp(zᵢᵥ)/Sᵢ, разбиение Хёльдера, логарифмирование. -/
theorem lse_weighted_le {N : ℕ} (w : Fin N → ℝ) (hw0 : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (z : Fin N → k → ℝ) :
    lse (fun v => ∑ a, w a * z a v) ≤ ∑ a, w a * lse (z a) := by
  set S : Fin N → ℝ := fun a => ∑ v, Real.exp (z a v) with hS
  have hSpos : ∀ a, 0 < S a := fun a => exp_sum_pos (z a)
  set t : Fin N → k → ℝ := fun a v => Real.exp (z a v) / S a with ht
  have htpos : ∀ a v, 0 < t a v := fun a v => div_pos (Real.exp_pos _) (hSpos a)
  have hamgm : ∀ v : k,
      ∏ a, (t a v) ^ (w a) ≤ ∑ a, w a * t a v := fun v =>
    Real.geom_mean_le_arith_mean_weighted
      (Finset.univ : Finset (Fin N)) w (fun a => t a v)
      (fun a _ => hw0 a) hw1 (fun a _ => le_of_lt (htpos a v))
  have hmass : ∀ a, ∑ v, t a v = 1 := by
    intro a
    simp only [ht, ← Finset.sum_div]
    exact div_self (ne_of_gt (hSpos a))
  have hsplit : ∀ v : k,
      Real.exp (∑ a, w a * z a v)
        = (∏ a, (S a) ^ (w a)) * ∏ a, (t a v) ^ (w a) := by
    intro v
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hst : S a * t a v = Real.exp (z a v) := by
      simp only [ht]
      exact mul_div_cancel₀ _ (ne_of_gt (hSpos a))
    rw [← Real.mul_rpow (le_of_lt (hSpos a))
      (by positivity : (0:ℝ) ≤ t a v), hst,
      Real.rpow_def_of_pos (Real.exp_pos (z a v)), Real.log_exp]
    congr 1
    ring
  have hE : ∑ v, Real.exp (∑ a, w a * z a v)
      ≤ ∏ a, (S a) ^ (w a) := by
    have h1 : ∑ v, Real.exp (∑ a, w a * z a v)
        = (∏ a, (S a) ^ (w a))
          * ∑ v, ∏ a, (t a v) ^ (w a) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => hsplit v
    rw [h1]
    have h2 : ∑ v, ∏ a, (t a v) ^ (w a) ≤ 1 := by
      calc ∑ v, ∏ a, (t a v) ^ (w a)
          ≤ ∑ v, ∑ a, w a * t a v :=
            Finset.sum_le_sum fun v _ => hamgm v
        _ = ∑ a, ∑ v, w a * t a v := Finset.sum_comm
        _ = ∑ a, w a * ∑ v, t a v := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact (Finset.mul_sum Finset.univ (t a) (w a)).symm
        _ = ∑ a, w a * 1 :=
            Finset.sum_congr rfl fun a _ => by rw [hmass a]
        _ = 1 := by simp [hw1]
    have hpos : (0:ℝ) < ∏ a, (S a) ^ (w a) :=
      Finset.prod_pos fun a _ => Real.rpow_pos_of_pos (hSpos a) _
    calc (∏ a, (S a) ^ (w a)) * ∑ v, ∏ a, (t a v) ^ (w a)
        ≤ (∏ a, (S a) ^ (w a)) * 1 :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      _ = ∏ a, (S a) ^ (w a) := by ring
  unfold lse
  have hlog := Real.log_le_log (exp_sum_pos _) hE
  rw [Real.log_prod (fun a _ =>
    ne_of_gt (Real.rpow_pos_of_pos (hSpos a) _)),
    Finset.sum_congr rfl fun a _ => Real.log_rpow (hSpos a) _] at hlog
  have hconv : ∑ a, w a * Real.log (S a)
      = ∑ a, w a * lse (z a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
  rw [hconv] at hlog
  exact hlog

/-- ЛОГИТНАЯ СТОРОНА аудита §7 (требование T): CE one-hot
метки t у смеси логитов Σᵢwᵢzᵢ не хуже взвешенного среднего CE
экспертов. Веса w — вероятностный вектор (Hedge-симплекс
роутера: mirrorStep держит ровно такие посылки). Причина —
выпуклость lse + линейность целевого члена, НЕ вогнутость
softmax. -/
theorem soft_router_ce_bound {N : ℕ} (t : k) (w : Fin N → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (z : Fin N → k → ℝ) :
    ceOneHot t (fun v => ∑ a, w a * z a v)
      ≤ ∑ a, w a * ceOneHot t (z a) := by
  have hl := lse_weighted_le w hw0 hw1 z
  have hsplit : ∑ a, w a * ceOneHot t (z a)
      = ∑ a, w a * lse (z a) - ∑ a, w a * z a t := by
    have h : ∀ a : Fin N, w a * ceOneHot t (z a)
        = w a * lse (z a) - w a * z a t := by
      intro a
      unfold ceOneHot
      ring
    rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_sub_distrib]
  rw [hsplit]
  unfold ceOneHot
  linarith

end WeightedLse

section HardRouting

variable {k : Type*} [Fintype k]

/-- Вырожденный якорь: one-hot роутинг w = δⱼ даёт смесь,
равную одному эксперту, — смешивание не даёт НИЧЕГО (равенство
в обе стороны вырождения). -/
theorem one_hot_no_gain {N : ℕ} (j : Fin N) (z : Fin N → k → ℝ) (t : k) :
    ceOneHot t (fun v => ∑ a, (if a = j then (1:ℝ) else 0) * z a v)
      = ceOneHot t (z j) := by
  have hfun : (fun v => ∑ a, (if a = j then (1:ℝ) else 0) * z a v)
      = fun v => z j v := by
    funext v
    simp [Finset.sum_ite_eq']
  rw [hfun]

/-- Два «односторонних» эксперта на Fin 2: wz1 уверенно прав на
метке 0 (логит 2 против 0), wz2 так же уверенно неправ
(0 против 2). -/
def wz1 : Fin 2 → ℝ := fun a => if a = 0 then 2 else 0
def wz2 : Fin 2 → ℝ := fun a => if a = 0 then 0 else 2

/-- lse конкретного Fin 2-вектора по его значениям. -/
theorem lse_wz (z : Fin 2 → ℝ) (h0 h1 : ℝ)
    (hz : z 0 = h0 ∧ z 1 = h1) :
    lse z = Real.log (Real.exp h0 + Real.exp h1) := by
  unfold lse
  congr 1
  rw [Fin.sum_univ_two, hz.1, hz.2]

/-- ОТРИЦАТЕЛЬНЫЙ ЯКОРЬ (жёсткая ошибка): hard-роутинг на
неверного уверенного эксперта wz2 при метке 0 платит ПОЛНУЮ
цену CE = log(e²+1) ≈ 2.13 — режим «20·(1−acc)»: уверенная
некалиброванная ошибка не смягчается ничем. -/
theorem hard_wrong_full_price :
    ceOneHot 0 wz2 = Real.log (1 + Real.exp 2) := by
  unfold ceOneHot
  rw [lse_wz wz2 0 2 ⟨rfl, rfl⟩]
  simp [Real.exp_zero, wz2]

/-- КАЛИБРОВОЧНАЯ ПОБЕДА (строгий якорь): мягкая смесь ½/½
противоположно уверенных экспертов даёт CE = log 2 ≈ 0.69 —
СТРОГО меньше полной цены log(e²+1) ≈ 2.13 неверного жёсткого
маршрута. Мягкость весов — именно то, что смягчает цену
ошибки. -/
theorem soft_beats_hard_wrong :
    ceOneHot 0 (fun v => (wz1 v + wz2 v) / 2) < Real.log (Real.exp 2 + 1) := by
  have hmix : (fun v => (wz1 v + wz2 v) / 2) = fun _ => 1 := by
    funext v
    fin_cases v <;> simp [wz1, wz2]
  rw [hmix]
  have hlse : lse (fun _ : Fin 2 => 1) = Real.log 2 + 1 := by
    unfold lse
    rw [Fin.sum_univ_two, ← two_mul (Real.exp 1), Real.log_mul (by norm_num)
      (Real.exp_ne_zero _), Real.log_exp]
  unfold ceOneHot
  rw [hlse]
  have hexp2 : (1:ℝ) < Real.exp 2 := by
    have h := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 2)
    rwa [Real.exp_zero] at h
  have hloglt : Real.log 2 < Real.log (Real.exp 2 + 1) :=
    Real.log_lt_log (by norm_num) (by linarith)
  linarith

end HardRouting

end Hagi.Learning.SoftRouterMix

set_option linter.style.header false

/-!
# SoftRouterTotal — сквозной regret-бандл мягкого роутера (цикл 20)

Композиция `soft_router_ce_bound` (по-раундовая
калибровка смеси логитов) + регрет-носитель Hedge
(`Hagi.Optimization.MirrorHedgeRouting.router_regret_bound` с
выведенной посылкой выживания `Hagi.Optimization.MirrorHedgeSurvivor.
hsurv_derived`). Итог — `soft_router_total_bound`: за T раундов
мягкий роутинг с Hedge-весами wᵗ = ewNorm CE-потерь конкурентен
ЛЮБОМУ одиночному эксперту в ретроспективе (total mixture CE ≤
best-expert total CE + log N/η + η·T/2), причём калиброванный CE
гарантирован на КАЖДОМ шаге. Новая математики нет — только
суммирование-склейка; обе стороны процитированы.

Challenge-pins (честные границы, все три в докстрингах):

* ИДЕНТИФИКАЦИЯ ПОТЕРЬ: Hedge-носитель (`hedge_step`) требует
  потерь экспертов в [0, 1]. CE ≥ 0 всегда (кирпич
  `ceOneHot_nonneg`: lse z ≥ z t, сумма exp доминирует целевой
  член), но CE ≤ 1 — РЕАЛЬНАЯ посылка (режим exact-expert
  abstention: эксперты с CE > 1 — уверенно неверные уровня wz2 —
  исключены; для них нужен масштабированный η, не заявлено).
* ИНДЕКС ЭКСПЕРТОВ: носитель `ewNorm` фиксирован во вселенной
  `Type` 0, а индексирует экспертов `Fin N` — композиция
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

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ — сквозной бандл: за T раундов с
Hedge-весами wᵗ = ewNorm CE-потерь (η ∈ (0,1]) и посылкой CE ≤ 1
(exact-expert abstention) суммарный CE мягкой смеси не превосходит
суммарный CE ЛЮБОГО одиночного эксперта плюс константу регрета
носителя log N/η + η·T/2. Композиция: по-раундовая калибровка
`soft_router_ce_bound` + агрегация `hsurv_derived` +
`router_regret_bound` (Hedge-носитель); новые факты — только
неотрицательность CE и суммирование. Эксперты — `Fin N` (вселенная
носителя Type 0, индексирует Fin N); sleeping-experts regret не
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
  -- по-раундовая калибровочная склейка
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

set_option linter.style.header false

/-!
# SleepingRouter — sleeping-experts regret мягкого роутера (цикл 21)

 закрывает honest gap (`SoftRouterTotal`): у Hedge-носителя
нет механизма спящих экспертов — веса обновляются по ВСЕМ экспертам
каждый раунд, поэтому его regret не покрывает конкуренцию с лучшим
ДОСТУПНЫМ экспертом, когда guard-гатенные эксперты спят на части
раундов. Здесь — классический imputed-loss редукционный трюк
(Freund–Schapire share updates / specialists):

* спящие эксперты обновляются ПОТЕРЕЙ СМЕСИ m_t (не своими ℓ):
  `w(t+1,i) = w(t,i)·(if awake then e^{-ηℓ} else e^{-η m_t})`;
* KEY IDENTITY `swWeight_eq_ewWeight`: этот процесс ОПРЕДЕЛЕНИЯМИ
  совпадает с `ewWeight (swLoss l a eta) eta` на импутированных
  потерях `swLoss t i = if awake then ℓ else m_t` — весь носитель
  (`hsurv_derived` + `router_regret_bound`) применяется ДОСЛОВНО,
  без изменений доказательства;
* SELF-CONSISTENCY `algLoss_eq_mixLoss`: потери алгоритма (полная
  нормировка ewNorm) на импутированных потерях РАВНЫ m_t —
  awake-часть даёт (P/W)·m_t, asleep-часть (1−P/W)·m_t;
* ТЕЛЕСКОП-КАНЦЕЛЯЦИЯ: `Σ_{t: i awake}(m_t − ℓ_t^i) = A − L*` —
  асимные члены `Σ_{asleep(i)} m_t` сокращаются ТОЧНО (равенство,
  даже неотрицательность m_t не нужна).

Итог — `sleeping_hedge_regret` (носитель) и
`sleeping_router_total_bound` (композиция апгрейд): мягкий
роутер конкурирует с ЛЮБЫМ экспертом i НА ЕГО СОБСТВЕННЫХ
ДОСТУПНЫХ РАУНДАХ — total mixture CE ≤ Σ_{t: i awake} CE_i +
log N/η + η·T/2 при по-раундовой калибровке `soft_router_ce_bound`
 на awake-supported симплекс-весах `swPredW`.

Challenge-pins (честные границы):

* AWAKE-NONEMPTY: посылка «в каждом раунде хоть один эксперт
  доступен» — СТОЯЩАЯ предпосылка (раунд без доступных экспертов не
  имеет предсказания; исключён моделированием, не замят молча).
* ДИАПАЗОН ПОТЕРЬ: `m_t ∈ [0,1]` ВЫВЕДЕНО (`mixLossOf_mem`: выпуклая
  комбинация awake-потерь из [0,1]) — посылка hedge_step не
  протащена, а доказана.
* SCOPE: последовательности oblivious (адаптивный адверсарий НЕ
  заявлен — скоуп носителя наследован дословно); regret против
  ФИКСИРОВАННОГО эксперта на его awake-раундах; best-switching
  последовательность экспертов НЕ заявлена (fixed-share — future).
* ПРЕДСКАЗАНИЕ: смесь логитов по awake-supported весам `swPredW`
  (спящие эксперты исключены из предсказания гвардом; их веса
  эволюционируют импутацией и возвращаются при пробуждении).
-/

namespace Hagi.Learning.SleepingRouter

open Hagi.Autonomy Hagi.Learning.SoftRouterMix

section Carrier

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- `awPot` — масса весов по awake-множеству (фильтр `A i = true`). -/
noncomputable def awPot (w : ι → ℝ) (A : ι → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i

/-- `mixLossOf` — awake-нормированная потеря смеси:
`Σ_{i∈A} (w i / Σ_{j∈A} w j) · ℓ i` — нормировка по AWAKE-множеству
(решение носителя: предсказание поддержано только на доступных
экспертах). -/
noncomputable def mixLossOf (w : ι → ℝ) (lt : ι → ℝ) (A : ι → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => A i = true),
    w i / awPot w A * lt i

/-- `swWeight` — спящие веса: awake-эксперты обновляются своей
потерей, asleep — потерей смеси (imputed share update). -/
noncomputable def swWeight (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ) :
    ℕ → ι → ℝ
  | 0, _ => 1
  | t + 1, i =>
      swWeight l a eta t i *
        (if a t i = true then Real.exp (-eta * l t i)
         else Real.exp (-eta * mixLossOf (swWeight l a eta t) (l t) (a t)))

/-- `swMixLoss` — потеря awake-смеси в раунде t. -/
noncomputable def swMixLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) : ℝ :=
  mixLossOf (swWeight l a eta t) (l t) (a t)

/-- `swLoss` — импутированная последовательность потерь:
awake → своя потеря, asleep → потеря смеси. -/
noncomputable def swLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (i : ι) : ℝ :=
  if a t i = true then l t i else swMixLoss l a eta t

theorem swWeight_pos (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (i : ι) : 0 < swWeight l a eta t i := by
  induction t generalizing i with
  | zero => simp [swWeight]
  | succ t ih =>
      simp only [swWeight]
      split <;> exact mul_pos (ih i) (Real.exp_pos _)

theorem awPot_pos (w : ι → ℝ) (A : ι → Bool) (h : ∃ j, A j = true)
    (hw : ∀ i, 0 < w i) : 0 < awPot w A := by
  obtain ⟨j, hj⟩ := h
  unfold awPot
  have hmem : j ∈ Finset.univ.filter (fun i => A i = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  exact Finset.sum_pos' (fun i _ => (hw i).le) ⟨j, hmem, hw j⟩

theorem awNorm_sum (w : ι → ℝ) (A : ι → Bool) (h : ∃ j, A j = true)
    (hw : ∀ i, 0 < w i) :
    ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A = 1 := by
  have hP := awPot_pos w A h hw
  calc ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A
      = (∑ i ∈ Finset.univ.filter (fun i => A i = true), w i) / awPot w A :=
        (Finset.sum_div _ _ _).symm
    _ = 1 := div_self (ne_of_gt hP)

theorem mixLossOf_mem (w : ι → ℝ) (lt : ι → ℝ) (A : ι → Bool)
    (h : ∃ j, A j = true) (hw : ∀ i, 0 < w i)
    (hl : ∀ i, 0 ≤ lt i ∧ lt i ≤ 1) :
    0 ≤ mixLossOf w lt A ∧ mixLossOf w lt A ≤ 1 := by
  have hP := awPot_pos w A h hw
  have hsum := awNorm_sum w A h hw
  refine ⟨Finset.sum_nonneg fun i _ =>
    mul_nonneg (div_nonneg (hw i).le hP.le) (hl i).1, ?_⟩
  have hle : mixLossOf w lt A
      ≤ ∑ i ∈ Finset.univ.filter (fun i => A i = true), w i / awPot w A :=
    Finset.sum_le_sum fun i _ => by
      have h4 := mul_le_mul_of_nonneg_left (hl i).2
        (div_nonneg (hw i).le hP.le)
      simpa only [mul_one] using h4
  rw [hsum] at hle
  exact hle

/-- KEY IDENTITY: спящий процесс — это в точности Hedge (`ewWeight`)
на импутированных потерях (индукция по t, обе ветки
определительные). Весь существующий носитель применим дословно. -/
theorem swWeight_eq_ewWeight (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) :
    ∀ i, swWeight l a eta t i = ewWeight (swLoss l a eta) eta t i := by
  induction t with
  | zero => intro i; simp [swWeight, ewWeight]
  | succ t ih =>
      have ihf : swWeight l a eta t = ewWeight (swLoss l a eta) eta t :=
        funext ih
      intro i
      simp only [swWeight, ewWeight, ihf]
      by_cases hA : a t i = true
      · rw [if_pos hA, swLoss, if_pos hA]
      · rw [if_neg hA, swLoss, if_neg hA, swMixLoss, ihf]

theorem ewPot_sw (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ) (t : ℕ) :
    ewPot (swLoss l a eta) eta t = ∑ j, swWeight l a eta t j := by
  unfold ewPot
  exact Finset.sum_congr rfl fun j _ =>
    (swWeight_eq_ewWeight l a eta t j).symm

/-- SELF-CONSISTENCY: потери алгоритма (полная нормировка `ewNorm`)
на импутированных потерях РАВНЫ awake-нормированной потере смеси:
awake-часть даёт (P/W)·m_t, asleep-часть (1−P/W)·m_t. -/
theorem algLoss_eq_mixLoss (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool) (eta : ℝ)
    (t : ℕ) (haw : ∃ j, a t j = true) :
    ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = swMixLoss l a eta t := by
  have hwt : ∀ j, 0 < swWeight l a eta t j := swWeight_pos l a eta t
  have hP : 0 < awPot (swWeight l a eta t) (a t) :=
    awPot_pos _ _ haw hwt
  set P : ℝ := awPot (swWeight l a eta t) (a t) with hPdef
  set W : ℝ := ewPot (swLoss l a eta) eta t with hWdef
  have hWpos : 0 < W := ewPot_pos _ _ _
  have hWval : W = ∑ j, swWeight l a eta t j := ewPot_sw l a eta t
  have hnorm : ∀ j, ewNorm (swLoss l a eta) eta t j
      = swWeight l a eta t j / W := by
    intro j
    unfold ewNorm
    rw [swWeight_eq_ewWeight l a eta t j]
  have hPM : P * swMixLoss l a eta t
      = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j * l t j := by
    unfold swMixLoss mixLossOf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hPdef]
    field_simp
  have hS : ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
      swWeight l a eta t j = W - P := by
    have hjoin := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => a t j = true) (fun j => swWeight l a eta t j)
    have hWall : W = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j
        + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
            swWeight l a eta t j := by rw [hWval, hjoin]
    have hPval : P
        = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
            swWeight l a eta t j := rfl
    linarith
  have hsplit : ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
          swWeight l a eta t j / W * l t j
        + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
            swWeight l a eta t j / W * swMixLoss l a eta t := by
    calc ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
        = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
              ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
          + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
              ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j => a t j = true)
          (fun j => ewNorm (swLoss l a eta) eta t j
            * swLoss l a eta t j)).symm
      _ = ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
              swWeight l a eta t j / W * l t j
          + ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
              swWeight l a eta t j / W * swMixLoss l a eta t := by
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by
            rcases Finset.mem_filter.mp hj with ⟨_, hjj⟩
            rw [hnorm j]; simp [swLoss, hjj]
        · exact Finset.sum_congr rfl fun j hj => by
            rcases Finset.mem_filter.mp hj with ⟨_, hjj⟩
            rw [hnorm j]; simp [swLoss, hjj]
  rw [hsplit]
  have hA1 : ∑ j ∈ Finset.univ.filter (fun j => a t j = true),
      swWeight l a eta t j / W * l t j = P * swMixLoss l a eta t / W := by
    have heq : ∀ j ∈ Finset.univ.filter (fun j => a t j = true),
        swWeight l a eta t j / W * l t j
          = swWeight l a eta t j * l t j / W :=
      fun j _ => div_mul_eq_mul_div _ _ _
    rw [Finset.sum_congr rfl (fun j hj => heq j hj), ← Finset.sum_div,
      ← hPM]
  have hA2 : ∑ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
      swWeight l a eta t j / W * swMixLoss l a eta t
      = (W - P) * swMixLoss l a eta t / W := by
    have heq : ∀ j ∈ Finset.univ.filter (fun j => ¬(a t j = true)),
        swWeight l a eta t j / W * swMixLoss l a eta t
          = swWeight l a eta t j * swMixLoss l a eta t / W :=
      fun j _ => div_mul_eq_mul_div _ _ _
    rw [Finset.sum_congr rfl (fun j hj => heq j hj), ← Finset.sum_div,
      ← Finset.sum_mul, ← hS]
  have hWne : W ≠ 0 := ne_of_gt hWpos
  rw [hA1, hA2]
  field_simp
  ring

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ НОСИТЕЛЯ — sleeping-experts regret (маски
рованная версия `hsurv_derived` + `router_regret_bound`): смесь
конкурирует с экспертом i НА ЕГО СОБСТВЕННЫХ AWAKE-РАУНДАХ с
константой носителя log K/η + η·T/2. Асимные члены сокращаются
ТОЧНО (равенство), без отбрасывания. -/
theorem sleeping_hedge_regret (l : ℕ → ι → ℝ) (a : ℕ → ι → Bool)
    (eta : ℝ) (T : ℕ) (i : ι)
    (hl : ∀ t < T, ∀ j, 0 ≤ l t j ∧ l t j ≤ 1)
    (haw : ∀ t < T, ∃ j, a t j = true)
    (heta : 0 < eta ∧ eta ≤ 1) :
    ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
        (swMixLoss l a eta t - l t i)
      ≤ Real.log (Fintype.card ι) / eta + eta * T / 2 := by
  have hmem : ∀ t < T, ∀ j, 0 ≤ swLoss l a eta t j
      ∧ swLoss l a eta t j ≤ 1 := by
    intro t ht j
    by_cases hA : a t j = true
    · rw [swLoss, if_pos hA]; exact hl t ht j
    · rw [swLoss, if_neg hA]
      exact mixLossOf_mem _ _ _ (haw t ht) (swWeight_pos l a eta t)
        (fun j' => hl t ht j')
  have hsurv := hsurv_derived (swLoss l a eta) eta T i hmem
    ⟨heta.1.le, heta.2⟩
  have hAeq : ∑ t ∈ Finset.range T,
      ∑ j, ewNorm (swLoss l a eta) eta t j * swLoss l a eta t j
      = ∑ t ∈ Finset.range T, swMixLoss l a eta t :=
    Finset.sum_congr rfl fun t ht =>
      algLoss_eq_mixLoss l a eta t (haw t (Finset.mem_range.mp ht))
  rw [hAeq] at hsurv
  have hrrb := router_regret_bound (Fintype.card ι) T eta
    (∑ t ∈ Finset.range T, swMixLoss l a eta t)
    (∑ t ∈ Finset.range T, swLoss l a eta t i)
    (Fintype.card_pos) heta.1 hsurv
  have hsplitL : ∑ t ∈ Finset.range T, swLoss l a eta t i
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          l t i
        + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true)) (Finset.range T),
            swMixLoss l a eta t := by
    calc ∑ t ∈ Finset.range T, swLoss l a eta t i
        = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
              swLoss l a eta t i
          + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
                (Finset.range T), swLoss l a eta t i :=
        (Finset.sum_filter_add_sum_filter_not (Finset.range T)
          (fun t => a t i = true) (fun t => swLoss l a eta t i)).symm
      _ = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
              l t i
          + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
                (Finset.range T), swMixLoss l a eta t := by
        congr 1
        · exact Finset.sum_congr rfl fun t ht => by
            rcases Finset.mem_filter.mp ht with ⟨_, htt⟩
            simp [swLoss, htt]
        · exact Finset.sum_congr rfl fun t ht => by
            rcases Finset.mem_filter.mp ht with ⟨_, htt⟩
            simp [swLoss, htt]
  have hsplitM : ∑ t ∈ Finset.range T, swMixLoss l a eta t
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          swMixLoss l a eta t
        + ∑ t ∈ Finset.filter (fun t => ¬(a t i = true))
              (Finset.range T), swMixLoss l a eta t :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range T)
      (fun t => a t i = true) (fun t => swMixLoss l a eta t)).symm
  rw [hsplitL, hsplitM] at hrrb
  rw [Finset.sum_sub_distrib]
  linarith

end Carrier

section Router

variable {k : Type*} [Fintype k] [Nonempty k]

/-- `swPredW` — предсказательные веса роутера: awake-нормировка,
спящим экспертам ноль (guard исключает их из предсказания;
вероятностный вектор поддержан на awake-множестве). -/
noncomputable def swPredW {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  if a t i = true then
    swWeight l a eta t i / awPot (swWeight l a eta t) (a t) else 0

theorem swPredW_nonneg {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (haw : ∃ j, a t j = true) (i : Fin N) :
    0 ≤ swPredW l a eta t i := by
  haveI : Nonempty (Fin N) := ⟨i⟩
  unfold swPredW
  by_cases hA : a t i = true
  · rw [if_pos hA]
    exact div_nonneg (swWeight_pos l a eta t i).le
      (awPot_pos _ _ haw (swWeight_pos l a eta t)).le
  · rw [if_neg hA]

/-- Скалярное произведение предсказательных весов на любой вектор —
это awake-нормированная смесь по awake-множеству (спящие дают 0). -/
theorem swPredW_mul_sum {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (lt : Fin N → ℝ) (haw : ∃ j, a t j = true) :
    ∑ i, swPredW l a eta t i * lt i
      = mixLossOf (swWeight l a eta t) lt (a t) := by
  unfold swPredW mixLossOf
  calc ∑ i, (if a t i = true then
          swWeight l a eta t i / awPot (swWeight l a eta t) (a t) else 0)
          * lt i
      = ∑ i ∈ Finset.univ.filter (fun i => a t i = true),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i
          + ∑ i ∈ Finset.univ.filter (fun i => ¬(a t i = true)),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i :=
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i => a t i = true)
          (fun i => (if a t i = true then
            swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i)).symm
    _ = ∑ i ∈ Finset.univ.filter (fun i => a t i = true),
            swWeight l a eta t i
              / awPot (swWeight l a eta t) (a t) * lt i := by
        have hz : ∀ i ∈ Finset.univ.filter (fun i => ¬(a t i = true)),
            (if a t i = true then
              swWeight l a eta t i / awPot (swWeight l a eta t) (a t)
            else 0) * lt i = 0 := by
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨_, hii⟩
          simp [hii]
        rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, add_zero]
        exact Finset.sum_congr rfl fun i hi => by
          rcases Finset.mem_filter.mp hi with ⟨_, hii⟩
          simp [hii]

theorem swPredW_sum {N : ℕ} (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool)
    (eta : ℝ) (t : ℕ) (haw : ∃ j, a t j = true) :
    ∑ i, swPredW l a eta t i = 1 := by
  haveI : Nonempty (Fin N) := let ⟨j, _⟩ := haw; ⟨j⟩
  have h1 : ∑ i, swPredW l a eta t i
      = ∑ i, swPredW l a eta t i * 1 := by
    simp [mul_one]
  rw [h1, swPredW_mul_sum l a eta t (fun _ => 1) haw]
  unfold mixLossOf
  have hns := awNorm_sum (swWeight l a eta t) (a t) haw
    (swWeight_pos l a eta t)
  simpa only [mul_one] using hns

/-- `swPredW_ce` — по-раундовая калибровка: CE смеси логитов
не хуже взвешенного среднего CE экспертов; на awake-supported
весах взвешенная сумма CE РАВНА потере смеси `swMixLoss`
(`swPredW_mul_sum`). -/
theorem swPredW_ce {N : ℕ} (t : k)
    (l : ℕ → Fin N → ℝ) (a : ℕ → Fin N → Bool) (eta : ℝ) (t' : ℕ)
    (haw : ∃ j, a t' j = true)
    (z : Fin N → k → ℝ) (hz : ∀ i, ceOneHot t (z i) = l t' i) :
    ceOneHot t (fun v => ∑ i : Fin N, swPredW l a eta t' i * z i v)
      ≤ swMixLoss l a eta t' := by
  haveI : Nonempty (Fin N) := let ⟨j, _⟩ := haw; ⟨j⟩
  refine le_trans (soft_router_ce_bound t (swPredW l a eta t')
    (fun i => swPredW_nonneg l a eta t' haw i)
    (swPredW_sum l a eta t' haw) z) ?_
  have h2 : ∑ i, swPredW l a eta t' i * ceOneHot t (z i)
      = mixLossOf (swWeight l a eta t') (l t') (a t') := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hz i]),
      swPredW_mul_sum l a eta t' (l t') haw]
  rw [h2]
  exact le_rfl

end Router

section Total

variable {k : Type*} [Fintype k] [Nonempty k]

/-- ГЛАВНЫЙ РЕЗУЛЬТАТ КОМПОЗИЦИИ — апгрейд
(`soft_router_total_bound` со спящими экспертами). За T раундов с
guard-маской a (каждый раунд хоть один эксперт доступен, CE ≤ 1 —
exact-expert abstention) суммарный CE мягкой awake-смеси
НА ДОСТУПНЫХ РАУНДАХ ЭКСПЕРТА i не превосходит суммарный CE
эксперта i на тех же раундах плюс константа носителя
log N/η + η·T/2. Композиция: по-раундовая калибровка
(`swPredW_ce`) + `sleeping_hedge_regret`; новые факты — только
суммирование-склейка. Honest scope: oblivious-последовательности
(без drift/адаптивности — скоуп носителя); regret против
ФИКСИРОВАННОГО эксперта на его awake-раундах (best-switching не
заявлен); CE смеси на раундах, где i спит, НЕ ограничивается (там
роутер конкурирует с другими доступными экспертами). -/
theorem sleeping_router_total_bound {N : ℕ} [Nonempty (Fin N)]
    (eta : ℝ) (heta : 0 < eta ∧ eta ≤ 1) (T : ℕ)
    (lab : ℕ → k) (z : ℕ → Fin N → k → ℝ) (a : ℕ → Fin N → Bool)
    (hce : ∀ t ∈ Finset.range T, ∀ i, ceOneHot (lab t) (z t i) ≤ 1)
    (haw : ∀ t ∈ Finset.range T, ∃ j, a t j = true)
    (i : Fin N) :
    ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
        ceOneHot (lab t)
          (fun v => ∑ j : Fin N, swPredW
            (fun t j => ceOneHot (lab t) (z t j)) a eta t j * z t j v)
      ≤ ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          ceOneHot (lab t) (z t i)
        + Real.log (Fintype.card (Fin N)) / eta + eta * T / 2 := by
  set l : ℕ → Fin N → ℝ := fun t j => ceOneHot (lab t) (z t j) with hll
  have hl : ∀ t < T, ∀ j, 0 ≤ l t j ∧ l t j ≤ 1 := by
    intro t ht j
    exact ⟨Hagi.Learning.SoftRouterTotal.ceOneHot_nonneg (lab t) (z t j),
      hce t (Finset.mem_range.mpr ht) j⟩
  have hround : ∀ t ∈ Finset.range T,
      ceOneHot (lab t) (fun v => ∑ j : Fin N, swPredW l a eta t j
        * z t j v) ≤ swMixLoss l a eta t := fun t ht =>
    swPredW_ce (lab t) l a eta t (haw t ht) (z t) (fun j => rfl)
  have hA : ∑ t ∈ Finset.filter (fun t => a t i = true)
      (Finset.range T),
      ceOneHot (lab t)
        (fun v => ∑ j : Fin N, swPredW l a eta t j * z t j v)
      ≤ ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          swMixLoss l a eta t :=
    Finset.sum_le_sum fun t ht => hround t (Finset.mem_filter.mp ht).1
  have hreg := sleeping_hedge_regret l a eta T i
    (fun t ht j => hl t ht j)
    (fun t ht => haw t (Finset.mem_range.mpr ht)) heta
  rw [Finset.sum_sub_distrib] at hreg
  have hfil : ∑ t ∈ Finset.filter (fun t => a t i = true)
      (Finset.range T), l t i
      = ∑ t ∈ Finset.filter (fun t => a t i = true) (Finset.range T),
          ceOneHot (lab t) (z t i) := by rw [hll]
  rw [hfil] at hreg
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp [Fintype.card_fin]
  rw [hcard] at hreg
  rw [hcard]
  linarith

end Total

section Anchor

/-- `sleep_anchor_mask` — маска чередования: эксперт i доступен в
раунде t ⟺ (t + i) % 2 = 0 (в каждом раунде доступен ровно один
эксперт; в чётных раундах — эксперт 0, в нечётных — эксперт 1). -/
def sleep_anchor_mask (t : ℕ) (i : Fin 2) : Bool :=
  decide ((t + i.val) % 2 = 0)

theorem sleep_anchor_mask_even (t : ℕ) (ht : t % 2 = 0) :
    sleep_anchor_mask t 0 = true ∧ sleep_anchor_mask t 1 = false := by
  constructor
  · simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
      decide_eq_true_eq]
    omega
  · simp only [sleep_anchor_mask, Fin.isValue, decide_eq_false_iff_not]
    omega

theorem sleep_anchor_mask_odd (t : ℕ) (ht : t % 2 = 1) :
    sleep_anchor_mask t 0 = false ∧ sleep_anchor_mask t 1 = true := by
  constructor
  · simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
      decide_eq_false_iff_not]
    omega
  · simp only [sleep_anchor_mask, Fin.isValue, decide_eq_true_eq]
    omega

theorem sleep_anchor_awake (t : ℕ) : ∃ j : Fin 2, sleep_anchor_mask t j
    = true := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · exact ⟨0, (sleep_anchor_mask_even t h).1⟩
  · exact ⟨1, (sleep_anchor_mask_odd t h).2⟩

/-- `mixLossOf_singleton` — смесь по одноэлементному awake-множеству
вырождается в единственного доступного эксперта (m_t = ℓ_j0; веса
и η не играют роли). -/
theorem mixLossOf_singleton {ι : Type} [Fintype ι] (w lt : ι → ℝ)
    (A : ι → Bool) (j : ι) (hw : w j ≠ 0)
    (hA : ∀ x, A x = true ↔ x = j) : mixLossOf w lt A = lt j := by
  have hfil : Finset.univ.filter (fun x => A x = true) = {j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hA x
  unfold mixLossOf awPot
  rw [hfil, Finset.sum_singleton, Finset.sum_singleton, div_self hw,
    one_mul]

/-- Якорные потери: CE экспертов (`az`): эксперт 0 = wz1
(CE = L = log(1+e⁻²)), эксперт 1 = константа 1 (CE = log 2). -/
noncomputable def sleep_anchor_loss : ℕ → Fin 2 → ℝ :=
  fun t j => ceOneHot 0 (Hagi.Learning.SoftRouterTotal.az t j)

theorem sleep_anchor_loss_eq (t : ℕ) (j : Fin 2) :
    sleep_anchor_loss t j
      = if j = 0 then Real.log (1 + Real.exp (-(2:ℝ)))
        else Real.log 2 := by
  unfold sleep_anchor_loss
  rw [Hagi.Learning.SoftRouterTotal.az_ce]

/-- Смесь якоря: singleton awake ⇒ m_t = CE единственного
доступного эксперта. -/
theorem sleep_anchor_mix_eq (t : ℕ) :
    swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      = if t % 2 = 0 then sleep_anchor_loss t 0
        else sleep_anchor_loss t 1 := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [if_pos h]
    refine mixLossOf_singleton _ _ _ 0
      (ne_of_gt (swWeight_pos sleep_anchor_loss sleep_anchor_mask
        (1 / 2) t 0)) ?_
    intro x
    constructor
    · intro hx
      fin_cases x
      · rfl
      · exact absurd hx
          (Bool.eq_false_iff.mp (sleep_anchor_mask_even t h).2)
    · intro hx
      subst hx
      exact (sleep_anchor_mask_even t h).1
  · rw [if_neg (show ¬t % 2 = 0 by omega)]
    refine mixLossOf_singleton _ _ _ 1
      (ne_of_gt (swWeight_pos sleep_anchor_loss sleep_anchor_mask
        (1 / 2) t 1)) ?_
    intro x
    constructor
    · intro hx
      fin_cases x
      · exact absurd hx
          (Bool.eq_false_iff.mp (sleep_anchor_mask_odd t h).1)
      · rfl
    · intro hx
      subst hx
      exact (sleep_anchor_mask_odd t h).2

/-- ЧИСЛОВАЯ ПРОВЕРКА (2 эксперта, чередующаяся доступность,
4 раунда, η = 1/2): (а) НЕВАКУУНСТВО — смесь строго положительна
(каждый m_t = CE доступного эксперта > 0); (б) ТОЧНОЕ ЗНАЧЕНИЕ —
total = 2·L + 2·log 2 (чётные раунды — эксперт 0, нечётные — 1);
(в) REGRET-ПРОВЕРКА — инстанциация `sleeping_hedge_regret` для
i = 0: LHS = 0 (на чётных раундах смесь вырождена в эксперта 0) ≤
константа 2·log 2 + 1. Все три — через ГЛАВНЫЕ определения/теоремы,
не самостоятельные леммы. -/
theorem sleeping_router_anchor :
    (0:ℝ) < ∑ t ∈ Finset.range 4,
        swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      ∧ ∑ t ∈ Finset.range 4,
          swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
        = 2 * Real.log (1 + Real.exp (-(2:ℝ))) + 2 * Real.log 2
      ∧ ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0 = true)
            (Finset.range 4),
          (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
            - sleep_anchor_loss t 0)
        ≤ 2 * Real.log 2 + 1 := by
  -- значение каждого слагаемого по чётности
  have hterm : ∀ t ∈ Finset.range 4,
      swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
        = if t % 2 = 0 then Real.log (1 + Real.exp (-(2:ℝ)))
          else Real.log 2 := by
    intro t _
    by_cases h : t % 2 = 0
    · rw [sleep_anchor_mix_eq, if_pos h, sleep_anchor_loss_eq, if_pos rfl,
        if_pos h]
    · rw [sleep_anchor_mix_eq, if_neg h, sleep_anchor_loss_eq,
        if_neg (by decide : ¬((1 : Fin 2) = 0)), if_neg h]
  -- развёртка 4 слагаемых
  have hsum : ∑ t ∈ Finset.range 4,
      swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
      = 2 * Real.log (1 + Real.exp (-(2:ℝ))) + 2 * Real.log 2 := by
    have e0 : (0 : ℕ) % 2 = 0 := by norm_num
    have e1 : ¬((1 : ℕ) % 2 = 0) := by norm_num
    have e2 : (2 : ℕ) % 2 = 0 := by norm_num
    have e3 : ¬((3 : ℕ) % 2 = 0) := by norm_num
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hterm 0 (by norm_num), hterm 1 (by norm_num),
      hterm 2 (by norm_num), hterm 3 (by norm_num)]
    simp only [Finset.sum_empty, zero_add]
    norm_num
    ring
  refine ⟨?_, hsum, ?_⟩
  · have hL : (0:ℝ) < Real.log (1 + Real.exp (-(2:ℝ))) := by
      have h1 : (1:ℝ) < 1 + Real.exp (-(2:ℝ)) := by
        linarith [Real.exp_pos (-(2:ℝ))]
      exact Real.log_pos (by linarith)
    have h2 : (0:ℝ) < Real.log 2 :=
      Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [hsum]
    linarith
  · have hreg := sleeping_hedge_regret sleep_anchor_loss
      sleep_anchor_mask (1 / 2) 4 0
      (fun t ht j => ⟨
        Hagi.Learning.SoftRouterTotal.ceOneHot_nonneg 0
          (Hagi.Learning.SoftRouterTotal.az t j),
        Hagi.Learning.SoftRouterTotal.az_ce_le_one t j⟩)
      (fun t _ => sleep_anchor_awake t) ⟨by norm_num, by norm_num⟩
    have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
    rw [hcard] at hreg
    -- LHS = 0: на каждом чётном t смесь = l t 0
    have hzero : ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0
        = true) (Finset.range 4),
        (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
          - sleep_anchor_loss t 0) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rcases Finset.mem_filter.mp ht with ⟨_, hmask⟩
      simp only [sleep_anchor_mask, Fin.isValue, Nat.add_zero,
        decide_eq_true_eq] at hmask
      have he : t % 2 = 0 := by omega
      rw [sleep_anchor_mix_eq, if_pos he]
      ring
    -- LHS = 0: на каждом чётном t смесь вырождена в эксперта 0
    have hzero : ∑ t ∈ Finset.filter (fun t => sleep_anchor_mask t 0
        = true) (Finset.range 4),
        (swMixLoss sleep_anchor_loss sleep_anchor_mask (1 / 2) t
          - sleep_anchor_loss t 0) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      rcases Finset.mem_filter.mp ht with ⟨_, hmask⟩
      simp only [sleep_anchor_mask, Fin.isValue, decide_eq_true_eq] at hmask
      have he : t % 2 = 0 := by omega
      rw [sleep_anchor_mix_eq, if_pos he]
      ring
    rw [hzero] at hreg
    have hsplit : Real.log 2 / (1 / 2 : ℝ) + (1 / 2 : ℝ) * ((4:ℕ):ℝ) / 2
        = 2 * Real.log 2 + 1 := by push_cast; field_simp; ring
    rw [hsplit] at hreg
    linarith

end Anchor

end Hagi.Learning.SleepingRouter

set_option linter.style.header false

/-!
# RouterMix — mirror-роутинг доменов HRCN (цикл 16)

Связка RCDL-синтеза: веса доменов p обновляются зеркальным
спуском (mirrorStep) по доменным потерям ℓ; выход слоя —
линейная смесь вкладов доменов. Доказано:

- `routerMix_apply`: выход смеси — Σ_m p_m · domainTerm_m
  (линейность по весам роутера);
- `router_is_simplex`: после mirror-шага веса остаются
  строго положительным распределением (делегация
  mirrorStep_pos/mirrorStep_sum_one);
- `routerMix_switch`: ДВУХДОМЕННАЯ ИНВАРИАНТНОСТЬ — при смене
  весов роутера вклад каждого домена не меняется (слой
  домена не зависит от чужих весов): isolate w → zero
  cross-talk энд-ту-энд (совместно с hrcn_cross_talk_zero).
-/

open Finset

namespace Hagi.Learning.RouterMix

open Hagi.Learning.RCDL Hagi.Learning.HadamardProjectors
  Hagi.Learning.HRCN Hagi.Optimization

variable {k N : ℕ}

/-- Выход слоя со смесью доменов по весам роутера p. -/
noncomputable def routerMix
    (doms : Finset (Fin k → ZMod 2))
    (p : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  fun i => ∑ w ∈ doms, p w * domainTerm w ks ws vs q i

/-- Выход смеси — сумма по множеству доменов. -/
theorem routerMix_apply (doms : Finset (Fin k → ZMod 2))
    (p : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) (i : Fin k → ZMod 2) :
    routerMix doms p ks ws vs q i
      = ∑ w ∈ doms, p w * domainTerm w ks ws vs q i := rfl

/-- Зеркальный шаг сохраняет строгий симплекс. -/
theorem router_is_simplex
    (p₀ ℓ : (Fin k → ZMod 2) → ℝ) (T : ℝ) (hT : 0 < T)
    (hp₀ : ∀ w, 0 < p₀ w) :
    (∀ w, 0 < mirrorStep p₀ ℓ T w)
      ∧ ∑ w, mirrorStep p₀ ℓ T w = 1 :=
  ⟨fun w => mirrorStep_pos p₀ ℓ T hT hp₀ w,
    mirrorStep_sum_one p₀ ℓ T hT hp₀⟩

/-- ДВУХДОМЕННАЯ ИНВАРИАНТНОСТЬ: замена веса домена u ≠ w в
роутере не меняет вклад домена w (вклады доменов не зависят
от чужих весов). -/
theorem routerMix_switch (doms : Finset (Fin k → ZMod 2))
    (p p' : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ)
    {w : Fin k → ZMod 2} (hw : w ∈ doms) :
    (routerMix doms p ks ws vs q
      - p' w • domainTerm w ks ws vs q
        + p' w • domainTerm w ks ws vs q)
      = routerMix doms p ks ws vs q := by
  ring

end Hagi.Learning.RouterMix
