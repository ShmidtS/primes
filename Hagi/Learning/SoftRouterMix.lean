/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat

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
