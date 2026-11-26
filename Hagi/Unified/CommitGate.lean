import Mathlib.Tactic
import Hagi.Energy.Quantizer
import Hagi.Cert.StepGen

/-!
# CommitGate: инвариант
ветвления вместо постулата h_emp_grow.

Главная идея: условие продуктивности шага НЕ
внешняя гипотеза, а РЕШИМОЕ неравенство внутри алгоритма:
commit разрешён ⟺ выигрыш (спуск + зазор ансамбля)
строго перекрывает издержки (квантование + обобщение).

Компоненты (все с честными источниками):
- `dStep` — контракт локального спуска (Dust/SafeQP-
  аналог: ≥ c·‖∇L‖² − σ²/K; сглаживание-гипотеза контракта
  — её производит DescentCore-инстанс);
- `gap` — зазор Йенсена ансамбля (twoGap ≥ 0, Ensemble);
- `quant` — ошибка квантования (≤ Δ/2, gridQ_error);
- `gen` — граница обобщения (PAC-Bayes/Catoni, ≥ 0).

Теоремы:
1. `commitProductive`: gate = true (win > loss) ⟹
   потенциал СТРОГО убывает после commit;
2. `holdSafe`: gate = false ⟹ rollback сохраняет потенциал
   (parent-preserving: Δ = 0);
3. `gate_decidable`: условие разрешимо (вычислимый if
   внутри алгоритма — инвариант ветвления, не гипотеза).
-/

namespace Hagi.Unified.CommitGate

open Hagi.Energy

/-- Сертификат компонент макро-шага (все источники
честные: контракты + вычисляемые величины). -/
structure GateCert where
  /-- Текущий потенциал (loss/energy). -/
  V : ℝ
  /-- Выигрыш спуска (контракт DescentCore-инстанса). -/
  dStep : ℝ
  /-- Зазор ансамбля (twoGap, ≥ 0). -/
  gap : ℝ
  hgap : 0 ≤ gap
  /-- Ошибка квантования решётки (вычислена, ≤ Δ/2). -/
  quant : ℝ
  /-- Граница обобщения (PAC-Bayes, ≥ 0). -/
  gen : ℝ
  hgen : 0 ≤ gen

/-- Вычислимое условие commit: выигрыш строго больше
издержек. -/
def gate (c : GateCert) : Prop := c.dStep + c.gap > c.quant + c.gen

variable (c : GateCert)



/-- Потенциал после commit: выигрыш применяется, издержки
вычитаются. -/
def commitV (c : GateCert) : ℝ :=
  c.V - (c.dStep + c.gap) + (c.quant + c.gen)

/-- Потенциал после rollback: неизменен (parent-preserving
lift / накопление без commit). -/
def holdV (c : GateCert) : ℝ := c.V

/-- ВЫЧИСЛИМОЕ РЕШЕНИЕ: gate — не только
Prop, но и разрешимое условие: решение commit/rollback
ВЫЧИСЛЯЕТСЯ из измеренных компонент (инвариант ветвления
внутри алгоритма, не внешняя гипотеза). -/
noncomputable instance : Decidable (gate c) :=
  Real.decidableLT _ _

/-- Процедура решения контроллера: Bool-команда
commit (true) / rollback (false), вычисляемая из
GateCert (над ℝ — noncomputable в Lean, но семантически
однозначная функция решения). Согласована с Prop-формой
в обе стороны. -/
noncomputable def gateDecision (c : GateCert) : Bool :=
  decide (gate c)

/-- Корректность процедуры: gateDecision = true ⟺ gate. -/
theorem gateDecision_iff (c : GateCert) :
    gateDecision c = true ↔ gate c := by
  simp [gateDecision]

/-- КОММИТ ПРОДУКТИВЕН: gate = true ⟹ потенциал строго
убывает (h_emp_grow заменён вычислимым ветвлением). -/
theorem commitProductive (c : GateCert) (h : gate c) :
    commitV c < c.V := by
  unfold commitV gate at *
  linarith

/-- ROLLBACK БЕЗОПАСЕН: gate = false ⟹ потенциал сохранён
точно (нулевая деградация, parent-preserving). -/
theorem holdSafe (c : GateCert) : holdV c = c.V := rfl

/-- СВЯЗЬ С РЕШЁТКОЙ: если quant вычислен как gridQ-ошибка
(Δ-решётка, норма Фробениуса-аналог через сумму
поточечных), то quant ≤ n·Δ²/4 — издержка квантования
ограничена решёткой (реюз gridQ_error поточечно). -/
theorem quant_bound_of_gridQ (delta : ℝ) (hdelta : 0 < delta)
    {k : Type*} [Fintype k] (w : k → ℝ) :
    (∑ i, (gridQ delta hdelta (w i) - w i)^2) ≤
      (Fintype.card k) * delta^2 / 4 := by
  have h1 : ∀ i : k, (gridQ delta hdelta (w i) - w i)^2
      ≤ (delta / 2)^2 := by
    intro i
    have h := gridQ_error delta hdelta (w i)
    have hnn : (0:ℝ) ≤ delta / 2 :=
      div_nonneg (le_of_lt hdelta) (by norm_num)
    exact sq_le_sq.mpr (h.trans (le_of_eq
      (abs_of_nonneg hnn).symm))
  have hsum : ∑ i : k, (delta/2)^2
      = (Fintype.card k) * (delta/2)^2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  calc ∑ i : k, (gridQ delta hdelta (w i) - w i)^2
      ≤ ∑ i : k, (delta/2)^2 :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = (Fintype.card k) * (delta/2)^2 := hsum
    _ = (Fintype.card k) * delta^2 / 4 := by
      have hq : (delta/2)^2 = delta^2/4 := by rw [div_pow]; norm_num
      rw [hq]
      ring

/-! ### Адаптер: GateCert → общее ядро CertStepGen

Гейт коммита — view над общим
ядром `Hagi.Cert.CertStepGen`. Носитель БЕЗСОСТОЯТЕЛЕН (V —
число, не состояние): состояния и выравнивание метрик даёт
потребитель (`hobj`/`hobj'`). Содержание адаптера — ветвление
gate ⟹ СТРОГИЙ дроп (commitProductive в форме ядра). Риск-
понятия в носителе нет — `riskRem` СВОБОДНЫЙ параметр с
посылками (без молчаливого 0); структурное слияние гейта в
Loop-слой — отдельный бит. -/

/-- коммит-ветвь гейта как шаг общего ядра (premise-form:
`hgate` даёт строгий дроп; выравнивание потенциала — посылки). -/
noncomputable def GateCert.toCertStepGen {S TaskId : Type*}
    (c : GateCert) (hgate : gate c)
    (M : Hagi.Cert.SystemMetrics S TaskId) (s s' : S)
    (hobj : M.objective s = c.V)
    (hobj' : M.objective s' = commitV c)
    {bs b' rs riskRem : ℝ}
    (hbud : M.budget s = b' + bs) (hbud' : M.budget s' = b')
    (hbudnn : 0 ≤ b')
    (hrisk : M.risk s = rs + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl (fun _ => 0) s s' where
  drop := c.dStep + c.gap - (c.quant + c.gen)
  drop_pos := by
    unfold gate at hgate
    linarith
  descent := by
    rw [hobj, hobj']
    unfold commitV
    linarith
  budgetSpend := bs
  budget_next := by rw [hbud, hbud']; linarith
  budget_nonneg := by rw [hbud']; exact hbudnn
  riskSpend := rs
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := 0
  delta_next := by simp
  delta_nonneg := by norm_num
  floorsKept := hfloors

end Hagi.Unified.CommitGate
