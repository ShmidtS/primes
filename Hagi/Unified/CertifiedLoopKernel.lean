import Mathlib.Tactic
import Hagi.Unified.CertifiedLoop
import Hagi.Cert.StepGen

/-!
# CertifiedLoopKernel — капстон на общем ядре (C345, A14 QW4+QW5)

Капстон `certified_loop` переформулирован над цепями
`Hagi.Cert.CertStepGenBounded` общего ядра (`TaskId` произвольный —
жёсткий `Fin 5` цикла не нужен), legacy-носители — premise-free
view:

* `certified_loop_kernel` — КАПСТОН НА ЯДРЕ: bounded-цепь даёт
  одновременно кумулятивный спуск ≥ Σ drops, ядерный floor,
  неотрицательный бюджет, бюджетный телескоп, риск- и δ-леджери;
* мост на ℕ × S (`bridgeMetrics`/`bridgeObl`/`legacy_chain`):
  траектория `StepCert` погружается в ядерную цепь БЕЗ посылок
  hbudeq/hrisk/hrisk'/hfloors C278-адаптера (C344 bounded-маршрут;
  riskLim ≥ 0 ВЫВОДИТСЯ из riskBound + неотрицательности траты);
* `certified_loop_eq_kernel` — заключения legacy `certified_loop`
  ВЫВЕДЕНЫ из ядерного капстона (+ риск-агрегация как бонус);
  формулировка legacy капстона НЕ изменена (Freeze).

Честные границы: ядерный floor — floor на ОБЪЕКТИВЕ; измеримое
качество `FloorKept` цикла — канал исполнения, восстановлен
отдельной индукцией `legacy_quality` (не подменяется ядерным).
QW4 (HonestTransition → kernel view) — не дёшево: HonestTransition
не несёт бюджетного закона вовсе (только 0 ≤ b') — следующий бит.
-/

namespace Hagi.Unified.CertifiedLoopKernel

open Hagi.Cert Hagi.Unified.CertifiedLoop Hagi.Unified.LinkedQVec

variable {S TaskId : Type*}
variable (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)

/-! ## Ядерный капстон (bounded-цепь, Fin n, TaskId произвольный) -/

/-- Ядро капстона (спуск/floor/бюджет), индукция по длине цепи. -/
theorem kernel_core {deltaLevel : S → ℝ}
    (n : ℕ) (t : ℕ → S)
    (hfloor0 : FloorsKept M obl (t 0)) (hb0 : 0 ≤ M.budget (t 0))
    (steps : ∀ j : Fin n, CertStepGenBounded M obl deltaLevel
      (t j.val) (t (j.val + 1)))
    (drops spends : ℕ → ℝ)
    (hdrops : ∀ j : Fin n, drops j.val = (steps j).drop)
    (hspends : ∀ j : Fin n, spends j.val = (steps j).budgetSpend) :
    ∑ j ∈ Finset.range n, drops j ≤ M.objective (t 0) - M.objective (t n)
      ∧ FloorsKept M obl (t n)
      ∧ 0 ≤ M.budget (t n)
      ∧ M.budget (t n) ≤ M.budget (t 0) - ∑ j ∈ Finset.range n, spends j := by
  revert steps hdrops hspends
  induction n with
  | zero =>
    intro _ _ _
    rw [Finset.sum_range_zero, Finset.sum_range_zero]
    exact ⟨by linarith, hfloor0, hb0, by linarith⟩
  | succ n ih =>
    intro steps hdrops hspends
    have hdrop := (steps (Fin.last n)).descent
    have hbd := (steps (Fin.last n)).budget_next_le
    have hq := (steps (Fin.last n)).floorsKept
    have hbb := (steps (Fin.last n)).budget_nonneg
    have hn1 : drops n = (steps (Fin.last n)).drop := hdrops (Fin.last n)
    have hn2 : spends n = (steps (Fin.last n)).budgetSpend :=
      hspends (Fin.last n)
    obtain ⟨h1, h2, h3, h4⟩ := ih
      (fun j => steps j.castSucc)
      (fun j => hdrops j.castSucc)
      (fun j => hspends j.castSucc)
    have hdrop2 : M.objective (t (n + 1))
        ≤ M.objective (t n) - (steps (Fin.last n)).drop := hdrop
    have hbd2 : M.budget (t (n + 1))
        ≤ M.budget (t n) - (steps (Fin.last n)).budgetSpend := hbd
    have hq2 : FloorsKept M obl (t (n + 1)) := hq
    have hbb2 : 0 ≤ M.budget (t (n + 1)) := hbb
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact ⟨by linarith, hq2, hbb2, by linarith⟩

/-- Риск-леджер, сильная форма: Σ трат ≤ начальный уровень − конечный. -/
theorem risk_ledger_fin {deltaLevel : S → ℝ} (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : Fin n, CertStepGenBounded M obl deltaLevel
      (t j.val) (t (j.val + 1)))
    (risks : ℕ → ℝ) (hrisks : ∀ j : Fin n, risks j.val = (steps j).riskSpend) :
    ∑ j ∈ Finset.range n, risks j ≤ M.risk (t 0) - M.risk (t n) := by
  revert steps hrisks
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro steps hrisks
    have e0 := (steps (Fin.last n)).risk_next_le
    have e : M.risk (t (n + 1))
        ≤ M.risk (t n) - (steps (Fin.last n)).riskSpend := e0
    have hr : risks n = (steps (Fin.last n)).riskSpend := hrisks (Fin.last n)
    have hrest := ih (fun j => steps j.castSucc) (fun j => hrisks j.castSucc)
    simp only [Finset.sum_range_succ]
    linarith

/-- δ-леджер, сильная форма. -/
theorem delta_ledger_fin {deltaLevel : S → ℝ} (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : Fin n, CertStepGenBounded M obl deltaLevel
      (t j.val) (t (j.val + 1)))
    (deltas : ℕ → ℝ)
    (hdeltas : ∀ j : Fin n, deltas j.val = (steps j).delta) :
    ∑ j ∈ Finset.range n, deltas j
      ≤ deltaLevel (t 0) - deltaLevel (t n) := by
  revert steps hdeltas
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
    intro steps hdeltas
    have e0 := (steps (Fin.last n)).delta_next_le
    have e : deltaLevel (t (n + 1))
        ≤ deltaLevel (t n) - (steps (Fin.last n)).delta := e0
    have hd : deltas n = (steps (Fin.last n)).delta := hdeltas (Fin.last n)
    have hrest := ih (fun j => steps j.castSucc) (fun j => hdeltas j.castSucc)
    simp only [Finset.sum_range_succ]
    linarith

/-- КАПСТОН НА ЯДРЕ: сертифицированная bounded-цепь общего ядра
(TaskId произвольный) даёт одновременно кумулятивный спуск,
ядерный floor, неотрицательный бюджет, бюджетный телескоп,
риск- и δ-леджери. Посылки hrisk0/hdelta0 — честные начальные
неотрицательности (как в `risk_telescope_gen`). -/
theorem certified_loop_kernel {deltaLevel : S → ℝ}
    (n : ℕ) (t : ℕ → S)
    (hfloor0 : FloorsKept M obl (t 0)) (hb0 : 0 ≤ M.budget (t 0))
    (hrisk0 : 0 ≤ M.risk (t 0)) (hdelta0 : 0 ≤ deltaLevel (t 0))
    (steps : ∀ j : Fin n, CertStepGenBounded M obl deltaLevel
      (t j.val) (t (j.val + 1)))
    (drops spends risks deltas : ℕ → ℝ)
    (hdrops : ∀ j : Fin n, drops j.val = (steps j).drop)
    (hspends : ∀ j : Fin n, spends j.val = (steps j).budgetSpend)
    (hrisks : ∀ j : Fin n, risks j.val = (steps j).riskSpend)
    (hdeltas : ∀ j : Fin n, deltas j.val = (steps j).delta) :
    ∑ j ∈ Finset.range n, drops j ≤ M.objective (t 0) - M.objective (t n)
      ∧ FloorsKept M obl (t n)
      ∧ 0 ≤ M.budget (t n)
      ∧ M.budget (t n) ≤ M.budget (t 0) - ∑ j ∈ Finset.range n, spends j
      ∧ ∑ j ∈ Finset.range n, risks j ≤ M.risk (t 0)
      ∧ ∑ j ∈ Finset.range n, deltas j ≤ deltaLevel (t 0) := by
  have hRiskNN : 0 ≤ M.risk (t n) := by
    match n with
    | 0 => exact hrisk0
    | m + 1 => exact (steps ⟨m, by omega⟩).risk_nonneg
  have hDeltaNN : 0 ≤ deltaLevel (t n) := by
    match n with
    | 0 => exact hdelta0
    | m + 1 => exact (steps ⟨m, by omega⟩).delta_nonneg
  obtain ⟨h1, h2, h3, h4⟩ := kernel_core M obl n t hfloor0 hb0 steps drops spends
    hdrops hspends
  have hr := risk_ledger_fin M obl n t steps risks hrisks
  have hd := delta_ledger_fin M obl n t steps deltas hdeltas
  exact ⟨h1, h2, h3, h4, by linarith, by linarith⟩

/-! ## Мост: legacy-траектория → ядерная цепь (premise-free) -/

variable {S : Type*}

/-- Монотонность объективы вдоль legacy-цепи: obj не возрастает
(следствие actualDescent каждого шага), без ядра. -/
theorem legacy_obj_anti (obj : S → ℝ) (Mm : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    (certs : ∀ t : Fin n,
      StepCert obj Mm floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (drops : ℕ → ℝ)
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop) :
    ∀ k m, k ≤ m → m ≤ n → obj (f m) ≤ obj (f k) := by
  intro k m hkm hmn
  induction m generalizing k with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp hkm
    subst hk
    exact le_refl _
  | succ m ih =>
    match Nat.lt_or_ge k (m + 1) with
    | .inr hge =>
      have hk : k = m + 1 := Nat.le_antisymm hkm hge
      subst hk
      exact le_refl _
    | .inl hlt =>
      have desc0 := (certs ⟨m, by omega⟩).trans.actualDescent
      have desc : obj (f (m + 1))
          ≤ obj (f m) - (certs ⟨m, by omega⟩).trans.objectiveDrop := desc0
      have hdp : 0 < (certs ⟨m, by omega⟩).trans.objectiveDrop :=
        (certs ⟨m, by omega⟩).trans.objectiveDrop_pos
      have hprev : obj (f m) ≤ obj (f k) :=
        ih k (show k ≤ m by omega) (show m ≤ n by omega)
      linarith

/-- Ядерные носители моста: состояние = (время, состояние цикла);
бюджет читается по времени, риск-носитель — остаток лимита,
объективна — объективна цикла. -/
def bridgeMetrics (obj : S → ℝ) (b : ℕ → ℝ) (riskLim : ℝ) (n : ℕ) :
    SystemMetrics (ℕ × S) Unit where
  objective p := obj p.2
  risk p := ((n - p.1 : ℕ) : ℝ) * riskLim
  budget p := b p.1
  task _ := ()

/-- Ядерные обязательства моста: floor = obj терминального состояния
(держится монотонностью цепи — premise-free). -/
def bridgeObl (obj : S → ℝ) (x : S) : StepObligations Unit where
  floor _ := obj x

/-- Один legacy-шаг как bounded-шаг ядра на носителях моста:
посылок hbudeq/hrisk/hrisk'/hfloors НЕТ — нестрогих законов
StepCert достаточно (C344), риск-носитель и floor держатся
следствиями самого StepCert. -/
def stepCert_to_kernel_bounded (obj : S → ℝ) (Mm : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    {j : ℕ} (hj : j < n)
    (hstep : StepCert obj Mm floor riskLim (f j) (f (j + 1))
      (b j) (b (j + 1)))
    (hmono : obj (f n) ≤ obj (f (j + 1))) :
    CertStepGenBounded (bridgeMetrics obj b riskLim n)
      (bridgeObl obj (f n)) (fun _ => (0:ℝ))
      (j, f j) (j + 1, f (j + 1)) where
  drop := hstep.trans.objectiveDrop
  drop_pos := hstep.trans.objectiveDrop_pos
  descent := hstep.trans.actualDescent
  budgetSpend := hstep.budgetSpend
  budget_next_le := hstep.hdec
  budget_nonneg := hstep.trans.budgetBound
  riskSpend := hstep.riskSpend
  risk_next_le := by
    show ((n - (j + 1) : ℕ) : ℝ) * riskLim
      ≤ ((n - j : ℕ) : ℝ) * riskLim - hstep.riskSpend
    have hrl : 0 ≤ riskLim := by
      have h1 := hstep.hriskSpend_nn
      have h2 := hstep.trans.riskBound
      linarith
    have hc : ((n - j : ℕ) : ℝ) = ((n - (j + 1) : ℕ) : ℝ) + 1 := by
      have h1 : (n - j : ℕ) = (n - (j + 1) : ℕ) + 1 := by omega
      rw [h1]
      push_cast
      ring
    have hrb := hstep.trans.riskBound
    rw [hc]
    linarith
  risk_nonneg := by
    show 0 ≤ ((n - (j + 1) : ℕ) : ℝ) * riskLim
    have hrl : 0 ≤ riskLim := by
      have h1 := hstep.hriskSpend_nn
      have h2 := hstep.trans.riskBound
      linarith
    exact mul_nonneg (Nat.cast_nonneg _) hrl
  delta := 0
  delta_next_le := by simp
  delta_nonneg := by norm_num
  floorsKept := by
    intro _
    exact hmono

/-- Траекторный мост: вся legacy-цепь Fin n — ядерная bounded-цепь
на носителях моста (TaskId = Unit, состояние ℕ × S). -/
def legacy_chain (obj : S → ℝ) (Mm : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ) (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    (certs : ∀ t : Fin n,
      StepCert obj Mm floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (drops : ℕ → ℝ)
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop) (j : Fin n) :
    CertStepGenBounded (bridgeMetrics obj b riskLim n)
      (bridgeObl obj (f n)) (fun _ => (0:ℝ))
      (j.val, f j.val) (j.val + 1, f (j.val + 1)) :=
  stepCert_to_kernel_bounded obj Mm floor riskLim f b n j.isLt
    (certs ⟨j.val, j.isLt⟩)
    (legacy_obj_anti obj Mm floor riskLim f b n certs drops hdrops
      (j.val + 1) n (Nat.succ_le_of_lt j.isLt) (Nat.le_refl _))

/-- ГЛАВНЫЙ МОСТ: заключения `certified_loop` ВЫВЕДЕНЫ из ядерного
капстона `certified_loop_kernel` через `legacy_chain` (плюс
риск-леджер — бонус ядра). Формулировка legacy капстона не
изменена (Freeze): это ОТДЕЛЬНАЯ теорема, доказательство которой
не использует legacy `certified_loop`. -/
theorem certified_loop_eq_kernel (obj : S → ℝ) (Mm : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b drops spends : ℕ → ℝ) (n : ℕ)
    (h₀ : FloorKept Mm (f 0) floor) (hb₀ : 0 ≤ b 0)
    (certs : ∀ t : Fin n,
      StepCert obj Mm floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop)
    (hspends : ∀ t : Fin n,
      spends t.val = (certs t).budgetSpend) :
    ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n)
      ∧ FloorKept Mm (f n) floor
      ∧ 0 ≤ b n
      ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, spends t
      ∧ ∑ t : Fin n, (certs t).riskSpend ≤ (n : ℝ) * riskLim := by
  have hanti := legacy_obj_anti obj Mm floor riskLim f b n certs drops hdrops
  have hf0 : Hagi.Cert.FloorsKept (bridgeMetrics obj b riskLim n)
      (bridgeObl obj (f n)) (0, f 0) := by
    intro _
    show obj (f n) ≤ obj (f 0)
    exact hanti 0 n (Nat.zero_le _) (Nat.le_refl _)
  have hb0 : 0 ≤ (bridgeMetrics obj b riskLim n).budget (0, f 0) := hb₀
  have hr0 : 0 ≤ (bridgeMetrics obj b riskLim n).risk (0, f 0) := by
    show 0 ≤ ((n - 0 : ℕ) : ℝ) * riskLim
    match n with
    | 0 => simp
    | m + 1 =>
      have h1 := (certs ⟨0, by omega⟩).hriskSpend_nn
      have h2 := (certs ⟨0, by omega⟩).trans.riskBound
      have hrl : 0 ≤ riskLim := by linarith
      exact mul_nonneg (by positivity) hrl
  have hdelta0 : (0:ℝ) ≤ (fun _ : ℕ × S => (0:ℝ)) (0, f 0) := le_refl _
  have hdrops' : ∀ j : Fin n, drops j.val
      = (legacy_chain obj Mm floor riskLim f b n certs drops hdrops j).drop :=
    fun j => hdrops j
  have hspends' : ∀ j : Fin n, spends j.val
      = (legacy_chain obj Mm floor riskLim f b n certs drops hdrops j).budgetSpend :=
    fun j => hspends j
  have hdeltas : ∀ j : Fin n,
      (fun _ : ℕ => (0:ℝ)) j.val
        = (legacy_chain obj Mm floor riskLim f b n certs drops hdrops j).delta :=
    fun _ => rfl
  have hriskfun : ∀ t : Fin n,
      (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t.val
        = (legacy_chain obj Mm floor riskLim f b n certs drops hdrops t).riskSpend := by
    intro t
    show dite (t.val < n) (fun h => (certs ⟨t.val, h⟩).riskSpend)
      (fun _ => (0:ℝ)) = _
    split
    · rfl
    · exact absurd t.isLt (by assumption)
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ :=
    certified_loop_kernel (bridgeMetrics obj b riskLim n)
      (bridgeObl obj (f n)) n (fun j => (j, f j)) hf0 hb0 hr0 hdelta0
      (legacy_chain obj Mm floor riskLim f b n certs drops hdrops) drops spends
      (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ))
      (fun _ => (0:ℝ)) hdrops' hspends' hriskfun hdeltas
  have hq : FloorKept Mm (f n) floor := by
    induction n with
    | zero => exact h₀
    | succ m _ => exact (certs (Fin.last m)).quality
  refine ⟨?_, hq, k3, k4, ?_⟩
  · show ∑ t ∈ Finset.range n, drops t ≤ obj (f 0) - obj (f n)
    exact k1
  · have hsum2 : ∑ t : Fin n, (certs t).riskSpend
        = ∑ t : Fin n,
          (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t.val :=
      Finset.sum_congr rfl
        (fun t _ => by rw [hriskfun t]; rfl)
    have hsum : ∑ t : Fin n,
          (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t.val
        = ∑ t ∈ Finset.range n,
          (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t :=
      Fin.sum_univ_eq_sum_range
        (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) n
    show ∑ t : Fin n, (certs t).riskSpend ≤ (n : ℝ) * riskLim
    rw [hsum2, hsum]
    show ∑ t ∈ Finset.range n,
        (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t
      ≤ ((n - 0 : ℕ) : ℝ) * riskLim
    have h5 : ∑ t ∈ Finset.range n,
        (fun k => if h : k < n then (certs ⟨k, h⟩).riskSpend else (0:ℝ)) t
      ≤ ((n - 0 : ℕ) : ℝ) * riskLim := k5
    rw [Nat.sub_zero] at h5
    exact h5

end Hagi.Unified.CertifiedLoopKernel

/-! ## Числовой якорь через ядро -/

namespace Hagi.Unified.CertifiedLoopKernel

open Hagi.Cert

/-- Объектива якоря: w². -/
private noncomputable def anchorObj : ℝ → ℝ := fun w => w * w

/-- Траектория якоря: 2 → 1 → 1/2. -/
private noncomputable def anchorW : ℕ → ℝ := fun j => if j = 0 then 2 else if j = 1 then 1 else 1 / 2

/-- Бюджет якоря: 10 → 9 → 17/2. -/
private noncomputable def anchorB : ℕ → ℝ := fun j => if j = 0 then 10 else if j = 1 then 9 else 15 / 2

/-- Носители моста якоря (riskLim = 1, n = 2). -/
private noncomputable def anchorKm : SystemMetrics (ℕ × ℝ) Unit :=
  bridgeMetrics anchorObj anchorB 1 2

private noncomputable def anchorObl : StepObligations Unit := bridgeObl anchorObj (1 / 2)

/-- Шаг 0 якоря: 2 → 1, drop 3, spend 1, risk 1. -/
private noncomputable def anchorStep0 : CertStepGenBounded anchorKm anchorObl (fun _ => (0:ℝ))
    (0, anchorW 0) (1, anchorW 1) where
  drop := 3
  drop_pos := by norm_num
  descent := by show anchorObj (anchorW 1) ≤ anchorObj (anchorW 0) - 3; norm_num [anchorObj, anchorW]
  budgetSpend := 1
  budget_next_le := by show anchorB 1 ≤ anchorB 0 - 1; norm_num [anchorB]
  budget_nonneg := by show 0 ≤ anchorB 1; norm_num [anchorB]
  riskSpend := 1
  risk_next_le := by show ((2 - 1 : ℕ) : ℝ) * 1 ≤ ((2 - 0 : ℕ) : ℝ) * 1 - 1; norm_num
  risk_nonneg := by show 0 ≤ ((2 - 1 : ℕ) : ℝ) * 1; norm_num
  delta := 0
  delta_next_le := by simp
  delta_nonneg := by norm_num
  floorsKept := fun _ => by show anchorObj (1/2) ≤ anchorObj (anchorW 1); norm_num [anchorObj, anchorW]

/-- Шаг 1 якоря: 1 → 1/2, drop 3/4, spend 3/2, risk 0. -/
private noncomputable def anchorStep1 : CertStepGenBounded anchorKm anchorObl (fun _ => (0:ℝ))
    (1, anchorW 1) (2, anchorW 2) where
  drop := 3 / 4
  drop_pos := by norm_num
  descent := by show anchorObj (anchorW 2) ≤ anchorObj (anchorW 1) - 3 / 4; norm_num [anchorObj, anchorW]
  budgetSpend := 3 / 2
  budget_next_le := by show anchorB 2 ≤ anchorB 1 - 3 / 2; norm_num [anchorB]
  budget_nonneg := by show 0 ≤ anchorB 2; norm_num [anchorB]
  riskSpend := 0
  risk_next_le := by show ((2 - 2 : ℕ) : ℝ) * 1 ≤ ((2 - 1 : ℕ) : ℝ) * 1 - 0; norm_num
  risk_nonneg := by show 0 ≤ ((2 - 2 : ℕ) : ℝ) * 1; norm_num
  delta := 0
  delta_next_le := by simp
  delta_nonneg := by norm_num
  floorsKept := fun _ => by show anchorObj (1/2) ≤ anchorObj (anchorW 2); norm_num [anchorObj, anchorW]

private noncomputable def anchorChain : ∀ j : Fin 2, CertStepGenBounded anchorKm anchorObl
    (fun _ => (0:ℝ))
    ((j : ℕ), anchorW (j : ℕ)) ((j : ℕ) + 1, anchorW ((j : ℕ) + 1))
  | 0 => anchorStep0
  | 1 => anchorStep1

/-- Числовой якорь: траектория 2 → 1 → 1/2 (obj w = w²),
бюджет 10 → 9 → 17/2, riskLim = 1. Ядерный капстон даёт ТЕСНЫЕ
неравенства (оба — равенства). -/
theorem kernel_anchor_quad :
    (3 + 3 / 4 : ℝ) ≤ anchorObj (anchorW 0) - anchorObj (anchorW 2)
      ∧ (15 / 2 : ℝ) ≤ 10 - (1 + 3 / 2) := by
  have hf0 : FloorsKept anchorKm anchorObl (0, anchorW 0) :=
    fun _ => by show anchorObj (1/2) ≤ anchorObj (anchorW 0); norm_num [anchorObj, anchorW]
  have hb0 : 0 ≤ anchorKm.budget (0, anchorW 0) := by
    show 0 ≤ anchorB 0; norm_num [anchorB]
  have hr0 : 0 ≤ anchorKm.risk (0, anchorW 0) := by
    show 0 ≤ ((2 - 0 : ℕ) : ℝ) * 1; norm_num
  have hdelta0 : (0:ℝ) ≤ (fun _ : ℕ × ℝ => (0:ℝ)) (0, anchorW 0) := le_refl _
  have hdrops : ∀ j : Fin 2,
      (fun _ : ℕ => (if (j:ℕ) = 0 then (3:ℝ) else 3 / 4)) j.val
        = (anchorChain j).drop := by
    intro j
    match j with
    | 0 => rfl
    | 1 => rfl
  have hspends : ∀ j : Fin 2,
      (fun _ : ℕ => (if (j:ℕ) = 0 then (1:ℝ) else 3 / 2)) j.val
        = (anchorChain j).budgetSpend := by
    intro j
    match j with
    | 0 => rfl
    | 1 => rfl
  have hrisks : ∀ j : Fin 2,
      (fun _ : ℕ => (if (j:ℕ) = 0 then (1:ℝ) else 0)) j.val
        = (anchorChain j).riskSpend := by
    intro j
    match j with
    | 0 => rfl
    | 1 => rfl
  have hdeltas : ∀ j : Fin 2,
      (fun _ : ℕ => (0:ℝ)) j.val = (anchorChain j).delta := by
    intro j
    match j with
    | 0 => rfl
    | 1 => rfl
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ :=
    certified_loop_kernel anchorKm anchorObl 2
      (fun j => (j, anchorW j)) hf0 hb0 hr0 hdelta0 anchorChain
      (fun k => if k = 0 then (3:ℝ) else 3 / 4)
      (fun k => if k = 0 then (1:ℝ) else 3 / 2)
      (fun k => if k = 0 then (1:ℝ) else 0)
      (fun _ => (0:ℝ)) hdrops hspends hrisks hdeltas
  have hsum1 : ∑ j ∈ Finset.range 2, (fun _ : ℕ => (if j = 0 then (3:ℝ) else 3 / 4)) j
      = 3 + 3 / 4 := by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have hsum2 : ∑ j ∈ Finset.range 2, (fun _ => (if j = 0 then (1:ℝ) else 3 / 2)) j
      = 1 + 3 / 2 := by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have h1 : (3 + 3 / 4 : ℝ) ≤ anchorObj (anchorW 0) - anchorObj (anchorW 2) := by
    have := k1
    rw [hsum1] at this
    exact this
  have h4 : anchorB 2 ≤ anchorB 0 - (1 + 3 / 2) := by
    have := k4
    rw [hsum2] at this
    show anchorB 2 ≤ anchorB 0 - (1 + 3/2)
    exact this
  refine ⟨h1, ?_⟩
  have e1 : anchorB 2 = 15 / 2 := by norm_num [anchorB]
  have e2 : anchorB 0 = 10 := by norm_num [anchorB]
  linarith

end Hagi.Unified.CertifiedLoopKernel
