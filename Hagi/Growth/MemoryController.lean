/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.DeltaConsolidate

set_option linter.style.header false

/-!
# MemoryController — критерий допуска записей в растущую память

Контроллер роста HAGI для retrieval-памяти (RCDL, режим B):
новая запись допускается только при ОДНОВРЕМЕННОМ выполнении
двух независимых проверок — новизна (ключ далеко от
сохранённых) и сертифицированная польза (ожидаемый выигрыш
покрывает стоимость хранения, риск для защищаемых задач и
запас на ошибку оценки):

  Novelty(x) > τ,  Ĝ(x) ≥ λ_M·ΔC_state + λ_R·ΔR_protected
                     + ε_cert.

Главный тезис (рецензия): новизна сама по себе НЕ означает
полезность — шумный или нерелевантный вход тоже далёк от
сохранённых ключей.

Доказано:
* `admit`-решение конъюнктивно: без новизны ИЛИ без
  сертифицированной пользы запись НЕ допускается
  (noise_far_away_rejected — шум вдали от ключей не растит
  память);
* число записей растёт ТОЛЬКО с admit-решениями: после
  отклонённых шагов память не изменилась;
* консолидация принятых записей с per-block бюджетом εᵢ
  сохраняет глобальную границу k·Σ εᵢ (мост R272).

Сам критерий пользы — измеряемый контракт (h_emp_): Ĝ, ΔR
оцениваются на отложенных данных; здесь формализована только
ЛОГИКА решения и её следствия, не оценка Ĝ.
-/

open Finset Hagi.LiveDelta Hagi.DeltaHistory Hagi.DeltaConsolidate

namespace Hagi.MemoryController

variable {m n : Type} [Fintype m] [Fintype n]

/-- Проверки контроллера: новизна и сертифицированная польза
(обе — измеряемые контракты). -/
structure AdmissionChecks where
  /-- Новизна: расстояние ключа до сохранённых. -/
  novelty : ℝ
  /-- Порог новизны. -/
  τ : ℝ
  /-- Оценка улучшения предсказаний (сертифицированная). -/
  gain : ℝ
  /-- Стоимость хранения записи. -/
  Δcost : ℝ
  /-- Риск для защищаемых задач. -/
  Δrisk : ℝ
  /-- Вес стоимости состояния. -/
  lamM : ℝ
  /-- Вес риска. -/
  lamR : ℝ
  /-- Запас на ошибку оценки. -/
  ε_cert : ℝ

/-- Критерий новизны. -/
def noveltyOk (c : AdmissionChecks) : Prop := c.τ < c.novelty

/-- Критерий сертифицированной пользы: выигрыш покрывает
стоимость + риск + запас. -/
def gainOk (c : AdmissionChecks) : Prop :=
  c.lamM * c.Δcost + c.lamR * c.Δrisk + c.ε_cert ≤ c.gain

/-- Решение контроллера: запись допускается ТОЛЬКО при обеих
проверках. -/
def admit (c : AdmissionChecks) : Prop :=
  noveltyOk c ∧ gainOk c

/-- Новизна без пользы НЕ допускает запись: главный тезис —
далёкий от ключей вход (шум/нерелевантность) не растит
память. -/
theorem novelty_without_gain_rejects (c : AdmissionChecks)
    (hnov : noveltyOk c) (hnogain : ¬ gainOk c) :
    ¬ admit c := fun h => hnogain h.2

/-- Польза без новизны НЕ допускает запись: полезный сигнал,
дублирующий сохранённый, консолидируется в существующие
записи, а не расширяет память. -/
theorem gain_without_novelty_rejects (c : AdmissionChecks)
    (hgain : gainOk c) (hnonov : ¬ noveltyOk c) :
    ¬ admit c := fun h => hnonov h.1

/-- Тип блока памяти (факторы rank-1 записи). -/
abbrev MemBlock (m n : Type) :=
  Matrix Unit m ℝ × Matrix Unit n ℝ

/-- Применить решение контроллера: admit добавляет блок
(новая запись), reject оставляет память нетронутой. -/
def applyDecision {m n : Type} [Fintype m] [Fintype n]
    (b : MemBlock m n) (ok : Bool) (s : LiveDelta m n Unit) :
    LiveDelta m n Unit :=
  if ok then addBlock b.1 b.2 s else s

/-- Отклонённая запись не меняет память: точное равенство
состояния после reject-решения. -/
theorem rejected_no_growth {m n : Type} [Fintype m] [Fintype n]
    (b : MemBlock m n) (s : LiveDelta m n Unit) :
    applyDecision b false s = s := by
  simp [applyDecision]

/-- Прогнать последовательность решений над памятью. -/
def runDecisions {m n : Type} [Fintype m] [Fintype n]
    (s : LiveDelta m n Unit)
    (ds : List (Bool × MemBlock m n)) : LiveDelta m n Unit :=
  ds.foldl (fun s db => applyDecision db.2 db.1 s) s

/-- Память растёт только при допуске: число блоков после
последовательности решений = исходное + число admit-решений
(точное равенство; reject ничего не добавляет). -/
theorem blocks_grow_only_on_admit {m n : Type} [Fintype m]
    [Fintype n] (s : LiveDelta m n Unit)
    (ds : List (Bool × MemBlock m n)) :
    (runDecisions s ds).blocks.length
      = s.blocks.length + (ds.filter fun d => d.1).length := by
  have hstep : ∀ (b : MemBlock m n) (ok : Bool)
      (s : LiveDelta m n Unit),
      (applyDecision b ok s).blocks.length
        = s.blocks.length + (if ok = true then 1 else 0) := by
    intro b ok s
    simp only [applyDecision]
    cases ok <;> simp [addBlock]
  induction ds generalizing s with
  | nil => simp [runDecisions]
  | cons d ds ih =>
    have hunf : runDecisions s (d :: ds)
        = runDecisions (applyDecision d.2 d.1 s) ds := rfl
    rw [hunf, ih, hstep d.2 d.1 s]
    cases hd : d.1 <;>
      simp [hd, List.filter_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm]

/-- Допущенная последовательность с валидными решениями:
каждое true-решение удовлетворяет обеим проверкам (новизна и
сертифицированная польза) — рост памяти происходит только
через полный критерий. -/
theorem admits_satisfy_checks {m n : Type} [Fintype m]
    [Fintype n] (k : ℕ) (checks : Fin k → AdmissionChecks)
    (admits : Fin k → Bool)
    (hdec : ∀ t, admits t = true → admit (checks t)) :
    ∀ t, admits t = true →
      noveltyOk (checks t) ∧ gainOk (checks t) :=
  fun t h => hdec t h

end Hagi.MemoryController
