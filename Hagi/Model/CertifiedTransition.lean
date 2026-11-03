import Hagi.Model.StageSemantics
import Hagi.Model.CycleCertificate
import Hagi.System.StepCertificate
import Hagi.Optimization.LRSchedule
import Hagi.System.Certificates

/-!
# CertifiedTransition — зависимый сертификат перехода

Реализация эскиза аудита v4 §5.4: сертификат привязан к
КОНКРЕТНЫМ состояниям pre/post — `exec` требует, чтобы post
был получен реальным `advance`; прогресс/риск/бюджет —
свойства именно этой пары состояний (нельзя выдать
сертификат произвольной последовательности чисел).
-/

namespace Hagi.Model

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Сертифицированный переход: post получен исполнением
advance над pre с входом u; спуск положителен; риск и бюджет
честно учтены относительно лимитов шага. -/
structure CertifiedTransition (S S' : Hagi.System.GrowthState X)
    (u : StageInput X) (riskLim : ℝ) where
  /-- Исполнение: S' — реальный результат advance. -/
  exec : S' = advance S u
  /-- Прогресс: verify-сертификат нового состояния положителен. -/
  progress : 0 < (Hagi.System.verify S').decrease
  /-- Безопасность (точный ledger): прирост защищённого
  риска ≤ суммарная фактическая риск-трата операций. -/
  safety : S'.protectedRisk
    ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
      + u.eff.jointRisk + u.eff.compressRisk)
  /-- Безопасность (ЛИМИТ): riskLim АКТИВНО участвует в
  контракте — spec P0-3.3: riskAfter ≤ riskBefore + riskLim. -/
  safetyLim : S'.protectedRisk ≤ S.protectedRisk + riskLim
  /-- Ресурсы: точный бюджетный ledger пост-состояния. -/
  resources : S'.budget = S.budget - (u.eff.growCost + u.eff.mergeCost
    + u.eff.jointCost + u.eff.compressCost)

/-- КОНСТРУКТОР-ЗВУЧНОСТЬ: при операциональных условиях
(advance_verify_decrease_pos) honest-переход порождает
CertifiedTransition — поля safety/resources выполняются
rfl-определительно для advance. -/
theorem certifiedTransition_of_advance (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (hgap : 0 ≤ u.gap) (heta : 0 ≤ u.sp.eta)
    (hks : u.sp.kappa * u.sp.s < 2 * u.eff.growGain) :
    CertifiedTransition S (advance S u) u
      (u.eff.growRisk + u.eff.mergeRisk + u.eff.jointRisk
        + u.eff.compressRisk) where
  exec := rfl
  progress := advance_verify_decrease_pos S u hgap heta hks
  safety := by
    show (advance S u).protectedRisk
      ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk)
    simp only [advance]
    exact le_of_eq (by ring)
  safetyLim := by
    show (advance S u).protectedRisk
      ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk)
    simp only [advance]
    exact le_of_eq (by ring)
  resources := by
    simp only [advance]
    ring

/-- ГОРИЗОНТНАЯ ТЕОРЕМА (аудит v4 §5.4/§4): семейство
сертифицированных переходов телескопирует точный бюджетный
ledger — S T = S 0 − Σ spends; ресурсы накапливаются только
через реальные exec-переходы. -/
theorem certified_trajectory_budget {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → Hagi.System.GrowthState X) (u : ℕ → StageInput X)
    (T : ℕ)
    (hc : ∀ t < T, CertifiedTransition (S t) (S (t + 1)) (u t)
      ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk)) :
    (S T).budget = (S 0).budget
      - ∑ t ∈ Finset.range T, ((u t).eff.growCost + (u t).eff.mergeCost
        + (u t).eff.jointCost + (u t).eff.compressCost) := by
  have hmain : ∀ n : ℕ, n ≤ T →
      (S n).budget = (S 0).budget
        - ∑ t ∈ Finset.range n, ((u t).eff.growCost + (u t).eff.mergeCost
          + (u t).eff.jointCost + (u t).eff.compressCost) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hih := ih (by omega)
      have hc' := hc n (by omega)
      have hres := hc'.resources
      have hstep := hres
      rw [hstep, hih, Finset.sum_range_succ]
      ring
  exact hmain T (le_refl _)

/-- ГОРИЗОНТНЫЙ РИСК: семейство сертифицированных переходов
телескопирует прирост защищённого риска —
R T = R 0 + Σ per-step risk spends; безопасность накапливается
только через exec-переходы. -/
theorem certified_trajectory_risk {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → Hagi.System.GrowthState X) (u : ℕ → StageInput X)
    (T : ℕ)
    (hc : ∀ t < T, CertifiedTransition (S t) (S (t + 1)) (u t)
      ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk)) :
    (S T).protectedRisk = (S 0).protectedRisk
      + ∑ t ∈ Finset.range T, ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk) := by
  have hmain : ∀ n : ℕ, n ≤ T →
      (S n).protectedRisk = (S 0).protectedRisk
        + ∑ t ∈ Finset.range n, ((u t).eff.growRisk + (u t).eff.mergeRisk
          + (u t).eff.jointRisk + (u t).eff.compressRisk) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hih := ih (by omega)
      have hc' := hc n (by omega)
      have hstep := hc'.safety
      -- точное равенство из определения advance (safety — ≤,
      -- но для advance это равенство)
      have hexact : (S (n + 1)).protectedRisk
          = (S n).protectedRisk + ((u n).eff.growRisk
            + (u n).eff.mergeRisk + (u n).eff.jointRisk
            + (u n).eff.compressRisk) := by
        rw [hc'.exec]
        simp only [advance]
        ring
      rw [hexact, hih, Finset.sum_range_succ]
      ring
  exact hmain T (le_refl _)

/-- ГОРИЗОНТНЫЙ РОСТ: семейство сертифицированных переходов
даёт ТОЧНЫЙ закон capability — C T = C 0 + Σ измеренных
growGain шагов; рост накапливается только через
exec-переходы (третья горизонтирующая гарантия после
бюджета и риска). -/
theorem certified_trajectory_capability {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → Hagi.System.GrowthState X) (u : ℕ → StageInput X)
    (T : ℕ)
    (hc : ∀ t < T, CertifiedTransition (S t) (S (t + 1)) (u t)
      ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk)) :
    (S T).capability = (S 0).capability
      + ∑ t ∈ Finset.range T, (u t).eff.growGain := by
  have hmain : ∀ n : ℕ, n ≤ T →
      (S n).capability = (S 0).capability
        + ∑ t ∈ Finset.range n, (u t).eff.growGain := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hih := ih (by omega)
      have hc' := hc n (by omega)
      have hexact : (S (n + 1)).capability
          = (S n).capability + (u n).eff.growGain := by
        rw [hc'.exec]
        simp only [advance]
      rw [hexact, hih, Finset.sum_range_succ]
      ring
  exact hmain T (le_refl _)

/-- НАСЕЛЁННОСТЬ CertifiedTransition: реальный witness-переход
(wS0, wU0) порождает сертификат — структура непуста на
конкретных данных (не только на бумаге). -/
theorem witness_certifiedTransition :
    CertifiedTransition wS0 (advance wS0 wU0) wU0
      (wU0.eff.growRisk + wU0.eff.mergeRisk + wU0.eff.jointRisk
        + wU0.eff.compressRisk) :=
  certifiedTransition_of_advance wS0 wU0 (by simp [wU0])
    (by simp [wU0]) (by simp [wU0])

/-- МОСТ ЦЕПОЧКИ УТОЧНЕНИЙ (аудит v6, L3): Certificate
(GrowthState.verify-проекция) согласован с CertifiedTransition
— переход уровня L3 детерминирует все три наблюдаемых поля
Certificate пост-состояния: спад положителен, риск-трата в
лимите, бюджетный расход точен. Сертификатное семейство
сводится к одной цепочке с CertifiedTransition в ядре. -/
theorem certificate_of_transition {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S S' : Hagi.System.GrowthState X} {u : Hagi.Model.StageInput X}
    {riskLim : ℝ} (ht : CertifiedTransition S S' u riskLim) :
    0 < (Hagi.System.verify S').decrease
    ∧ S'.protectedRisk - S.protectedRisk
      ≤ u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk
    ∧ S.budget - S'.budget
      = u.eff.growCost + u.eff.mergeCost
        + u.eff.jointCost + u.eff.compressCost := by
  obtain ⟨exec, progress, safety, safetyLim, resources⟩ := ht
  refine ⟨progress, ?_, ?_⟩
  · linarith [safety]
  · rw [resources]
    ring


/-- ЗВЕНО ЦЕПОЧКИ 2 (аудит v6, L3): сертифицированный
переход (ядро CertifiedTransition) делает шаг-кандидата
StepCertificate продуктивным для алгоритма отбора
(bestDecrease): safe_selection_productive срабатывает —
L3-сертификат напрямую кормит Certified Growth Loop. -/
theorem transition_safe_selection {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S S' : Hagi.System.GrowthState X} {u : StageInput X}
    {riskLim : ℝ} (ht : CertifiedTransition S S' u riskLim)
    (epsG : ℝ) (hE : 0 ≤ epsG) :
    0 < Hagi.System.bestDecrease
      [Hagi.System.stepCertificateOfParts S' epsG hE] := by
  apply Hagi.System.safe_selection_productive
  refine ⟨Hagi.System.stepCertificateOfParts S' epsG hE,
    List.mem_cons_self, ?_⟩
  have hbase : (Hagi.System.stepCertificateOfParts S' epsG hE).base
      = Hagi.System.verify S' := rfl
  rw [hbase]
  exact ht.progress


/-- МОСТ WSD → CERTIFIED GROWTH LOOP (источник №11 ×
L3-цепочка): траектория сертифицированных переходов, чья
энергия следует PL-рекуррентности с LR-расписанием
(stable-фаза η = η_max длины m + late-фаза k), даёт ОДНОВРЕМЕННО
WSD-оценку энергии (геометрическое сжатие + шумовой бюджет +
late-decay) и ТОЧНУЮ бюджетную бухгалтерию цикла —
сертифицированный рост с LR-расписанием. -/
theorem wsd_cycle_bound {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → Hagi.System.GrowthState X) (u : ℕ → StageInput X)
    (mu sig etaMax : ℝ) (m k : ℕ)
    (hc : ∀ t < m + k, CertifiedTransition (S t) (S (t + 1)) (u t)
      ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk))
    (hpl : Hagi.Optimization.LRSchedule.plRec mu sig
      (fun t => (u t).sp.eta) (fun t => (S t).energy))
    (hmu : 0 < mu) (hetaMax : 0 < etaMax)
    (hwindow : mu * etaMax ≤ 1)
    (hnn : ∀ t, 0 ≤ (u t).sp.eta)
    (hb : ∀ t, (u t).sp.eta ≤ etaMax)
    (henn : ∀ t, 0 ≤ (S t).energy)
    (hstable : ∀ t < m, (u t).sp.eta = etaMax) :
    (S (m + k)).energy
      ≤ (1 - mu * etaMax) ^ m * (S 0).energy
        + sig ^ 2 * etaMax ^ 2
          * ((1 - (1 - mu * etaMax) ^ m) / (1 - (1 - mu * etaMax)))
        + (k : ℝ) * sig ^ 2 * etaMax ^ 2
    ∧ (S (m + k)).budget = (S 0).budget
      - ∑ t ∈ Finset.range (m + k),
          ((u t).eff.growCost + (u t).eff.mergeCost
            + (u t).eff.jointCost + (u t).eff.compressCost) := by
  constructor
  · exact Hagi.Optimization.LRSchedule.wsd_full_bound mu sig etaMax
      (fun t => (u t).sp.eta) (fun t => (S t).energy) m k hpl
      hmu hetaMax hwindow hnn hb henn hstable
  · exact certified_trajectory_budget S u (m + k) hc

open Hagi.System InnerProductSpace

/-- ЗВЕНО ЦЕПОЧКИ 3 (аудит v6, L3): семейство сертифицированных
переходов с законами стадий ПОРОЖДАЕТ CycleCertificate:
локальные контракты CertifiedTransition (exec/progress/safety/
resources) + законы стадий дают T-горизонтный цикл-сертификат
(точный рост capability, спуск потенциала, бюджетный ledger). -/
theorem cycle_certificate_of_transitions {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → GrowthState X) (u : ℕ → StageInput X) (T : ℕ)
    (hc : ∀ t < T, CertifiedTransition (S t) (S (t + 1)) (u t)
      ((u t).eff.growRisk + (u t).eff.mergeRisk
        + (u t).eff.jointRisk + (u t).eff.compressRisk))
    (hgainnn : ∀ t < T, 0 ≤ (u t).eff.growGain)
    (hgap : ∀ t < T, 0 ≤ (u t).gap)
    (hgrow : ∀ t < T, (u t).eff.growEnergy
      ≤ (S t).energy - (u t).eff.growGain)
    (hmerge : ∀ t < T, (u t).eff.mergeEnergy
      ≤ (u t).eff.growEnergy - (u t).gap)
    (hL : ∀ t < T, 0 < (u t).sp.L)
    (heta : ∀ t < T, (u t).sp.eta ≤ 1 / (u t).sp.L)
    (hdesc : ∀ t < T, ‖(u t).stepDir‖ ^ 2
      ≤ ⟪(u t).grad, (u t).stepDir⟫_ℝ)
    (hjoint : ∀ t < T, (u t).eff.jointEnergy
      ≤ (u t).eff.mergeEnergy
        - (u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
        + (u t).sp.L * (u t).sp.eta ^ 2 * ‖(u t).stepDir‖ ^ 2 / 2)
    (hledger : ∀ t < T, (u t).eff.compressEnergy
        - (u t).eff.jointEnergy
      ≤ (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr)
    (hcostnn : ∀ t < T, 0 ≤ (u t).eff.growCost + (u t).eff.mergeCost
      + (u t).eff.jointCost + (u t).eff.compressCost) :
    ∃ _gc : CycleCertificate T (fun t => (S t).capability)
      (fun t => (S t).energy) (fun t => (S t).budget), True := by
  refine ⟨{
  gain := fun t => (u t).eff.growGain
  h_gain_nonneg := hgainnn
  cap_step := by
    intro t ht
    have hexec := (hc t ht).exec
    have hcap : (advance (S t) (u t)).capability
        = (S t).capability + (u t).eff.growGain := rfl
    calc (S (t + 1)).capability
        = (advance (S t) (u t)).capability := by rw [hexec]
      _ = (S t).capability + (u t).eff.growGain := hcap
  drop := fun t => (u t).eff.growGain + (u t).gap
    + ((u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
      - (u t).sp.L * (u t).sp.eta ^ 2 * ‖(u t).stepDir‖ ^ 2 / 2)
    - (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr
  risk := fun _ => 0
  h_risk_nonneg := by intro t _; norm_num
  pot_descent := by
    intro t ht
    have hed := advance_energy_drop (S t) (u t)
      (hgrow t ht) (hgap t ht) (hmerge t ht) (hL t ht)
      (heta t ht) (hdesc t ht) (hjoint t ht) (hledger t ht)
    have hE : (S (t + 1)).energy
        = (advance (S t) (u t)).energy := by
      rw [(hc t ht).exec]
    have hAdven : (advance (S t) (u t)).energy
        = (u t).eff.compressEnergy := rfl
    rw [hE, hAdven]
    linarith
  spend := fun t => (u t).eff.growCost + (u t).eff.mergeCost
    + (u t).eff.jointCost + (u t).eff.compressCost
  h_spend_nonneg := hcostnn
  budget_ledger := by
    intro t ht
    exact (hc t ht).resources }, trivial⟩


/-- АУДИТ v12: riskLim-СВЯЗЬ. Если лимит riskLim покрывает
суммарный риск входа, то CertifiedTransition с этим лимитом
гарантирует S'.protectedRisk − S.protectedRisk ≤ riskLim
(параметр типа реально ограничивает прирост риска через
safety-поле; закрытие замечания «riskLim не используется»). -/
theorem certifiedTransition_risk_respect {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S S' : Hagi.System.GrowthState X) (u : StageInput X)
    (riskLim : ℝ)
    (h : CertifiedTransition S S' u riskLim)
    (hlim : u.eff.growRisk + u.eff.mergeRisk
      + u.eff.jointRisk + u.eff.compressRisk ≤ riskLim) :
    S'.protectedRisk - S.protectedRisk ≤ riskLim := by
  have hs := h.safety
  linarith [hs, hlim]


/-! ### Аудит v16, проблема №5: riskLim ДОЛЖЕН проверяться.
`CertifiedTransition` ведёт риск-бухгалтерию (safety), но
не связывает её с переданным лимитом. `CertifiedTransitionV2`
добавляет активное поле `hRiskLim : ΔR ≤ riskLim` (лимит
реально соблюдён) и мост из старой структуры. -/

/-- V2: сертифицированный переход с АКТИВНО проверенным
риск-лимитом (№5: счётчик ≠ соблюдение лимита).
НЕканонический слой: канонический переход — зависимый
`Hagi.Unified.HonestTransition` (спуск выведен из
исполнения); сведение — `ctv2Honest` при операциональных
условиях спуска. Новым кодом использовать
`HonestTransition` напрямую. -/
structure CertifiedTransitionV2 (S S' : Hagi.System.GrowthState X)
    (u : StageInput X) (riskLim : ℝ) where
  /-- Вся валидация V1. -/
  base : CertifiedTransition S S' u riskLim
  /-- ЛИМИТ АКТИВЕН: прирост защищённого риска ≤ riskLim. -/
  hRiskLim : S'.protectedRisk - S.protectedRisk ≤ riskLim

/-- МОСТ V1 → V2: старый сертификат + соблюдение лимита
дают V2 (полная совместимость, Freeze стабилен). -/
theorem ctv2_of_ct {S S' : Hagi.System.GrowthState X}
    {u : StageInput X} {riskLim : ℝ}
    (hc : CertifiedTransition S S' u riskLim)
    (hrisk : S'.protectedRisk - S.protectedRisk ≤ riskLim) :
    CertifiedTransitionV2 S S' u riskLim :=
  ⟨hc, hrisk⟩


/-! ### Аудит v17 (P0-2): фактическое убывание objective —
обязательное поле сертификата.

`progress : 0 < (verify S').decrease` — положительность
ВЫЧИСЛЕННОГО числа-сертификата; это не то же, что
`E(S') < E(S)`. `CertifiedTransitionV3` добавляет активное
поле `hActualDescent` — фактический спад энергии
пост-состояния относительно пре-состояния — и конструктор
из канонических законов стадий (`advance_energy_drop`):
спад ВЫВЕДЕН из исполнения, а не постулирован. -/

/-- V3: сертифицированный переход с ОБЯЗАТЕЛЬНЫМ фактическим
убыванием objective: `E(S') < E(S)`. Наследует всю валидацию
V2 (исполнение, положительный verify, риск в лимите, точный
бюджет). Канонический конструктор — `ctv3_of_stageLaws`. -/
structure CertifiedTransitionV3 (S S' : Hagi.System.GrowthState X)
    (u : StageInput X) (riskLim : ℝ) extends CertifiedTransitionV2 S S' u riskLim where
  /-- ФАКТИЧЕСКИЙ спад: энергия пост-состояния строго меньше
  энергии пре-состояния (не сертификатное число, а само
  `S'.energy < S.energy`). -/
  hActualDescent : S'.energy < S.energy

/-- Мост V2 → V3: фактический спад + V2-валидация. -/
theorem ctv3_of_actualDescent {S S' : Hagi.System.GrowthState X}
    {u : StageInput X} {riskLim : ℝ}
    (hc : CertifiedTransitionV2 S S' u riskLim)
    (hdrop : S'.energy < S.energy) :
    CertifiedTransitionV3 S S' u riskLim :=
  { toCertifiedTransitionV2 := hc, hActualDescent := hdrop }

/-- КОНСТРУКТОР ИЗ ЗАКОНОВ СТАДИЙ (P0-2): при канонических
предпосылках `advance_energy_drop` и строгой положительности
сертифицированного дропа переход `advance S u` несёт
V3-сертификат. -/
theorem ctv3_of_stageLaws (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (hgap : 0 ≤ u.gap) (heta : 0 ≤ u.sp.eta)
    (hks : u.sp.kappa * u.sp.s < 2 * u.eff.growGain)
    (hgain : u.eff.growEnergy ≤ S.energy - u.eff.growGain)
    (hmerge : u.eff.mergeEnergy ≤ u.eff.growEnergy - u.gap)
    (hL : 0 < u.sp.L) (hetaL : u.sp.eta ≤ 1 / u.sp.L)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hjoint : u.eff.jointEnergy
      ≤ u.eff.mergeEnergy - u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        + u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    (hledger : u.eff.compressEnergy - u.eff.jointEnergy
      ≤ u.sp.kappa * u.sp.s * u.eff.quantErr)
    (hcostnn : 0 ≤ u.eff.growCost + u.eff.mergeCost
      + u.eff.jointCost + u.eff.compressCost)
    (hstrict : 0 < u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * u.eff.quantErr) :
    CertifiedTransitionV3 S (advance S u) u
      (u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk) where
  toCertifiedTransitionV2 :=
    { base := certifiedTransition_of_advance S u hgap heta hks
      hRiskLim := by
        -- для advance прирост риска РАВЕН сумме стадийных
        -- рисков (safety-поле ядра — равенство).
        have hEq : (advance S u).protectedRisk - S.protectedRisk
            = u.eff.growRisk + u.eff.mergeRisk
              + u.eff.jointRisk + u.eff.compressRisk := by
          simp only [advance]; ring
        rw [hEq] }
  hActualDescent := by
    have hd := advance_energy_drop S u hgain hgap hmerge hL hetaL
      hdesc hjoint hledger
    have hE : (advance S u).energy = u.eff.compressEnergy := rfl
    rw [hE]
    linarith [hstrict]

/-- ЗВУК V3: из сертификата следует фактический спад и
V1-валидация (exec/progress/safety/resources) — единая точка
входа для потребителей. -/
theorem ctv3_sound {S S' : Hagi.System.GrowthState X}
    {u : StageInput X} {riskLim : ℝ}
    (h : CertifiedTransitionV3 S S' u riskLim) :
    S' = advance S u
    ∧ 0 < (Hagi.System.verify S').decrease
    ∧ S'.protectedRisk - S.protectedRisk
      ≤ u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk
    ∧ S.budget - S'.budget
      = u.eff.growCost + u.eff.mergeCost
        + u.eff.jointCost + u.eff.compressCost
    ∧ S'.energy < S.energy := by
  obtain ⟨⟨base, _⟩, hdrop⟩ := h
  exact ⟨base.exec, base.progress,
    (certificate_of_transition base).2.1,
    (certificate_of_transition base).2.2, hdrop⟩


/-! ### Мост с решёточной вертикалью: монотонность сертифицируемости

MachineBridge подставляет `quantErr = quantErr Delta w` в
StageInput; machine_quant_err_bound даёт `quantErr ≤ √n·Δ/2`.
При решёточном расписании Δ_K = δ/2^K ошибка падает
геометрически с глубиной K — и строгий спад, сертифицированный
на одной глубине, остаётся строгим на любой большей. Это
делает углубление решётки БЕЗОПАСНЫМ улучшением контроллера:
сертификат V3 не теряется. -/

/-- МОНОТОННОСТЬ СЕРТИФИЦИРУЕМОСТИ: если строгий спад
выполнен при квантовой ошибке `qe₀` (и slack положителен
через `slack₀`), то он выполнен и при меньшей ошибке
`qe ≤ qe₀`. Углубление решётки (Δ→Δ/2^k ⇒ quantErr↓)
сохраняет сертификат V3. -/
theorem stageLaws_mono_quantErr (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (hgap : 0 ≤ u.gap) (heta : 0 ≤ u.sp.eta)
    (hks : u.sp.kappa * u.sp.s < 2 * u.eff.growGain)
    (hgain : u.eff.growEnergy ≤ S.energy - u.eff.growGain)
    (hmerge : u.eff.mergeEnergy ≤ u.eff.growEnergy - u.gap)
    (hL : 0 < u.sp.L) (hetaL : u.sp.eta ≤ 1 / u.sp.L)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hjoint : u.eff.jointEnergy
      ≤ u.eff.mergeEnergy - u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        + u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    (hcostnn : 0 ≤ u.eff.growCost + u.eff.mergeCost
      + u.eff.jointCost + u.eff.compressCost)
    (qe qe₀ : ℝ) (hqe : qe ≤ qe₀) (hksnn : 0 ≤ u.sp.kappa * u.sp.s)
    (hledger₀ : u.eff.compressEnergy - u.eff.jointEnergy
      ≤ u.sp.kappa * u.sp.s * qe₀)
    (hstrict₀ : 0 < u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * qe₀) :
    0 < u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * qe := by
  have h1 : u.sp.kappa * u.sp.s * qe
      ≤ u.sp.kappa * u.sp.s * qe₀ :=
    mul_le_mul_of_nonneg_left hqe hksnn
  linarith

end Hagi.Model
