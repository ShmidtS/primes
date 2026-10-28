import Hagi.Model.StageSemantics
import Hagi.System.StepCertificate
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
  /-- Безопасность: прирост защищённого риска в лимите. -/
  safety : S'.protectedRisk
    ≤ S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
      + u.eff.jointRisk + u.eff.compressRisk)
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
  obtain ⟨exec, progress, safety, resources⟩ := ht
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

end Hagi.Model
