/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
set_option linter.style.header false

/-!
# Мост III+IV: FrontierProduction (сертифицированный) + CapabilitySemantics

Аудит §23–24: абстрактная динамика
`D_{t+1} ≥ ρD_t + βC_t − ξ_t` (FrontierScaling/GainRenewal)
держит β как ГЛАВНУЮ недоказанную гипотезу — «система порождает
новый usable frontier пропорционально capability». Этот модуль
делает два шага к её закрытию:

**III-a (детерминированная редукция)**: `injection_law_of_measured` —
закон обновления следует, если измеренное свежее разногласие
экспертов dis_t (среднее клиппированных попарных разностей
логитов, [0,1]) покрывает потребность обновления:
`ρD_t + βC_t − ξ_t ≤ κ·dis_t`. β-посылка сведена к ИЗМЕРИМОЙ
величине (GapLaw уже связывает разногласие с merge gain).

**III-b (статистическая сертификация)**:
`certified_cycle_renewal` — композиция с `certified_premise`
(R114): если измеренная сумма проб разногласия цикла t превышает
порог n·thr + 2nε, то истинное среднее разногласие ≥ thr с
вероятностью ≥ 1 − 2e^{−2nε²}; при архитектурной посылке
`hD : D_{t+1} ≥ κ·disMean` это даёт renewal-закон на хорошем
событии. β становится runtime-проверяемой, а не декоративной.

**IV (CapabilitySemantics)**: `CapabilitySound C U` — C_t ≤ U_t,
где U — полезность над семейством задач; `takeoff_lifts_utility`
переносит экспоненциальный рост C на U. Честная граница:
связка C с реальной моделью остаётся premise (audit §9).

**Честные границы**: (1) hD (разногласие ⇒ frontier) —
архитектурная посылка, не выведена из GapLaw (GapLaw даёт
разногласие ⇒ merge gain, недостающий кусок — gain ⇒ следующий
frontier); (2) многoцикловая версия требует union bound по
независимым циклам — сформулирована для одного цикла.
-/

open Finset Real

namespace Hagi

/-! ## III-a: детерминированная редукция β-посылки -/

/-- Абстрактный закон производства frontier (audit §23). -/
def InjectionLaw (D C xi : ℕ → ℝ) (rho beta : ℝ) : Prop :=
  ∀ t, D (t + 1) ≥ rho * D t + beta * C t - xi t

/-- **β-посылка сведена к измеримому разногласию**: если свежее
разногласие экспертов dis_t (mean clipped pairwise logit diff)
покрывает потребность обновления, закон производства выполнен. -/
theorem injection_law_of_measured (D C dis xi : ℕ → ℝ) (kappa rho beta : ℝ)
    (hD : ∀ t, D (t + 1) ≥ kappa * dis t)
    (h : ∀ t, rho * D t + beta * C t - xi t ≤ kappa * dis t) :
    InjectionLaw D C xi rho beta :=
  fun t => le_trans (h t) (hD t)

/-! ## III-b: статистическая сертификация одного цикла -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Истинное среднее разногласие по n пробам (в [0,1]). -/
noncomputable def disMean {n : ℕ} (p : Fin n → V → ℝ) (Y : Fin n → V → ℝ) : ℝ :=
  (∑ i, coordMean p Y i) / (n : ℝ)

@[simp]
theorem coordMean_const {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (c : ℝ) (i : Fin n) : coordMean p (fun _ _ => c) i = c := by
  unfold coordMean
  rw [← Finset.sum_mul, (hp i).2, one_mul]

theorem const_probe_sum {n : ℕ} (c : ℝ) (ω : Fin n → V) :
    ∑ i, (fun _ _ => c) i (ω i) = (n : ℝ) * c := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Сертифицированное обновление frontier одного цикла**:
пусть `thr` — требуемый уровень свежего разногласия
(достаточный для renewal: `κ·thr ≥ ρD_t + βC_t − ξ_t`), Y — n
парных проб разногласия в [0,1]. Если ИЗМЕРЕННАЯ сумма проб
превышает порог с margin 2nε, то renewal-закон цикла t выполнен
с вероятностью ≥ 1 − 2e^{−2nε²}. Бета-механизм становится
runtime-проверяемым: порог + margin + n проб ⇒ гарантия. -/
theorem certified_cycle_renewal {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (Y : Fin n → V → ℝ) (hY : ∀ i v, 0 ≤ Y i v ∧ Y i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (D C : ℕ → ℝ) (kappa rho beta : ℝ) (xi : ℕ → ℝ) (t : ℕ) (thr : ℝ)
    (hthr01 : 0 ≤ thr ∧ thr ≤ 1) (hkappa : 0 ≤ kappa)
    (hD : D (t + 1) ≥ kappa * disMean p Y)
    (hthr : rho * D t + beta * C t - xi t ≤ kappa * thr) :
    1 - 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω =>
        (n : ℝ) * thr + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → D (t + 1) ≥ rho * D t + beta * C t - xi t) := by
  classical
  set X : Fin n → V → ℝ := fun _ _ => thr with hXdef
  have hXb : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1 :=
    fun _ _ => ⟨hthr01.1, hthr01.2⟩
  have hc := certified_premise p hp X Y hXb hY hn eps heps
  -- измеренная сумма константных проб = n·thr; их среднее тоже
  have hsumX : ∀ ω : Fin n → V, ∑ i, X i (ω i) = (n : ℝ) * thr :=
    fun ω => const_probe_sum thr ω
  have hmuX : (∑ i, coordMean p X i) = (n : ℝ) * thr := by
    rw [hXdef]
    simp [coordMean_const p hp thr]
  -- μ-формула disMean
  have hdis : disMean p Y = (∑ i, coordMean p Y i) / (n : ℝ) := rfl
  -- на хорошем событии hc: требование выполнено
  have hmono : prodPq p (fun ω =>
        ∑ i, X i (ω i) + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → ∑ i, coordMean p X i ≤ ∑ i, coordMean p Y i)
      ≤ prodPq p (fun ω =>
        (n : ℝ) * thr + 2 * (n : ℝ) * eps ≤ ∑ i, Y i (ω i)
          → D (t + 1) ≥ rho * D t + beta * C t - xi t) :=
    prodPq_mono p hp _ _ (by
      intro ω hfull hmeas
      -- hmeas : n·thr + 2nε ≤ ΣY; hfull ждёт ΣX + 2nε ≤ ΣY
      have hXle : ∑ i, X i (ω i) + 2 * (n : ℝ) * eps
          ≤ ∑ i, Y i (ω i) := by
        rw [hsumX ω]
        exact hmeas
      have hconcl := hfull hXle
      rw [hmuX] at hconcl
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hthr_le : thr ≤ disMean p Y := by
        rw [hdis, le_div_iff₀ hnpos, mul_comm thr]
        exact hconcl
      have hchain : kappa * thr ≤ kappa * disMean p Y :=
        mul_le_mul_of_nonneg_left hthr_le (by positivity)
      have hreq : kappa * thr ≥ rho * D t + beta * C t - xi t := hthr
      have hD2 : D (t + 1) ≥ kappa * disMean p Y := hD
      have hfin : D (t + 1) ≥ rho * D t + beta * C t - xi t := by
        nlinarith [hchain, hreq, hD2]
      exact hfin)
  exact le_trans hc hmono

/-! ## IV: CapabilitySemantics -/

/-- **CapabilitySemantics** (audit §24): формальная C_t — нижняя
грань полезности U_t над семейством задач. Связка с реальной
моделью — premise; без неё capability остаётся certificate
variable (audit §9 это признаёт). -/
def CapabilitySound (C U : ℕ → ℝ) : Prop := ∀ t, C t ≤ U t

/-- Экспоненциальный takeoff формальной capability переносится
на полезность: `C_T ≥ C₀(1+α)^T ∧ CapabilitySound C U ⇒
U_T ≥ C₀(1+α)^T`. -/
theorem takeoff_lifts_utility (C U : ℕ → ℝ) (alpha : ℝ) (T : ℕ)
    (hsnd : CapabilitySound C U)
    (hgr : C 0 * (1 + alpha) ^ T ≤ C T) :
    C 0 * (1 + alpha) ^ T ≤ U T :=
  le_trans hgr (hsnd T)

end Hagi
