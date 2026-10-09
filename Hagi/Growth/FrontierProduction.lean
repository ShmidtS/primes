/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
set_option linter.style.header false

/-!
# FrontierProduction — сертифицированное производство frontier и семантика capability

* `injection_law_of_measured` (III-a): если `D (t+1) ≥ κ·dis t`
  и потребность обновления `ρ·D t + β·C t − ξ t ≤ κ·dis t`, то
  выполнен `InjectionLaw D C xi rho beta`.
* `certified_cycle_renewal` (III-b): если измеренная сумма n
  проб разногласия в [0,1] превышает `n·thr + 2n·ε` и
  `D (t+1) ≥ κ·disMean`, то renewal-закон одного цикла выполнен
  на этом событии с вероятностью `≥ 1 − 2e^{−2nε²}`.
  Посылка `hD` (разногласие ⇒ frontier) — архитектурная, не
  выводится здесь; многoцикловая версия не формализована.
* `CapabilitySound` (IV): `C t ≤ U t` для всех t; связка C с
  реальной моделью — посылка.
* `takeoff_lifts_utility`: если `CapabilitySound C U` и
  `C 0 * (1 + alpha) ^ T ≤ C T`, то `C 0 * (1 + alpha) ^ T ≤ U T`.
-/

open Finset Real

namespace Hagi

/-! ## III-a: детерминированная редукция β-посылки -/

/-- Абстрактный закон производства frontier:
`∀ t, D (t+1) ≥ ρ·D t + β·C t − ξ t`. -/
def InjectionLaw (D C xi : ℕ → ℝ) (rho beta : ℝ) : Prop :=
  ∀ t, D (t + 1) ≥ rho * D t + beta * C t - xi t

/-- Если `D (t+1) ≥ κ·dis t` для всех t и
`ρ·D t + β·C t − ξ t ≤ κ·dis t` для всех t, то
`InjectionLaw D C xi rho beta`. -/
theorem injection_law_of_measured (D C dis xi : ℕ → ℝ) (kappa rho beta : ℝ)
    (hD : ∀ t, D (t + 1) ≥ kappa * dis t)
    (h : ∀ t, rho * D t + beta * C t - xi t ≤ kappa * dis t) :
    InjectionLaw D C xi rho beta :=
  fun t => le_trans (h t) (hD t)

/-! ## III-b: статистическая сертификация одного цикла -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- Среднее по n пробам координатных средних (значения в [0,1]). -/
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

/-- Сертифицированное обновление одного цикла: при пробах
разногласия `Y` в [0,1], пороге `thr ∈ [0,1]`, `κ ≥ 0` и
посылках `D (t+1) ≥ κ·disMean p Y` и
`ρ·D t + β·C t − ξ t ≤ κ·thr`: с вероятностью
`≥ 1 − 2e^{−2nε²}` из измеренного события
`n·thr + 2n·ε ≤ Σ Y i (ω i)` следует
`D (t+1) ≥ ρ·D t + β·C t − ξ t`. -/
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

/-- `CapabilitySound C U` означает `C t ≤ U t` для всех t
(`U` — полезность над семейством задач; связка с реальной
моделью остаётся посылкой). -/
def CapabilitySound (C U : ℕ → ℝ) : Prop := ∀ t, C t ≤ U t

/-- Если `CapabilitySound C U` и `C 0 * (1 + alpha) ^ T ≤ C T`,
то `C 0 * (1 + alpha) ^ T ≤ U T`. -/
theorem takeoff_lifts_utility (C U : ℕ → ℝ) (alpha : ℝ) (T : ℕ)
    (hsnd : CapabilitySound C U)
    (hgr : C 0 * (1 + alpha) ^ T ≤ C T) :
    C 0 * (1 + alpha) ^ T ≤ U T :=
  le_trans hgr (hsnd T)

end Hagi
