/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CertifiedArgmax — канонический слой сертифицированного argmax

Консолидация R3 (addendum A5, slice 1): единый канон для всех
«ε-точные оценки ⇒ сертифицированный выбор» лемм. Источники
(полный перенос, FQN сохранены):

* `Hagi.Data.CertifiedArgmax` (был `Hagi/Data/CertifiedArgmax.lean`):
  строгая 2ε-форма на истинном зазоре + контрпример неоднозначности;
* `Hagi.Budget` (был `Hagi/Budget/CertifiedArgmax.lean`):
  попарная/селекционная 2ε-форма на зазоре оценок + политика
  случайного выбора при несертифицированном зазоре;
* `Hagi.Growth` (были `Hagi/Growth/SelfDevelopment.lean` — селекторы,
  `Hagi/Growth/AdaptiveQuery.lean` — усреднённая форма):
  3ε-форма на базовом выигрыше с аддитивной 2ε-гарантией.

Семантическая честность (2ε vs 3ε): варианты НЕ сливаются — у них
разные посылки. 2ε-варианты восстанавливают точный argmax при
сертифицированном зазоре; 3ε-вариант даёт лишь аддитивную
2ε-гарантию без посылки разделения. Ядро связи —
`Hagi.Cert.certified_selection_slack` (общая 2ε-механика), через
которую переприведён `certified_gain_select`: третий ε покупает
положительность (`g a' ≥ g a₀ − 2ε > 3ε − 2ε = ε ≥ 0`).

Размещение: A5-цель `Hagi/Math/` отсутствует в LAYERS карты
`scripts/LayerLint.py` (6-слойная цель аспирационна); канон лежит
в `Hagi/Cert/` (слой 2, каноническое certification-ядро C224).
Миграция в Math/ — debt-запись (см. `.omc/tech-debt.md`).
-/

namespace Hagi.Cert

/-- **Общая 2ε-механика сертифицированного выбора (связующий
варианты lemma)**: если все оценки ε-точны и `Ghat a₀ ≤ Ghat a'`,
то `g a₀ − 2·ε ≤ g a'` — два треугольных неравенства. Это ядро,
которое 2ε-варианты (`certified_argmax_strict`,
`argmax_pair_certified`) усиливают до точного argmax при
сертифицированном зазоре, а 3ε-вариант (`certified_gain_select`)
использует как есть: третий ε даёт положительность. -/
theorem certified_selection_slack {A : Type} (g Ghat : A → ℝ)
    (eps : ℝ) (hconc : ∀ a, |Ghat a - g a| ≤ eps)
    (a₀ a' : A) (hsel : Ghat a₀ ≤ Ghat a') :
    g a₀ - 2 * eps ≤ g a' := by
  have h1 := hconc a₀
  have h2 := hconc a'
  rw [abs_le] at h1 h2
  linarith

end Hagi.Cert

namespace Hagi.Data.CertifiedArgmax

variable {ι : Type*}

/-- **Гарантированный argmax**: при отрыве истинного
максимума imax от каждого конкурента строго больше 2ε и
оценках с ошибкой ≤ ε — argmax оценок детерминированно
равен imax. -/
theorem certified_argmax_strict {v est : ι → ℝ} {ε : ℝ}
    (herr : ∀ i, |est i - v i| ≤ ε)
    {imax : ι} (hgap : ∀ i, i ≠ imax → 2 * ε < v imax - v i) :
    ∀ i, i ≠ imax → est i < est imax := by
  intro i hi
  have h1 : est i ≤ v i + ε := by
    have h := herr i
    rw [abs_le] at h
    linarith
  have h2 : v imax - ε ≤ est imax := by
    have h := herr imax
    rw [abs_le] at h
    linarith
  have h3 := hgap i hi
  linarith

/-- **Неоднозначность — честная граница**: при зазоре
0 < g ≤ ε (≤ 2ε) существуют ε-точные оценки, у которых
argmax смещён с истинного максимума: v 0 > v 1, но
est 1 > est 0. Никакой метод выбора не может гарантировать
истинный максимум при 2ε-зазоре — нужна отдельная
обработка неоднозначности. -/
theorem certified_argmax_ambiguity {ε g : ℝ}
    (hε : 0 < ε) (hg : 0 < g) (hgε : g ≤ ε) :
    ∃ (v est : Fin 2 → ℝ),
      (∀ i, |est i - v i| ≤ ε)
      ∧ v 0 > v 1 ∧ est 1 > est 0 := by
  refine ⟨fun i => if i = 0 then g else 0,
    fun i => if i = 0 then 0 else ε,
    ?_, by simp [if_pos]; exact hg, by simp [if_pos]; exact hε⟩
  intro i
  fin_cases i <;> simp <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

end Hagi.Data.CertifiedArgmax

open Finset

namespace Hagi.Budget

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Попарная сертификация: зазор > 2ε_Γ при точности ε_Γ
восстанавливает истинное упорядочение Γ. -/
theorem argmax_pair_certified (Gamma GammaHat : I → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hacc : ∀ k, |GammaHat k - Gamma k| ≤ eps)
    (i j : I) (hgap : 2 * eps < GammaHat i - GammaHat j) :
    Gamma j < Gamma i := by
  have h1 := hacc i
  have h2 := hacc j
  have h3 : GammaHat i - eps ≤ Gamma i := by
    rw [abs_sub_comm] at h1
    rw [abs_le] at h1
    linarith
  have h4 : Gamma j ≤ GammaHat j + eps := by
    rw [abs_le] at h2
    linarith
  linarith

/-- Селекционная сертификация: максимайзер измерения с
зазором > 2ε_Γ от каждого конкурента — истинный максимайзер. -/
theorem argmax_select_certified (Gamma GammaHat : I → ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hacc : ∀ k, |GammaHat k - Gamma k| ≤ eps)
    (sel : I)
    (hsel : ∀ k, GammaHat k ≤ GammaHat sel)
    (hsep : ∀ k, sel ≠ k → 2 * eps < GammaHat sel - GammaHat k) :
    ∀ k, Gamma k ≤ Gamma sel := by
  intro k
  by_cases hk : k = sel
  · rw [hk]
  · have hgt := argmax_pair_certified Gamma GammaHat eps heps hacc sel k
      (hsep k (fun h => hk h.symm))
    exact le_of_lt hgt

/-- Политика случайного выбора при несертифицированном зазоре
(2ε_Γ-брекет не выполнен): argmax НЕ легитимен. -/
def RequiresRandomSplit (GammaHat : I → ℝ) (eps : ℝ) (i j : I) : Prop :=
  GammaHat i - GammaHat j ≤ 2 * eps

/-- **Неоднозначность при несертифицированном зазоре**
(контрпример-конструкция): зазор Γ̂ i − Γ̂ j = 2ε − δ ≤ 2ε
допускает ДВЕ конфигурации истинных Γ, обе согласованные с
измерением в пределах ε, но с ПРОТИВОПОЛОЖНЫМ argmax
(Γᴬ: argmax = true; Γᴮ: argmax = false) — argmax по Γ̂ не
несёт информации об истинном argmax. Политика
`RequiresRandomSplit` обоснована. -/
theorem tie_ambiguity (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta) (hdelta2 : delta < 2 * eps) :
    ∃ GammaA GammaB GammaHat : Bool → ℝ,
      (∀ k, |GammaHat k - GammaA k| ≤ eps)
        ∧ (∀ k, |GammaHat k - GammaB k| ≤ eps)
        ∧ RequiresRandomSplit GammaHat eps true false
        ∧ GammaB true < GammaB false
        ∧ GammaA false < GammaA true := by
  refine ⟨(fun b => if b then eps else delta - eps),
    (fun b => if b then -eps else delta - eps),
    (fun b => if b then 0 else -(2 * eps - delta)), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  · intro k
    cases k <;> simp <;> rw [abs_le] <;> constructor <;> linarith
  · unfold RequiresRandomSplit
    simp
    linarith
  · simp
    linarith
  · simp
    linarith

end Hagi.Budget

namespace Hagi.Growth

variable {A : Type} [Fintype A] [Nonempty A]

/-- Safe-подмножество кандидатов: фильтр `Finset.univ` по
`safe` (decidable). -/
def safeCandidates (safe : A → Prop) [DecidablePred safe] : Finset A :=
  Finset.univ.filter safe

/-- Если safe-набор непуст, то существует
`a' ∈ safeCandidates safe` с `G a ≤ G a'` для всех
`a ∈ safeCandidates safe`. -/
theorem controller_max_exists (G : A → ℝ) (safe : A → Prop)
    [DecidablePred safe] (hne : (safeCandidates safe).Nonempty) :
    ∃ a' ∈ safeCandidates safe, ∀ a ∈ safeCandidates safe, G a ≤ G a' :=
  Finset.exists_max_image (safeCandidates safe) G hne

/-- Если `|Ghat a − g a| ≤ eps` для всех a,
`a₀ ∈ safeCandidates safe` и `3·eps < g a₀`, то существует
`a' ∈ safeCandidates safe` с `0 < g a'` и
`g a₀ − 2·eps ≤ g a'`. 3ε-вариант: без посылки разделения —
гарантия лишь аддитивная; доказательство переприведено через
общую 2ε-механику `Hagi.Cert.certified_selection_slack`
(третий ε покупает положительность). -/
theorem certified_gain_select (g Ghat : A → ℝ) (safe : A → Prop)
    [DecidablePred safe] (eps : ℝ) (heps : 0 ≤ eps)
    (hconc : ∀ a, |Ghat a - g a| ≤ eps)
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe)
    (hgap : 3 * eps < g a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < g a' ∧ g a₀ - 2 * eps ≤ g a' := by
  have hne : (safeCandidates safe).Nonempty := ⟨a₀, h₀⟩
  obtain ⟨a', ha'mem, hmax⟩ := controller_max_exists Ghat safe hne
  refine ⟨a', ha'mem, ?_, ?_⟩
  · -- 0 < g a': slack + третий ε (hgap) даёт g a' > ε ≥ 0
    have hslack :=
      Hagi.Cert.certified_selection_slack g Ghat eps hconc a₀ a' (hmax a₀ h₀)
    linarith
  · exact Hagi.Cert.certified_selection_slack g Ghat eps hconc a₀ a'
      (hmax a₀ h₀)

/-- The averaged-estimator radius: e/√K for K queries. -/
noncomputable def avgRadius (e : ℝ) (K : ℕ) : ℝ := e / Real.sqrt K

/-- The radius function is nonincreasing in `K` over positive
integers and `avgRadius e 1 = e` (given `0 ≤ e`). -/
theorem avgRadius_shrinks (e : ℝ) (he : 0 ≤ e) (K L : ℕ)
    (hK : 0 < K) (hKL : K ≤ L) :
    avgRadius e L ≤ avgRadius e K ∧
      avgRadius e 1 = e := by
  constructor
  · unfold avgRadius
    have hs : (Real.sqrt K : ℝ) ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by exact_mod_cast hKL)
    exact div_le_div_of_nonneg_left he (Real.sqrt_pos.mpr (by exact_mod_cast hK)) hs
  · unfold avgRadius
    norm_num

/-- Averaged certified selection: assuming every estimate
`Ghat a` deviates from `g a` by at most `avgRadius e K`, if the
safe candidate `a₀` has `3 * avgRadius e K < g a₀`, then some
safe candidate `a'` satisfies `0 < g a'` and
`g a₀ - 2 * avgRadius e K ≤ g a'`. -/
theorem certified_gain_select_avg {A : Type} [Fintype A] [Nonempty A]
    (g Ghat : A → ℝ) (safe : A → Prop) [DecidablePred safe]
    (e : ℝ) (he : 0 ≤ e) (K : ℕ) (hK : 0 < K)
    (hconc : ∀ a, |Ghat a - g a| ≤ avgRadius e K)
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe)
    (hgap : 3 * avgRadius e K < g a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < g a' ∧ g a₀ - 2 * avgRadius e K ≤ g a' :=
  have hrad : 0 ≤ avgRadius e K := by
    unfold avgRadius
    apply div_nonneg he (Real.sqrt_nonneg _)
  certified_gain_select g Ghat safe (avgRadius e K) hrad hconc a₀ h₀
    hgap

end Hagi.Growth
