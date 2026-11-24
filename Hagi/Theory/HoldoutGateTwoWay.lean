/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.Statistics

/-!
# HoldoutGateTwoWay — holdout-гейт ↔ популяционный риск

Код-предикат (HAGI_v2 `hagi/unified.py`, `_maybe_grow` @b3740e0:504-581):
новый блок принимается (`GROW`) iff

  holdoutMean(new) < holdoutMean(old) − 1e-4

на ОДНОЙ фиксированной holdout-выборке (последние ≤ 512 окон
fresh-домена; НЕ пересемплируется), иначе точный rollback. Оба
измерения — holdout-средние; «old» — trunk + свежий нетренированный
блок, «new» — trunk + block после warm-up.

Здесь честная часть: что такой гейт гарантирует о ПОПУЛЯЦИОННОМ
риске. Одна выборка оценивает обе гипотезы (и, из-за выбора лучшего
состояния блока по holdout, все промежуточные тоже) — это holdout-
переподбор, поэтому нужен union bound по семейству Θ всех
оценивавшихся состояний, а не одна гипотеза. Носитель —
`holdout_uniform_codebook` (two-sided Hoeffding). `anytime_catoni`
здесь не используется: он требует супермартингал по номеру шага
ВЫБОРКИ, а код заглядывает в одну выборку много раз (peeking по
гипотезам, не по размеру выборки).

Модель-посылки (не теоремы): holdout-выборка — k независимых
равномерных draws из конечной популяции Ω; потери ∈ [0, B].
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

open Hagi.Probability

namespace Hagi.Theory.HoldoutGateTwoWay

open Hagi.Theory.HoldoutRisk

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- **holdout_gate_two_way**: old и candidate оцениваются на одной
holdout-выборке; candidate может ВЫБИРАТЬСЯ по этой выборке
(`cand : (Fin k → Ω) → Θ`). С вероятностью ≥ 1 − |Θ|·2·exp(−2k(ε/B)²)
обе гипотезы одновременно в пределах ε от популяционного риска
(union bound по семейству), поэтому если гейт принял
(holdout-среднее кандидата ≤ holdout-среднего old минус margin),
то популяционный риск кандидата ≤ риск old + 2ε − margin:
«гейт не ухудшает популяционный риск больше чем на 2ε». -/
theorem holdout_gate_two_way {Θ : Type} [Fintype Θ] {k : ℕ} (hk : 0 < k)
    (ℓ : Θ → Ω → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ : ∀ θ ω, 0 ≤ ℓ θ ω ∧ ℓ θ ω ≤ B)
    (old : Θ) (cand : (Fin k → Ω) → Θ) (margin eps : ℝ) (heps : 0 < eps) :
    1 - (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k ≤
      prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => holdoutMean (ℓ (cand ωs)) ωs ≤ holdoutMean (ℓ old) ωs - margin →
          popMean (ℓ (cand ωs)) ≤ popMean (ℓ old) + 2 * eps - margin) := by
  classical
  have hunion : prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ωs => ∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      = 1 - prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => ¬ ∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|) := by
    rw [← prodPq_compl _ popIsProb]
    apply prodPq_iff
    intro ωs
    simp only [not_not]
  have hmono : prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ωs => ¬ ∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      ≤ prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => holdoutMean (ℓ (cand ωs)) ωs ≤ holdoutMean (ℓ old) ωs - margin →
          popMean (ℓ (cand ωs)) ≤ popMean (ℓ old) + 2 * eps - margin) := by
    apply prodPq_mono _ popIsProb
    intro ωs hgood hgate
    by_contra hcon
    push Not at hgood hcon
    have hnew := hgood (cand ωs)
    have hold := hgood old
    rw [abs_lt] at hnew hold
    linarith
  have hbound := holdout_uniform_codebook (Ω := Ω) hk ℓ hB hℓ eps heps
  rw [hunion] at hbound
  linarith


/-- Бюджет: радиус `eps / B` с `log(2N/δ) ≤ 2k(ε/B)²` делает union-фактор
`2N·exp(−2k(ε/B)²)` не больше `δ`. -/
theorem two_sided_union_budget {k : ℕ} (N delta x : ℝ)
    (hN : 0 < N) (hdelta : 0 < delta)
    (hbudget : Real.log (2 * N / delta) ≤ 2 * (k : ℝ) * x ^ 2) :
    2 * N * Real.exp (-2 * (k : ℝ) * x ^ 2) ≤ delta := by
  have hratio : 0 < 2 * N / delta := div_pos (by linarith) hdelta
  have hanti : Real.exp (-2 * (k : ℝ) * x ^ 2) ≤
      Real.exp (-Real.log (2 * N / delta)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, Real.exp_log hratio] at hanti
  have hmul := mul_le_mul_of_nonneg_left hanti (show (0 : ℝ) ≤ 2 * N by linarith)
  have hcancel : 2 * N * (2 * N / delta)⁻¹ = delta := by field_simp
  rwa [hcancel] at hmul

/-- **holdout_gate_two_way_delta** — δ-форма того же сертификата:
если `|Θ| ≤ N` и `log(2N/δ) ≤ 2k(ε/B)²`, то с вероятностью ≥ 1 − δ
принятый гейтом кандидат имеет популяционный риск
≤ риск old + 2ε − margin. Для двух гипотез без peeking `N = 2`;
для кода `N` — число оценивавшихся по holdout состояний блока
(выбор лучшего состояния — peeking), поэтому N ≥ 2 + число
checkpoint-оценок. -/
theorem holdout_gate_two_way_delta {Θ : Type} [Fintype Θ] {k : ℕ} (hk : 0 < k)
    (ℓ : Θ → Ω → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ : ∀ θ ω, 0 ≤ ℓ θ ω ∧ ℓ θ ω ≤ B)
    (old : Θ) (cand : (Fin k → Ω) → Θ) (margin eps : ℝ) (heps : 0 < eps)
    (N delta : ℝ) (hN : 0 < N) (hdelta : 0 < delta)
    (hcard : (Fintype.card Θ : ℝ) ≤ N)
    (hbudget : Real.log (2 * N / delta) ≤ 2 * (k : ℝ) * (eps / B) ^ 2) :
    1 - delta ≤
      prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => holdoutMean (ℓ (cand ωs)) ωs ≤ holdoutMean (ℓ old) ωs - margin →
          popMean (ℓ (cand ωs)) ≤ popMean (ℓ old) + 2 * eps - margin) := by
  classical
  have hfac : (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k ≤ delta := by
    have h := two_sided_union_budget (N := N) (delta := delta) (x := eps / B)
      hN hdelta hbudget
    have hcard2 : (Fintype.card Θ : ℝ) * 2 ≤ 2 * N := by nlinarith
    have hstep := mul_le_mul_of_nonneg_right hcard2
      (Real.exp_pos (-2 * (k : ℝ) * (eps / B) ^ 2)).le
    simpa only [concConfidenceTwoSided, concConfidence, ← mul_assoc] using hstep.trans h
  have hmain := holdout_gate_two_way hk ℓ hB hℓ old cand margin eps heps
  linarith

end Hagi.Theory.HoldoutGateTwoWay
