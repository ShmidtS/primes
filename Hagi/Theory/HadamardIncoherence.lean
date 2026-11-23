/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: HAGI_v2 formalization team
-/

import Mathlib.Tactic
import Hagi.Core.Hadamard
import Hagi.Runtime.TernaryExact

set_option linter.style.header false

/-!
# HadamardIncoherence — проверяемый когерентностный гейт для
Hadamard-поворота перед тернарным квантованием (A19/P5)

Аудит P5: Hadamard-поворот перед тернарным квантованием полезен
только под условием некогерентности — автор сам доказал, что без
условия насыщение возможно (корпусный негатив
`Hagi.Contracts.HadamardTernaryBridge.hadamard_not_universally_
incoherent`: для k = 1 и константного вектора x = (2, 2) первая
координата Hx равна 2√2 = ‖x‖₂ и насыщает при s = 1). Этот модуль
делает условие ИЗМЕРЯЕМЫМ: польза поворота проверяется ДО
квантования сравнением двух вычислимых ℚ-величин.

Измеряемая премиса: cohSq w := ‖w‖∞² / ‖w‖₂² (когерентность в
квадрате; coh = √cohSq, квадрат монотонен на неотрицательных —
работаем без иррациональностей). Гейт «поворот полезен»:
cohSq (H w) < cohSq w — строгое ℚ-неравенство, обе части конечны и
вычислимы (max и сумма по явному списку); решение принимает машина,
не постулат (rotate-if-measured-better).

Целочисленность: гейт использует ЦЕЛОЧИСЛЕННЫЙ Sylvester H (±1, без
1/√(2^k)); корректность следует из масштабной инвариантности
`cohSq_smul`: cohSq (c • w) = cohSq w — нормировка матрицы не влияет
на сравнение. Энергия не теряется: `rotate_energy_eq` — целочисленный
Парсевал ‖H w‖₂² = 2^k · ‖w‖₂² (для ортонормированного Q = H/√(2^k)
это ‖Q w‖₂ = ‖w‖₂; доменная projector-форма Парсеваля —
`Hagi.Learning.HadamardParseval.parseval`, цикл 26, другая форма —
указатель, не дублирование).

Условная польза — тернарная: при по-координатной границе |v i| ≤ M
и масштабе s хвост насыщения ограничен `satTail_le_of_forall_le`:
satTail s v ≤ n · (M − s)² (семейство ternary_split_le); при
M ≤ 3s/2 хвост нулевой (интерпретация моста
`hadamard_satTail_zero_of_l2_bound`: μ-премиса ⇒ в-диапазон). Гейт
уменьшает измеренный M — польза условная, никогда не универсальная:
`rotate_hurts_constant` — константный вектор поворот КОНЦЕНТРИРУЕТ
(H · 1 = 2^k · e₀, cohSq(H1) = 1 > 1/2^k = cohSq(1)), гейт честно
откажет.
-/

open scoped Matrix Classical

namespace Hagi.Theory.HadamardIncoherence

open Hagi.Core Hagi.Runtime

variable (k : ℕ)

/-- Целочисленный (±1) Hadamard Sylvester в ℚ — без нормировки
1/√(2^k): сравнение cohSq масштабно-инвариантно (`cohSq_smul`),
иррациональности не нужны. -/
def hadamardQ : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℚ :=
  (sylvester k).map (algebraMap ℤ ℚ)

variable {k}

/-- Hadamard-поворот вектора: `H *ᵥ w` (целочисленный H). -/
def rotate (w : (Fin k → ZMod 2) → ℚ) : (Fin k → ZMod 2) → ℚ :=
  hadamardQ k *ᵥ w

/-- Квадрат ℓ₂-нормы: `∑ i, w i * w i` (ℚ, вычислимо). -/
def l2Sq (w : (Fin k → ZMod 2) → ℚ) : ℚ :=
  ∑ i, w i * w i

/-- ∞-норма: sup' |w j| по явно перечислимому кубу (ℚ, вычислимо). -/
def infNorm (w : (Fin k → ZMod 2) → ℚ) : ℚ :=
  Finset.univ.sup' (⟨fun _ => 0, Finset.mem_univ _⟩) (fun j => |w j|)

/-- ИЗМЕРЯЕМАЯ когерентность (в квадрате):
`cohSq w = ‖w‖∞² / ‖w‖₂²` — ℚ-выражение без корней. Для ненулевого
вектора cohSq ∈ [1/2^k, 1]; cohSq = 1 ⟺ вся энергия в одной
координате (худший случай для тернарного квантования). Нулевой
вектор вырожден (0/0 = 0 в ℚ-поле) — гейт имеет смысл для w ≠ 0. -/
def cohSq (w : (Fin k → ZMod 2) → ℚ) : ℚ :=
  infNorm w ^ 2 / l2Sq w

/-! ### Базовые оценки ∞-нормы -/

/-- Каждая координата ограничена ∞-нормой. -/
theorem le_infNorm (w : (Fin k → ZMod 2) → ℚ) (j : Fin k → ZMod 2) :
    |w j| ≤ infNorm w :=
  Finset.le_sup' (fun j => |w j|) (Finset.mem_univ j)

/-- По-координатная граница мажорирует ∞-норму. -/
theorem infNorm_le (w : (Fin k → ZMod 2) → ℚ) (c : ℚ)
    (h : ∀ j, |w j| ≤ c) : infNorm w ≤ c :=
  Finset.sup'_le _ _ fun j _ => h j

/-! ### Целочисленный Парсевал: энергия не теряется -/

/-- Целочисленный Sylvester симметричен: `Hᵀ = H` (ℚ-версия). -/
theorem hadamardQ_transpose : (hadamardQ k)ᵀ = hadamardQ k := by
  unfold hadamardQ
  rw [← Matrix.transpose_map]
  exact congrArg (fun M : Matrix _ _ ℤ => M.map (algebraMap ℤ ℚ))
    sylvester_transpose

/-- `H · Hᵀ = 2^k • 1` (ℚ-версия, из `sylvester_mul_transpose`). -/
theorem hadamardQ_mul_transpose :
    hadamardQ k * (hadamardQ k)ᵀ = ((2 ^ k : ℕ) : ℚ) • 1 := by
  have h1 : hadamardQ k * (hadamardQ k)ᵀ
      = ((sylvester k) * (sylvester k)ᵀ).map (algebraMap ℤ ℚ) := by
    rw [hadamardQ, ← Matrix.transpose_map, ← Matrix.map_mul]
  rw [h1, sylvester_mul_transpose]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split <;> simp

/-- ЦЕЛОЧИСЛЕННЫЙ ПАРСЕВАЛ: поворот не теряет энергию —
`‖H w‖₂² = 2^k · ‖w‖₂²`. Для ортонормированного Q = H/√(2^k) это
`‖Q w‖₂ = ‖w‖₂`: квантование в повёрнутом базисе начинается с той
же ℓ₂-энергии (матричная форма; доменная projector-форма —
`Hagi.Learning.HadamardParseval.parseval`, цикл 26). Связь с гейтом:
знаменатель cohSq(Hw) = 2^k · знаменатель cohSq(w) — сравнение гейта
сводится к сравнению числителей `‖Hw‖∞² < 2^k · ‖w‖∞²`. -/
theorem rotate_energy_eq (w : (Fin k → ZMod 2) → ℚ) :
    l2Sq (rotate w) = ((2 ^ k : ℕ) : ℚ) * l2Sq w := by
  have hd : (hadamardQ k *ᵥ w) ⬝ᵥ (hadamardQ k *ᵥ w)
      = ((hadamardQ k)ᵀ *ᵥ (hadamardQ k *ᵥ w)) ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hmm : ((hadamardQ k)ᵀ *ᵥ (hadamardQ k *ᵥ w))
      = ((hadamardQ k)ᵀ * hadamardQ k) *ᵥ w :=
    Matrix.mulVec_mulVec _ _ _
  have hsym : (hadamardQ k)ᵀ * hadamardQ k
      = hadamardQ k * (hadamardQ k)ᵀ := by
    rw [hadamardQ_transpose]
  unfold l2Sq rotate
  rw [show ∑ j, (hadamardQ k *ᵥ w) j * (hadamardQ k *ᵥ w) j
      = (hadamardQ k *ᵥ w) ⬝ᵥ (hadamardQ k *ᵥ w) from rfl,
    hd, hmm, hsym, hadamardQ_mul_transpose, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Масштабная инвариантность cohSq -/

/-- ℓ₂² гомогенен: `l2Sq (c • w) = c² · l2Sq w`. -/
theorem l2Sq_smul (c : ℚ) (w : (Fin k → ZMod 2) → ℚ) :
    l2Sq (fun i => c * w i) = c * c * l2Sq w := by
  unfold l2Sq
  calc ∑ i, (fun i => c * w i) i * (fun i => c * w i) i
      = ∑ i, c * c * (w i * w i) := Finset.sum_congr rfl fun i _ => by
        show c * w i * (c * w i) = c * c * (w i * w i)
        ring
    _ = c * c * ∑ i, w i * w i := by rw [Finset.mul_sum]

/-- ∞-норма положительно-гомогенна. -/
theorem infNorm_smul (c : ℚ) (hc : 0 < c) (w : (Fin k → ZMod 2) → ℚ) :
    infNorm (fun i => c * w i) = c * infNorm w := by
  apply le_antisymm
  · refine infNorm_le _ _ fun j => ?_
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (le_infNorm w j) hc.le
  · have h : ∀ j, |w j| = c⁻¹ * |c * w j| := by
      intro j
      rw [abs_mul, abs_of_pos hc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc),
        one_mul]
    have h2 : infNorm w ≤ c⁻¹ * infNorm (fun i => c * w i) :=
      infNorm_le _ _ fun j => by
        rw [h j]
        exact mul_le_mul_of_nonneg_left (le_infNorm _ j) (inv_nonneg.mpr hc.le)
    have h3 : c * infNorm w ≤ c * (c⁻¹ * infNorm (fun i => c * w i)) :=
      mul_le_mul_of_nonneg_left h2 hc.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h3
    exact h3

/-- МАСШТАБНАЯ ИНВАРИАНТНОСТЬ ИЗМЕРЯЕМОГО ГЕЙТА:
`cohSq (c • w) = cohSq w` при c > 0 и w ≠ 0. Следствие: сравнение
cohSq(Hw) < cohSq(w) НЕ зависит от нормировки матрицы —
целочисленный H (±1, без 1/√n) даёт то же решение гейта, что и
ортонормированный Q = H/√n; иррациональности исключены. -/
theorem cohSq_smul (c : ℚ) (hc : 0 < c) (w : (Fin k → ZMod 2) → ℚ)
    (hw : l2Sq w ≠ 0) :
    cohSq (fun i => c * w i) = cohSq w := by
  unfold cohSq
  rw [infNorm_smul c hc, l2Sq_smul]
  field_simp

/-! ### Гейт: rotate-if-measured-better -/

/-- ГЕЙТ ПОЛЕЗНОСТИ ПОВОРОТА (rotate-if-measured-better):
строгое ℚ-неравенство `cohSq (H w) < cohSq w`. Обе части вычислимы
(max + сумма по явному списку) — решение принимает исполнимая
арифметика (CertifiedArgmax-строгость), а не постулат. По
`rotate_energy_eq` сравнение эквивалентно `‖Hw‖∞² < 2^k · ‖w‖∞²`.
Польза условная: применение только при pass; негатив
`rotate_hurts_constant` показывает, что pass не гарантирован. -/
def hadamardRotateBenefits (k : ℕ) (w : (Fin k → ZMod 2) → ℚ) : Prop :=
  cohSq (rotate (k := k) w) < cohSq w

/-! ### Негатив: поворот НЕ универсально полезен -/

/-- Первая координата образа константного вектора: `H · 1 = 2^k` в
нулевой характер (все χ(0·i) = 1, сумма по кубу). -/
theorem rotate_ones_zero :
    rotate (k := k) (fun _ => (1 : ℚ)) (fun _ => (0 : ZMod 2))
      = ((2 ^ k : ℕ) : ℚ) := by
  have hexpand : rotate (k := k) (fun _ => (1 : ℚ)) (fun _ => (0 : ZMod 2))
      = ((∑ i : Fin k → ZMod 2, chi2 (∑ l, (0 : Fin k → ZMod 2) l * i l) : ℤ) : ℚ) := by
    unfold rotate hadamardQ
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, sylvester_apply,
      algebraMap_int_eq, one_mul]
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  rw [hexpand]
  have hone : ∀ i : Fin k → ZMod 2,
      chi2 (∑ l, (0 : Fin k → ZMod 2) l * i l) = 1 := by
    intro i
    have hz : ∑ l, (0 : Fin k → ZMod 2) l * i l = 0 := by
      rw [Finset.sum_congr rfl
          (fun l _ => by rw [Pi.zero_apply, zero_mul]),
        Finset.sum_const_zero]
    rw [hz, chi2_zero]
  have hsum : (∑ i : Fin k → ZMod 2,
      chi2 (∑ l, (0 : Fin k → ZMod 2) l * i l) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by
    rw [Finset.sum_congr rfl fun i _ => hone i, Finset.sum_const]
    simp
  rw [hsum]
  push_cast
  ring

/-- Ненулевой характер: образ константного вектора нулевой
(сумма характера по кубу, `sum_chi2_eq_zero`). -/
theorem rotate_ones_ne {j : Fin k → ZMod 2} (hj : j ≠ 0) :
    rotate (k := k) (fun _ => (1 : ℚ)) j = 0 := by
  have hexpand : rotate (k := k) (fun _ => (1 : ℚ)) j
      = ((∑ i : Fin k → ZMod 2, chi2 (∑ l, j l * i l) : ℤ) : ℚ) := by
    unfold rotate hadamardQ
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, sylvester_apply,
      algebraMap_int_eq, one_mul]
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  rw [hexpand]
  exact_mod_cast sum_chi2_eq_zero hj

/-- НЕГАТИВ (зеркало корпусного `hadamard_not_universally_incoherent`):
Hadamard-поворот КОНЦЕНТРИРУЕТ константный вектор —
`H · 1 = 2^k · e₀`, поэтому `cohSq (H · 1) = 1 > 1/2^k = cohSq(1)`:
гейт hadamardRotateBenefits честно ОТКАЖЕТ в повороте. Полезность
поворота — всегда УСЛОВНЫЙ (измеренный) факт, не свойство матрицы. -/
theorem rotate_hurts_constant (hk : 1 ≤ k) :
    ¬ hadamardRotateBenefits k (fun _ => (1 : ℚ)) := by
  have hinf : infNorm (rotate (k := k) (fun _ => (1 : ℚ)))
      = ((2 ^ k : ℕ) : ℚ) := by
    apply le_antisymm
    · refine infNorm_le _ _ fun j => ?_
      rcases eq_or_ne j 0 with hj | hj
      · rw [hj]
        show |rotate (k := k) (fun _ => (1 : ℚ)) (fun _ => (0 : ZMod 2))|
            ≤ ((2 ^ k : ℕ) : ℚ)
        rw [rotate_ones_zero, abs_of_nonneg (by positivity)]
      · rw [rotate_ones_ne hj]
        norm_num
    · have h := le_infNorm (rotate (k := k) (fun _ => (1 : ℚ)))
        (fun _ => (0 : ZMod 2))
      rw [rotate_ones_zero] at h
      simpa using h
  have hl2 : l2Sq (rotate (k := k) (fun _ => (1 : ℚ)))
      = ((2 ^ k : ℕ) : ℚ) ^ 2 := by
    rw [rotate_energy_eq]
    unfold l2Sq
    rw [Finset.sum_const]
    simp
    ring
  have hl2w : l2Sq (k := k) (fun _ => (1 : ℚ)) = ((2 ^ k : ℕ) : ℚ) := by
    unfold l2Sq
    rw [Finset.sum_const]
    simp
  have hinfw : infNorm (k := k) (fun _ => (1 : ℚ)) = 1 := by
    apply le_antisymm
    · exact infNorm_le _ _ (fun _ => by simp)
    · have h := le_infNorm (k := k) (fun _ => (1 : ℚ)) (fun _ => (0 : ZMod 2))
      simpa using h
  unfold hadamardRotateBenefits cohSq
  rw [hinf, hl2, hinfw, hl2w]
  intro hlt
  have hden : ((2 ^ k : ℕ) : ℚ) ^ 2 ≠ 0 := by positivity
  have hc2 : (2 : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by
    have h : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : (2 : ℕ) = (2 : ℕ) ^ 1 := by ring
    rw [h2]
    exact_mod_cast h
  rw [div_self hden, one_pow, one_div] at hlt
  have hinv : ((2 ^ k : ℕ) : ℚ)⁻¹ ≤ (2 : ℚ)⁻¹ := by
    rw [inv_le_inv₀]
    · exact hc2
    · positivity
    · positivity
  nlinarith

/-! ### Условная тернарная польза: оценка хвоста насыщения -/

/-- КОЛИЧЕСТВЕННАЯ ОЦЕНКА ХВОСТА НАСЫЩЕНИЯ (f(M, s)-форма,
семейство ternary_split_le): если каждая координата ограничена
`|w i| ≤ M` и масштаб `s ≤ M`, то каждый насыщенный член
`(|w i| − s)² ≤ (M − s)²`, а число насыщенных координат ≤ n, hence
`satTail s w ≤ n · (M − s)²`. При `M ≤ 3s/2` хвост нулевой
(интерпретация моста `hadamard_satTail_zero_of_l2_bound`:
μ-премиса ⇒ в-диапазон). Гейт уменьшает измеренный
M := infNorm — условная польза поворота: меньше M ⇒ меньше/нуль
хвост при том же s. -/
theorem satTail_le_of_forall_le {n : ℕ} (s M : ℝ) (w : Fin n → ℝ)
    (hM : ∀ i, |w i| ≤ M) (hs : 0 < s) (hsM : s ≤ M) :
    satTail s w ≤ (n : ℝ) * (M - s) ^ 2 := by
  have hcard : (Finset.univ.filter (fun i => ¬ ternInRange s (w i))).card ≤ n := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_univ, Fintype.card_fin]
  calc satTail s w
      = ∑ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)),
          (|w i| - s) ^ 2 := rfl
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)),
          (M - s) ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hns := (Finset.mem_filter.mp hi).2
        unfold ternInRange at hns
        push_neg at hns
        have h1 : 0 ≤ |w i| - s := by linarith [abs_nonneg (w i)]
        have h2 : |w i| - s ≤ M - s := by linarith [hM i, abs_nonneg (w i)]
        nlinarith [sq_nonneg (|w i| - s)]
    _ = (Finset.univ.filter (fun i => ¬ ternInRange s (w i))).card * (M - s) ^ 2 := by
        simp
    _ ≤ (n : ℝ) * (M - s) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by nlinarith)
        exact Nat.cast_le.mpr hcard

end Hagi.Theory.HadamardIncoherence
