import Hagi.Information.Pinsker
import Hagi.Probability.PinskerTV
import Hagi.Unified.ArchitectureTheorem

namespace Hagi.Unified

/-!
# Pinsker — единая точка входа семейства Пинскера (P1.5)

Консолидация форм неравенства Пинскера (план P1.5;
дубли «Pinsker×2 + KL/TV-модули»):

* **Функциональная форма** (`Hagi.Information.Pinsker`,
  `pinsker4_fin`): |E_q f − E_p f| ≤ 2√KL для 0 ≤ f ≤ 1;
* **TV-форма** (`Hagi.Probability.PinskerTV`,
  `pinsker_sqrt_kl`): ½ Σ|p−q| ≤ √KL — классика через
  Бхаттачарью;
* **Энтропийная непрерывность** (`entropy_continuity_pinsker`
  и `'`-вариант в этом же модуле Unified): Фанне-Пинскер
  оценка |H(p) − H(q)|.

Все формы на канонических `Prelude.klDef/entDef/tvDef`;
настоящий модуль — фасад и реестр форм (P1.5), дубликатных
определений нет.
-/

/-- ДЕДУП-МОСТ (аудит v5 п.5): f-форма Пинскера
(pinsker4_fin, Information) выводится из канонной TV-формы
(pinsker_sqrt_kl, Probability): разность ожиданий ограничена
тотал-вариацией, TV ≤ √KL. Копии связаны, примитив один. -/
theorem pinsker4_via_canon {V : Type*} [Fintype V] [Nonempty V]
    (q p f : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
  -- |Eq f − Ep f| ≤ Σ|q − p|
  have hstep : ∀ v, |(q v - p v) * f v| ≤ |q v - p v| := by
    intro v
    have h1 : |(q v - p v) * f v| = |q v - p v| * |f v| :=
      abs_mul _ _
    rw [h1, mul_comm]
    have h2 : |f v| ≤ 1 := by
      rcases lt_or_ge (f v) 0 with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith [(hf v).1]
      · rw [abs_of_nonneg h]
        exact (hf v).2
    nlinarith [h2, abs_nonneg (q v - p v)]
  have habs : abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := by
    have hsplit : ∑ v, q v * f v - ∑ v, p v * f v
        = ∑ v, (q v - p v) * f v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hsplit]
    calc abs (∑ v, (q v - p v) * f v)
        ≤ ∑ v, |(q v - p v) * f v| :=
          Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ v, |q v - p v| :=
          Finset.sum_le_sum (fun v _ => hstep v)
  -- канон: ½Σ|p−q| ≤ √KL(p||q) = √klDef q p (симметрия ролей)
  have hcanon := Hagi.Probability.pinsker_sqrt_kl q p hq hsumq
    hp hsump
  -- klDef q p = Σ q·log(q/p): канон даёт Σ p·log(p/q) с
  -- ролями (q,p) → Σ q·log(q/p) = klDef q p ✓
  calc abs (∑ v, q v * f v - ∑ v, p v * f v)
      ≤ ∑ v, |q v - p v| := habs
    _ = 2 * ((1/2) * ∑ v, |q v - p v|) := by ring
    _ ≤ 2 * Real.sqrt (Hagi.Prelude.klDef q p) := by
        apply mul_le_mul_of_nonneg_left hcanon (by norm_num)

end Hagi.Unified
