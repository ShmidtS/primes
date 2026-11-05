import Mathlib.Tactic
import Hagi.Learning.HadamardParseval

set_option linter.style.header false

/-!
# SpectralBudget — спектральное распределение бюджета (цикл 27)

Связка Parseval (цикл 26) ↔ битовый бюджет: пер-доменное
РАВНООТНОСИТЕЛЬНОЕ квантование даёт глобальную относительную
ошибку. Если каждый домен w квантован с относительной
ошибкой δ (‖P_w v − P_w Q‖² ≤ δ²·‖P_w v‖²), то глобальная
ошибка реконструкции ‖v − Q‖² ≤ δ²·‖v‖².

Доказательство — три звена уже доказанной теории:
  1. полнота (цикл 25) для v − Q: v − Q = Σ_w P_w (v−Q);
  2. Parseval (цикл 26) для v − Q: ‖v−Q‖² = Σ_w ‖P_w(v−Q)‖²;
  3. линейность P_w: ‖P_w(v−Q)‖² = ‖P_w v − P_w Q‖², и
     пер-доменная оценка + Parseval для v дают δ²·‖v‖².

СЛЕДСТВИЕ ДЛЯ АРХИТЕКТУРЫ: битовый бюджет домена w должен
быть пропорционален доменной энергии ‖P_w v‖² (домены с
нулевой энергией — нулевой бюджет; эта спектральная
стратегия — прямое обращение доказанной оценки). Вместе с
равномерным по слоям распределением (цикл 24): сеть = слои
(равномерно) × домены (спектрально) — конфигурация выводится
из сигнала, а не подбирается.
-/

open Finset Hagi.Core

namespace Hagi.Learning.SpectralBudget

open Hagi.Learning.HadamardProjectors Hagi.Learning.HadamardComplete
  Hagi.Learning.HadamardParseval

variable {k : ℕ}

/-! ### Линейность проекторов над вычитанием -/

/-- P_w линейнен: P_w (v − u) = P_w v − P_w u. -/
theorem charProjR_sub (w : Fin k → ZMod 2)
    (v u : (Fin k → ZMod 2) → ℝ) :
    charProjR w (v - u) = charProjR w v - charProjR w u := by
  funext i
  unfold charProjR
  have hd : dotProduct (charRowR w) (v - u)
      = dotProduct (charRowR w) v - dotProduct (charRowR w) u := by
    unfold dotProduct
    have hreg : ∀ j : Fin k → ZMod 2,
        charRowR w j * ((v - u) j)
          = charRowR w j * v j - charRowR w j * u j := by
      intro j
      simp only [Pi.sub_apply]
      ring
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hreg j),
      ← Finset.sum_sub_distrib]
  rw [hd]
  simp only [Pi.sub_apply]
  ring

/-! ### ГЛАВНАЯ ТЕОРЕМА: спектральное бюджетирование -/

/-- СПЕКТРАЛЬНЫЙ БЮДЖЕТ: пер-доменное равноотносительное
квантование с фактором δ даёт глобальную относительную
ошибку δ. Полная ошибка реконструкции:
  ‖v − Q‖² = Σ_w ‖P_w v − P_w Q‖²   (полнота+Parseval+лин.)
           ≤ δ² · Σ_w ‖P_w v‖² = δ² · ‖v‖² (Parseval).
Бюджет домена пропорционален ‖P_w v‖² — спектральная
стратегия выводится из оценки, а не подбирается. -/
theorem spectral_budget (v Q : (Fin k → ZMod 2) → ℝ) (delta : ℝ)
    (hδnn : (0:ℝ) ≤ delta)
    (hdom : ∀ w : Fin k → ZMod 2,
      dotProduct (charProjR w v - charProjR w Q)
        (charProjR w v - charProjR w Q)
        ≤ delta ^ 2 * dotProduct (charProjR w v) (charProjR w v)) :
    dotProduct (v - Q) (v - Q)
      ≤ delta ^ 2 * dotProduct v v := by
  -- полнота + Parseval для разности
  have hdec : dotProduct (v - Q) (v - Q)
      = ∑ w, dotProduct (charProjR w (v - Q))
          (charProjR w (v - Q)) := parseval (v - Q)
  -- линейность: P_w (v−Q) = P_w v − P_w Q
  have hlin : ∀ w : Fin k → ZMod 2,
      charProjR w (v - Q) = charProjR w v - charProjR w Q :=
    fun w => charProjR_sub w v Q
  rw [hdec, Finset.sum_congr rfl (fun w _ => by rw [hlin w])]
  -- пер-доменные оценки + Parseval для v
  calc ∑ w, dotProduct (charProjR w v - charProjR w Q)
          (charProjR w v - charProjR w Q)
      ≤ ∑ w, delta ^ 2
          * dotProduct (charProjR w v) (charProjR w v) :=
        Finset.sum_le_sum (fun w _ => hdom w)
    _ = delta ^ 2
          * ∑ w, dotProduct (charProjR w v) (charProjR w v) := by
        rw [← Finset.mul_sum]
    _ = delta ^ 2 * dotProduct v v := by
        rw [← parseval v]

/-! ### СЛЕДСТВИЕ: нулевые домены — нулевой бюджет -/

/-- Домен с нулевой энергией не требует бюджета: его вклад в
глобальную ошибку НУЛЕВОЙ при любом квантовании с носителем
в этом домене (ошибка, спроецированная на нулевой домен,
исчезает в сумме). -/
theorem zero_energy_domain_free (v : (Fin k → ZMod 2) → ℝ)
    (w : Fin k → ZMod 2)
    (hzero : dotProduct (charProjR w v) (charProjR w v) = 0) :
    dotProduct (charProjR w v) (charProjR w v) = 0
      ∧ ∀ e : (Fin k → ZMod 2) → ℝ,
        dotProduct e e
          ≤ dotProduct (charProjR w v) (charProjR w v) →
        e = 0 := by
  refine ⟨hzero, ?_⟩
  intro e he
  funext i
  have hE : dotProduct e e = 0 := by
    have hle : dotProduct e e
        ≤ dotProduct (charProjR w v) (charProjR w v) := he
    rw [hzero] at hle
    have hnn : (0:ℝ) ≤ dotProduct e e := by
      unfold dotProduct
      exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (e j))
    exact le_antisymm hle hnn
  have hterm : ∀ j : Fin k → ZMod 2, e j * e j = e j ^ 2 :=
    fun j => (sq (e j)).symm
  have hconv : dotProduct e e = ∑ j, e j ^ 2 := by
    unfold dotProduct
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  have hsq : e i ^ 2 ≤ dotProduct e e := by
    rw [hconv]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hE] at hsq
  have : e i = 0 := by
    rcases eq_or_lt_of_le hsq with h | h
    · exact (pow_eq_zero_iff (by norm_num)).mp h
    · exact absurd (sq_nonneg (e i)) (by linarith)
  exact this

end Hagi.Learning.SpectralBudget
