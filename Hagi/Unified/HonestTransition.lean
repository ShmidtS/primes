import Mathlib

/-!
# HonestTransition 

Дефект старого `CertifiedTransition.progress`: оно
сертифицирует ПОЛОЖИТЕЛЬНОСТЬ ВЫЧИСЛЯЕМОГО ПОКАЗАТЕЛЯ
(verify.decrease), а не реальное улучшение модели.
Аудитор привёл контрпример: E(S)=0, G_grow=1,
E_compress=100 — положительный сертификат при росте
энергии.

`HonestTransition` устраняет разрыв по построению:
спуск — не вычисляемый показатель, а ДОКАЗАННАЯ связь
`objective S' ≤ objective S - objectiveDrop` между
реальным исполнением и реальной функцией.

Ключевые гарантии:
1. `honest_actual_drop`: из сертификата следует точный
   реальный спуск (нельзя сертифицировать рост);
2. `honest_telescope`: два последовательных честных
   перехода кумулятивны (обструкция двухшаговости старой
   GrowthState-семантики здесь НЕВОЗМОЖНА по построению —
   эффекты не хранятся в состоянии);
3. `honest_two_steps_existent`: конкретный свидетель
   (квадратичная машина) двух продуктивных переходов.
-/

namespace Hagi.Unified.HonestTransition

variable {S : Type*}

/-- Честный переход: спуск связан с objective-функцией
зависимым доказательством, не с показателем. -/
structure HonestTransition (obj : S → ℝ)
    (s s' : S) (riskSpend riskLim budgetSpend : ℝ)
    (budget' : ℝ) where
  /-- Реальное уменьшение (нижняя сертифицированная
  граница). -/
  objectiveDrop : ℝ
  objectiveDrop_pos : 0 < objectiveDrop
  /-- ГЛАВНОЕ: реальный спуск, выведенный из исполнения. -/
  actualDescent : obj s' ≤ obj s - objectiveDrop
  /-- Риск шага ограничен. -/
  riskBound : riskSpend ≤ riskLim
  /-- Бюджет шага ограничен, остаток неотрицателен. -/
  budgetBound : 0 ≤ budget'

/-- Сертификат ⇒ реальное строгое убывание
(заключение ссылается на поле сертификата:
положительный спуск-сертификат невозможен при росте). -/
theorem honest_actual_drop (obj : S → ℝ) (s s' : S)
    (rs rl bs b' : ℝ)
    (T : HonestTransition obj s s' rs rl bs b') :
    obj s' < obj s ∧ 0 < T.objectiveDrop := by
  exact ⟨by
    have h1 := T.actualDescent
    have h2 := T.objectiveDrop_pos
    linarith, T.objectiveDrop_pos⟩

/-- Телескоп: два честных перехода кумулятивны.
Сравни с corePremises_two_step_decrease_nonpos старой
семантики: здесь противоречие НЕВОЗМОЖНО, т.к. каждый
переход несёт собственное доказательство спуска. -/
theorem honest_telescope (obj : S → ℝ) (s0 s1 s2 : S)
    (rs1 rl1 bs1 b1 rs2 rl2 bs2 b2 : ℝ)
    (T1 : HonestTransition obj s0 s1 rs1 rl1 bs1 b1)
    (T2 : HonestTransition obj s1 s2 rs2 rl2 bs2 b2) :
    obj s2 ≤ obj s0 - (T1.objectiveDrop + T2.objectiveDrop) := by
  have h1 := T1.actualDescent
  have h2 := T2.actualDescent
  linarith

/-- Конкретный свидетель двух продуктивных честных
переходов: E(w)=w², траектория 2 → 1 → ½:
E: 4 → 1 → ¼, точные спуски 3 и ¾. -/
noncomputable def quadObj (w : ℝ) : ℝ := w * w

theorem honest_two_steps_existent :
    ∃ (d1 d2 : ℝ), 0 < d1 ∧ 0 < d2 ∧
      quadObj 1 ≤ quadObj 2 - d1 ∧
      quadObj (1 / 2) ≤ quadObj 1 - d2 := by
  refine ⟨3, 3 / 4, by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num [quadObj]

end Hagi.Unified.HonestTransition
