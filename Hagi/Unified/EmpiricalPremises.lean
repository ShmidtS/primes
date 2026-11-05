import Mathlib.Tactic
import Hagi.Foundations.StageCalculus

set_option linter.style.header false

/-!
# EmpiricalPremises — единый реестр эмпирических посылок (цикл 40, аудит #8 п.2)

Проблема аудита: ≥50 разнородных `h_emp_*`-посылок в
сигнатурах 89 теорем — реестр скриптом есть (AssumptionScan),
единой СТРУКТУРЫ нет. Здесь — канонический реестр:

`EmpiricalPremises` — измеряемые величины обучения
(гладкость L, кривизна κ, шаг η, стадийные коэффициенты,
шумовая модель), на которых работает единый монитор `holds`.
Он НЕ выводит гладкость произвольной энергии:

- `holds` — конъюнкция измеримых неравенств; при нарушении
  любого поля цикл уходит в hold;
- `premises_give_smooth` лишь компонует `holds` с ЯВНО
  принятой модельной `hsmooth` и направлением `hdir`;
- `premises_lip_witness` доказывает только неотрицательность
  κ·s·dnorm, а не саму ledger-границу энергии;
- `premises_noise_cases` разбивает шум на нулевой/положительный.

89 теорем с h_emp-сигнатурами НЕ переписываются; мост
даёт единый слой мониторинга, но не устраняет исходные
модельные и вероятностные посылки.
-/

namespace Hagi.Unified.EmpiricalPremises

/-- Измеряемые эмпирические величины обучения (реестр).
Каждое поле — измеримая константа; предикат `holds` —
монитор. -/
structure EmpiricalPremises where
  /-- Измеренная константа Липшица градиента. -/
  L : ℝ
  /-- Измеренная кривизна энергии (квантование). -/
  kappa : ℝ
  /-- Рабочая скорость обучения. -/
  eta : ℝ
  /-- Измеренный типичный размер шага параметров. -/
  dnorm : ℝ
  /-- Измеренный inner-зазор ⟨g, d⟩ (спуск-направление). -/
  inner : ℝ
  /-- Шумовой бюджет шага (станд. отклонение). -/
  noiseSigma : ℝ

/-- МОНИТОР: все измеримые неравенства реестра. Нарушение
любого поля ⇒ holds = False ⇒ цикл должен уходить в hold. -/
def holds (p : EmpiricalPremises) : Prop :=
  0 < p.L ∧ 0 < p.kappa ∧ 0 < p.eta ∧ p.eta ≤ 2
    ∧ p.L * p.eta ≤ 1
    ∧ 0 ≤ p.dnorm ∧ p.inner ≤ p.L * p.dnorm ^ 2
    ∧ 0 ≤ p.noiseSigma

/-- МОСТ 1 (smooth-форма): при ЯВНО принятой модельной
`hsmooth`, направлении `hdir` и мониторе `holds` получаем
сертифицированное убывание. Монитор контролирует L и η,
но сам не доказывает `hsmooth`. -/
theorem premises_give_smooth (p : EmpiricalPremises)
    (E1 E2 : ℝ) (h : holds p)
    (hdir : p.dnorm ^ 2 ≤ p.inner)
    (hsmooth : E2 ≤ E1 - p.eta * p.inner
      + p.L * p.eta ^ 2 * p.dnorm ^ 2 / 2) :
    E2 ≤ E1 - p.eta * p.dnorm ^ 2 / 2 := by
  obtain ⟨hL, hκ, hη0, hη2, hηL, hdn, _⟩ := h
  -- из hsmooth: E2 ≤ E1 − η·inner + L·η²·dn²/2
  -- с inner ≥ dn²: −η·inner ≤ −η·dn²
  -- нужно: L·η²·dn²/2 ≤ η·dn²/2, т.е. L·η ≤ 1 (монитор holds)
  have hkey : p.L * p.eta ^ 2 * p.dnorm ^ 2 / 2
      ≤ p.eta * p.dnorm ^ 2 / 2 := by
    have hnn : (0:ℝ) ≤ p.dnorm ^ 2 := sq_nonneg _
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [h0.symm]
      simp
    · rw [div_le_div_iff₀ (show (0:ℝ) < 2 from by norm_num)]
      have hmid : p.L * p.eta * p.dnorm ^ 2 ≤ 1 * p.dnorm ^ 2 := by
        nlinarith [hηL, hnn]
      nlinarith [hmid]
      norm_num
  calc E2 ≤ E1 - p.eta * p.inner
        + p.L * p.eta ^ 2 * p.dnorm ^ 2 / 2 := hsmooth
    _ ≤ E1 - p.eta * p.dnorm ^ 2
        + p.L * p.eta ^ 2 * p.dnorm ^ 2 / 2 := by
        nlinarith [hdir]
    _ ≤ E1 - p.eta * p.dnorm ^ 2 / 2 := by nlinarith

/-- МОСТ 2 (lip-форма): монитор контролирует измеренную
кривизну κ>0 и зазор s≥0 — форма h_emp_lip стадии merge
(E3−E2pre ≤ κ·s·dnorm) принимается с κ, s, dnorm ИЗ реестра. -/
theorem premises_lip_witness (p : EmpiricalPremises)
    (s : ℝ) (h : holds p) (hs : 0 ≤ s) :
    0 ≤ p.kappa * s * p.dnorm := by
  obtain ⟨hL, hκ, hη0, _, _, hdn, _⟩ := h
  exact mul_nonneg (mul_nonneg hκ.le hs) hdn

/-- МОСТ 3 (шум): monitor noiseSigma контролирует
шумовую составляющую: при noiseSigma = 0 измерение точное
(форма h_emp_noise_zero), при > 0 — бюджет шума
(h_emp_noise_bound). -/
theorem premises_noise_cases (p : EmpiricalPremises)
    (h : holds p) :
    p.noiseSigma = 0 ∨ 0 < p.noiseSigma := by
  obtain ⟨_, _, _, _, _, _, _, hσ⟩ := h
  rcases eq_or_lt_of_le hσ with h' | h'
  · exact Or.inl h'.symm
  · exact Or.inr h'

end Hagi.Unified.EmpiricalPremises
