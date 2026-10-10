/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.DField

set_option linter.style.header false

/-!
# MDLThreeCurrency — цель обучения в трёх валютах

Развивает MDLObjective (две величины, одна λ) до честной
трёхвалютной цели (рецензия на Monotone Compression,
arXiv:2610.11031):

  J(θ, M) = L_pred(θ) + λ_M·C_state(M) + λ_R·R_protected(M),

где L_pred — качество предсказаний (кросс-энтропия данных),
C_state — размер хранимого состояния (биты/байты), R_protected
— риск забывания защищаемых задач. Валюты НЕРАВНОЦЕННЫ и не
сводятся друг к другу без явных мостов.

Доказано:
* `J3_nonincreasing`: если все три слагаемых не растут и веса
  неотрицательны — J3 не растёт (обобщение
  mdlObjective_nonincreasing);
* `double_counting_identified`: если стоимость состояния
  НАИВНО приравнять длине кода данных (dataCode = L_pred при
  идеальном арифметическом коде по модели), J3 вырождается в
  (1 + λ_M)·L_pred + λ_R·R — двойной учёт ОПОЗНАЁТСЯ
  алгебраически: одна и та же компрессия посчитана дважды;
* `no_compression_below_entropy`: при кодировании данных по
  модели ожидаемая длина (−log p_model) не ниже энтропии
  источника — мост из kl_nonneg (кросс-энтропия ≥ энтропия);
  сжатие данных не может обойти источник.

Честная граница: bridges от весов/состояния модели к этим
трём валютам — измеряемые контракты; здесь формализована
арифметика цели и опознание двойного учёта.
-/

open Finset

namespace Hagi.MDLThreeCurrency

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Трёхвалютная цель: предсказание + стоимость состояния +
риск забывания. -/
def J3 (Lpred Cstate Rprot : ℝ) (lamM lamR : ℝ) : ℝ :=
  Lpred + lamM * Cstate + lamR * Rprot

/-- Если все три слагаемых не растут и веса неотрицательны,
J3 не растёт (обобщение двухвалютной
mdlObjective_nonincreasing). -/
theorem J3_nonincreasing (Lp Lp' Cst Cst' Rp Rp' lamM lamR : ℝ)
    (hp : Lp' ≤ Lp) (hc : Cst' ≤ Cst) (hr : Rp' ≤ Rp)
    (hM : 0 ≤ lamM) (hR : 0 ≤ lamR) :
    J3 Lp' Cst' Rp' lamM lamR ≤ J3 Lp Cst Rp lamM lamR := by
  have h1 : lamM * Cst' ≤ lamM * Cst :=
    mul_le_mul_of_nonneg_left hc hM
  have h2 : lamR * Rp' ≤ lamR * Rp :=
    mul_le_mul_of_nonneg_left hr hR
  unfold J3
  linarith

/-- Двойной учёт опознан: если стоимость состояния наивно
приравнять длине кода данных — которая при идеальном
арифметическом коде ПО МОДЕЛИ равна кросс-энтропии L_pred —
то J3 вырождается в (1 + λ_M)·L_pred + λ_R·R: одна и та же
компрессия посчитана дважды. Это алгебраический тест на
ошибку подмены валют. -/
theorem double_counting_identified (Lpred Rprot lamM lamR : ℝ)
    (cst : ℝ) (hcode : cst = Lpred) :
    J3 Lpred cst Rprot lamM lamR
      = (1 + lamM) * Lpred + lamR * Rprot := by
  unfold J3
  rw [hcode]
  ring

/-- Идеальный арифметический код по модели: ожидаемая длина
кодового слова для символа v равна −log q v. -/
noncomputable def dataCodeLen (p q : V → ℝ) : ℝ :=
  ∑ v, p v * (-Real.log (q v))

/-- Энтропия источника: ∑ p·(−log p). -/
noncomputable def sourceEntropy (p : V → ℝ) : ℝ :=
  ∑ v, p v * (-Real.log (p v))

/-- Кодирование данных по модели не короче энтропии
источника: dataCodeLen − sourceEntropy = KLdiv p q ≥ 0
(мост из kl_nonneg; p — распределение данных, q — модель).
Сжатие данных не может обойти источник — граница
Monotone-Compression-постановки на нашем языке. -/
theorem no_compression_below_entropy (p q : V → ℝ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hsump : ∑ v, p v = 1) (hsumq : ∑ v, q v = 1) :
    sourceEntropy p ≤ dataCodeLen p q := by
  have hkl : dataCodeLen p q - sourceEntropy p
      = Hagi.KLdiv p q := by
    unfold dataCodeLen sourceEntropy Hagi.KLdiv
    have hsplit : ∀ v ∈ (Finset.univ : Finset V),
        p v * (-Real.log (q v)) - p v * (-Real.log (p v))
          = p v * Real.log (p v / q v) := by
      intro v _
      have hpv : 0 < p v := hp v
      have hqv : 0 < q v := hq v
      field_simp
      rw [Real.log_div (by positivity) (by positivity)]
      ring
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => hsplit v
      (Finset.mem_univ v)
  have hnn : 0 ≤ Hagi.KLdiv p q :=
    Hagi.kl_nonneg p q hp hq hsump hsumq
  linarith

end Hagi.MDLThreeCurrency
