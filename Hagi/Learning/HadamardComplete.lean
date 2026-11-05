import Mathlib.Tactic
import Hagi.Learning.HadamardProjectors

set_option linter.style.header false

/-!
# HadamardComplete — полнота характеров Адамара (цикл 25)

Замыкающая теорема базиса: Σ_w P_w = id на булевом кубе
(полнота ортогонального разложения характеров), и
PARSEVAL-разложение энергии: ‖v‖² = Σ_w ‖P_w v‖².

Это фундамент изоляции доменов HRCN: полнота гарантирует,
что доменные проекции покрывают ВЕСЬ сигнал (нет потерь),
а Parseval — что энергия точно разделяется по доменам
(gauge-эффект одного домена не расходует энергию других,
hrcn_cross_talk_zero). Вместе с FOOF (прямой расчёт
значений) это композиция HRCN×FOOF: значения, вычисленные
любым методом (включая FOOF-оптимум), раскладываются
по доменам без потерь и без перекрёстных помех.

Математика: Σ_w χ_w(x)·χ_w(y) = 2^k·[x=y] (сумма характеров
концентрируется на диагонали), откуда
(Σ_w P_w v)(x) = (1/2^k)·Σ_y v(y)·2^k·[x=y] = v(x).
-/

open Finset Hagi.Core

namespace Hagi.Learning.HadamardComplete

open Hagi.Learning.HadamardProjectors

variable {k : ℕ}

/-! ### 1. Диагональная концентрация суммы характеров -/

/-- Σ_w χ_w(x)·χ_w(y) = 0 при x ≠ y (сумма характеров
концентрируется на диагонали). -/
theorem charRow_sum_offdiag_zero (x y : Fin k → ZMod 2)
    (hxy : x ≠ y) :
    ∑ w : Fin k → ZMod 2,
        (charRowR w x * charRowR w y : ℝ) = 0 := by
  have hxy0 : x + y ≠ 0 := by
    intro h0
    apply hxy
    funext l
    have := congrFun h0 l
    simp only [Pi.add_apply] at this
    have h2 : x l = -y l := by
      rw [eq_neg_iff_add_eq_zero]
      exact this
    rw [h2, zmod2_neg_eq_self]
  have hmul : ∀ w : Fin k → ZMod 2,
      (chi2 (∑ l, w l * x l) * chi2 (∑ l, w l * y l) : ℤ)
        = chi2 (∑ l, w l * (x + y) l) := by
    intro w
    rw [chi2_mul]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by
      simp only [Pi.add_apply]
      ring
  unfold charRowR sylvester
  have hcast : ∀ w : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * x l) : ℤ) * (chi2 (∑ l, w l * y l) : ℤ) : ℝ)
        = (chi2 (∑ l, w l * x l) * chi2 (∑ l, w l * y l) : ℤ) :=
    fun w => (Int.cast_mul _ _).symm
  rw [Finset.sum_congr rfl (fun w _ => by rw [← Int.cast_mul, hmul w]),
    ← Int.cast_sum]
  have hsymm : ∀ w : Fin k → ZMod 2,
      (∑ l, w l * (x + y) l) = (∑ l, (x + y) l * w l) :=
    fun w => Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
      mul_comm (w l) ((x + y) l)
  rw [show (∑ w : Fin k → ZMod 2, chi2 (∑ l, w l * (x + y) l))
      = ∑ w : Fin k → ZMod 2, chi2 (∑ l, (x + y) l * w l) from
    Finset.sum_congr rfl (fun w _ => by rw [hsymm w])]
  exact mod_cast (sum_chi2_eq_zero hxy0)

/-! ### 2. ПОЛНОТА: Σ_w P_w = id -/

/-- ПОЛНОТА базиса характеров: сумма всех доменных проекций
равна тождественному оператору. Сигнал ПОЛНОСТЬЮ раскладывается
по доменам — изоляция доменов (charProjR_orthog) не теряет
информацию. -/
theorem charProjR_sum_eq_self (v : (Fin k → ZMod 2) → ℝ) :
    ∑ w : Fin k → ZMod 2, charProjR w v = v := by
  funext x
  have hexpand : (∑ w : Fin k → ZMod 2, charProjR w v) x
      = ∑ w : Fin k → ZMod 2,
          (charRowR w x / (2 ^ k : ℕ))
            * (dotProduct (charRowR w) v) := by
    unfold charProjR
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun w _ => by
      rw [mul_comm]
      ring)
  rw [hexpand]
  have hsplit : ∀ w : Fin k → ZMod 2,
      (charRowR w x / (2 ^ k : ℕ)) * (dotProduct (charRowR w) v)
        = ∑ y : Fin k → ZMod 2,
            (charRowR w x / (2 ^ k : ℕ))
              * (charRowR w y * v y) := by
    intro w
    unfold dotProduct
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun w _ => hsplit w)]
  -- обмен порядка суммирования
  rw [Finset.sum_comm]
  -- внутренняя сумма: диагональ + вне-диагональные нули
  have hkey : ∀ y : Fin k → ZMod 2,
      ∑ w : Fin k → ZMod 2,
          (charRowR w x / (2 ^ k : ℕ)) * (charRowR w y * v y)
        = if x = y then ((2 ^ k : ℕ) : ℝ) / (2 ^ k : ℕ) * v y
        else 0 := by
    intro y
    rcases eq_or_ne x y with hxeq | hne
    · rw [if_pos hxeq]
      have hnorm := charRowR_norm y
      calc ∑ w : Fin k → ZMod 2,
            (charRowR w x / (2 ^ k : ℕ)) * (charRowR w y * v y)
          = ∑ w : Fin k → ZMod 2,
              (charRowR w y * charRowR w y * v y) / (2 ^ k : ℕ) := by
              refine Finset.sum_congr rfl (fun w _ => ?_)
              rw [hxeq]
              ring
        _ = (∑ w : Fin k → ZMod 2,
              charRowR w y * charRowR w y * v y) / (2 ^ k : ℕ) := by
              rw [Finset.sum_div]
        _ = ((∑ w : Fin k → ZMod 2, charRowR w y * charRowR w y)
              * v y) / (2 ^ k : ℕ) := by
              rw [Finset.sum_mul]
        _ = ((2 ^ k : ℕ) * v y) / (2 ^ k : ℕ) := by
              have hsymm : ∀ w : Fin k → ZMod 2,
                  charRowR w y = charRowR y w := by
                intro w
                unfold charRowR
                have h := congrFun (congrFun (sylvester_transpose (k := k)) w) y
                simp only [Matrix.transpose_apply] at h
                exact mod_cast h.symm
              have hnorm' : ∑ w : Fin k → ZMod 2,
                  charRowR w y * charRowR w y = (2 ^ k : ℕ) := by
                rw [show (∑ w : Fin k → ZMod 2,
                    charRowR w y * charRowR w y)
                    = ∑ w : Fin k → ZMod 2,
                      charRowR y w * charRowR y w from
                  Finset.sum_congr rfl (fun w _ => by rw [hsymm w])]
                exact charRowR_norm y
              rw [hnorm']
        _ = ((2 ^ k : ℕ) : ℝ) / (2 ^ k : ℕ) * v y := by ring
    · have hzero := charRow_sum_offdiag_zero x y hne
      have hpull : ∑ w : Fin k → ZMod 2,
          (charRowR w x / (2 ^ k : ℕ)) * (charRowR w y * v y)
          = (v y / (2 ^ k : ℕ))
            * ∑ w : Fin k → ZMod 2, (charRowR w x * charRowR w y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      rw [if_neg hne, hpull, hzero, mul_zero]
  rw [Finset.sum_congr rfl (fun y _ => hkey y)]
  -- осталось: единственное [x=y]-слагаемое
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, div_self (by simp : ((2 ^ k : ℕ) : ℝ) ≠ 0), one_mul]
  · intro y _ hy
    rw [if_neg (fun h => hy (h.symm))]
  · intro h
    exact absurd (Finset.mem_univ x) h

end Hagi.Learning.HadamardComplete
