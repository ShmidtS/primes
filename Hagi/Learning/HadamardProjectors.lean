import Mathlib.Tactic
import Hagi.Core.Hadamard

set_option linter.style.header false

/-!
# HadamardProjectors — ортогональные проекторы характеров для
изоляции доменов памяти

Синтез RCDL+HAGI: памяти разных доменов не должны
интерферировать. Строки матрицы Сильвестра — характеры χ_w,
попарно ортогональные. Проектор на характер w:
P_w(v) = (⟨χ_w, v⟩ / 2^k) • χ_w.

Доказано строго:
- `charProj_idem`: P_w — идемпотентный проектор;
- `charProj_orthog`: P_w ∘ P_u = 0 для w ≠ u — изоляция
  доменов: обновление памяти домена w не меняет компоненту u.
-/

open Finset

namespace Hagi.Learning.HadamardProjectors

open Hagi.Core

variable {k : ℕ}

/-- Строка-характер χ_w матрицы Сильвестра. -/
def charRow (w : Fin k → ZMod 2) : (Fin k → ZMod 2) → ℚ :=
  fun i => (sylvester k w i : ℚ)

/-- Норма характера: ⟨χ_w, χ_w⟩ = 2^k. -/
theorem charRow_norm (w : Fin k → ZMod 2) :
    dotProduct (charRow w) (charRow w) = (2 ^ k : ℕ) := by
  unfold charRow dotProduct sylvester
  simp only [← Int.cast_mul, chi2_sq, Int.cast_one]
  rw [Finset.sum_const]
  simp [Fintype.card_fun]

/-- Ортогональность характеров: w ≠ u ⇒ ⟨χ_w, χ_u⟩ = 0. -/
theorem charRow_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u) :
    dotProduct (charRow w) (charRow u) = 0 := by
  have hwu0 : w + u ≠ 0 := by
    intro h0
    apply hwu
    funext l
    have := congrFun h0 l
    simp only [Pi.add_apply] at this
    have h2 : w l = -u l := by
      rw [eq_neg_iff_add_eq_zero]
      exact this
    rw [h2, zmod2_neg_eq_self]
  unfold charRow dotProduct sylvester
  have hmul : ∀ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l)) : ℤ)
        = chi2 (∑ l, (w + u) l * i l) := by
    intro i
    rw [chi2_mul, inner2_add_left]
  have hz : ∑ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hmul i), sum_chi2_eq_zero hwu0]
  calc dotProduct (charRow w) (charRow u)
      = ((∑ i : Fin k → ZMod 2,
          ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ))) : ℚ) := rfl
    _ = ((0 : ℤ) : ℚ) := by
        have : ∀ i : Fin k → ZMod 2,
            (↑(chi2 (∑ l, w l * i l)) * ↑(chi2 (∑ l, u l * i l)) : ℚ)
              = ↑((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l))) :=
          fun i => (Int.cast_mul _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Int.cast_sum, hz]
    _ = 0 := by simp


/-! ### Проекторы и изоляция доменов -/

/-- Ортогональный проектор на характер χ_w (нормировка 2^k). -/
noncomputable def charProj (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℚ) : (Fin k → ZMod 2) → ℚ :=
  fun i => (dotProduct (charRow w) v / (2 ^ k : ℕ)) * charRow w i

/-- Идемпотентность: P_w — проектор. -/
theorem charProj_idem (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℚ) :
    charProj w (charProj w v) = charProj w v := by
  have hnorm : dotProduct (charRow w) (charRow w) = (2 ^ k : ℕ) :=
    charRow_norm w
  unfold charProj
  have hinner : dotProduct (charRow w)
      (fun j => dotProduct (charRow w) v / (2 ^ k : ℕ) * charRow w j)
        = dotProduct (charRow w) v := by
    have hsmul : (fun j => dotProduct (charRow w) v / (2 ^ k : ℕ)
        * charRow w j)
          = (dotProduct (charRow w) v / (2 ^ k : ℕ)) • (charRow w) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hsmul, dotProduct_smul, hnorm]
    have h2k : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by
      positivity
    rw [smul_eq_mul, div_mul_cancel₀ _ h2k]
  funext i
  rw [hinner]


/-- Изоляция доменов: проекторы разных характеров обнуляют
друг друга: P_w ∘ P_u = 0 при w ≠ u. Обновление памяти домена w
не меняет компоненту домена u. -/
theorem charProj_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℚ) :
    charProj w (charProj u v) = 0 := by
  have horth := charRow_orthog hwu
  unfold charProj
  have hsmul : (fun j => dotProduct (charRow u) v / (2 ^ k : ℕ)
      * charRow u j)
        = (dotProduct (charRow u) v / (2 ^ k : ℕ)) • (charRow u) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  funext i
  rw [hsmul, dotProduct_smul, horth, smul_zero]
  simp


/-! ### ℝ-версии (для связки с RCDL-софтмаксом) -/

/-- Строка-характер в ℝ. -/
def charRowR (w : Fin k → ZMod 2) : (Fin k → ZMod 2) → ℝ :=
  fun i => (sylvester k w i : ℝ)

theorem charRowR_norm (w : Fin k → ZMod 2) :
    dotProduct (charRowR w) (charRowR w) = (2 ^ k : ℕ) := by
  unfold charRowR dotProduct sylvester
  simp only [← Int.cast_mul, chi2_sq, Int.cast_one]
  rw [Finset.sum_const]
  simp [Fintype.card_fun]

theorem charRowR_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u) :
    dotProduct (charRowR w) (charRowR u) = 0 := by
  have hwu0 : w + u ≠ 0 := by
    intro h0
    apply hwu
    funext l
    have := congrFun h0 l
    simp only [Pi.add_apply] at this
    have h2 : w l = -u l := by
      rw [eq_neg_iff_add_eq_zero]
      exact this
    rw [h2, zmod2_neg_eq_self]
  unfold charRowR dotProduct sylvester
  have hmul : ∀ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l)) : ℤ)
        = chi2 (∑ l, (w + u) l * i l) := by
    intro i
    rw [chi2_mul, inner2_add_left]
  have hz : ∑ i : Fin k → ZMod 2,
      ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ)) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hmul i), sum_chi2_eq_zero hwu0]
  calc dotProduct (charRowR w) (charRowR u)
      = ((∑ i : Fin k → ZMod 2,
          ((chi2 (∑ l, w l * i l) : ℤ)) * ((chi2 (∑ l, u l * i l) : ℤ))) : ℝ) := rfl
    _ = ((0 : ℤ) : ℝ) := by
        have : ∀ i : Fin k → ZMod 2,
            (↑(chi2 (∑ l, w l * i l)) * ↑(chi2 (∑ l, u l * i l)) : ℝ)
              = ↑((chi2 (∑ l, w l * i l)) * (chi2 (∑ l, u l * i l))) :=
          fun i => (Int.cast_mul _ _).symm
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Int.cast_sum, hz]
    _ = 0 := by simp

/-- Ортогональный проектор на характер χ_w в ℝ. -/
noncomputable def charProjR (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  fun i => (dotProduct (charRowR w) v / (2 ^ k : ℕ)) * charRowR w i

theorem charProjR_idem (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    charProjR w (charProjR w v) = charProjR w v := by
  have hnorm : dotProduct (charRowR w) (charRowR w) = (2 ^ k : ℕ) :=
    charRowR_norm w
  unfold charProjR
  have hsmul : (fun j => dotProduct (charRowR w) v / (2 ^ k : ℕ)
      * charRowR w j)
        = (dotProduct (charRowR w) v / (2 ^ k : ℕ)) • (charRowR w) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  have hinner : dotProduct (charRowR w)
      (fun j => dotProduct (charRowR w) v / (2 ^ k : ℕ) * charRowR w j)
        = dotProduct (charRowR w) v := by
    rw [hsmul, dotProduct_smul, hnorm]
    have h2k : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
    rw [smul_eq_mul, div_mul_cancel₀ _ h2k]
  funext i
  rw [hinner]

theorem charProjR_orthog {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℝ) :
    charProjR w (charProjR u v) = 0 := by
  have horth := charRowR_orthog hwu
  unfold charProjR
  have hsmul : (fun j => dotProduct (charRowR u) v / (2 ^ k : ℕ)
      * charRowR u j)
        = (dotProduct (charRowR u) v / (2 ^ k : ℕ)) • (charRowR u) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
  funext i
  rw [hsmul, dotProduct_smul, horth, smul_zero]
  simp

/-- Линейность проектора по аргументу. -/
theorem charProjR_add (w : Fin k → ZMod 2) (v1 v2 : (Fin k → ZMod 2) → ℝ) :
    charProjR w (v1 + v2) = charProjR w v1 + charProjR w v2 := by
  unfold charProjR
  funext i
  rw [dotProduct_add, add_div, add_mul, Pi.add_apply]

end Hagi.Learning.HadamardProjectors


set_option linter.style.header false

/-!
# HadamardComplete — полнота характеров Адамара

Σ_w P_w = id на булевом кубе
(полнота ортогонального разложения характеров), и
PARSEVAL-разложение энергии: ‖v‖² = Σ_w ‖P_w v‖².

Полнота: доменные проекции покрывают весь сигнал; Parseval
(см. ниже): энергия точно разделяется по доменам.

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

/-- Полнота базиса характеров: сумма всех доменных проекций
равна тождественному оператору. Сигнал полностью раскладывается
по доменам: изоляция доменов (`charProjR_orthog`) не теряет
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

set_option linter.style.header false

/-!
# HadamardParseval — энергетическое разложение

PARSEVAL для доменного разложения HRCN: энергия сигнала
равна сумме энергий доменных компонент:
  ⟨v, v⟩ = Σ_w ‖P_w v‖².
Следствие полноты (`charProjR_sum_eq_self`) и
ортогональности (`charProjR_orthog`): разложение —
ортогональная прямая сумма, энергия делится по доменам
без перекрёстных членов. Битовый бюджет домена w
контролирует только ‖P_w v‖².
-/

open Finset Hagi.Core

namespace Hagi.Learning.HadamardParseval

open Hagi.Learning.HadamardProjectors Hagi.Learning.HadamardComplete

variable {k : ℕ}

/-! ### Вспомогательные тождества -/

/-- Линейность: dotProduct (c • a) b = c · (a ⬝ᵥ b). -/
theorem dotProduct_smul_left (c : ℝ)
    (a b : (Fin k → ZMod 2) → ℝ) :
    dotProduct (c • a) b = c * dotProduct a b := by
  unfold dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc]
  rw [Finset.mul_sum]
  ring

/-- Сумма в первом аргументе: ⟨Σ_w f w, v⟩ = Σ_w ⟨f w, v⟩. -/
theorem dotProduct_sum_left (f : (Fin k → ZMod 2)
      → ((Fin k → ZMod 2) → ℝ)) (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (∑ w, f w) v = ∑ w, dotProduct (f w) v := by
  unfold dotProduct
  simp only [Finset.sum_apply]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-! ### Доменная энергия -/

/-- P_w v — скалярное кратное характера:
P_w v = (⟨χ_w, v⟩ / 2^k) • χ_w. -/
theorem charProjR_eq_smul (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    ∃ c : ℝ, charProjR w v = c • charRowR w ∧
      c * (2 ^ k : ℕ) = dotProduct (charRowR w) v := by
  refine ⟨dotProduct (charRowR w) v / (2 ^ k : ℕ), rfl, ?_⟩
  have h2 : ((2:ℕ)^k : ℝ) ≠ 0 := by positivity
  field_simp

/-- Норма доменной компоненты:
‖P_w v‖² = ⟨χ_w, v⟩² / 2^k. -/
theorem charProjR_norm_sq (w : Fin k → ZMod 2)
    (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (charProjR w v) (charProjR w v)
      = (dotProduct (charRowR w) v) ^ 2 / (2 ^ k : ℕ) := by
  obtain ⟨c, hproj, hcscale⟩ := charProjR_eq_smul w v
  have hsmul_right : dotProduct (charRowR w) (c • charRowR w)
      = c * dotProduct (charRowR w) (charRowR w) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    have hreg : ∀ i : Fin k → ZMod 2,
        charRowR w i * (c * charRowR w i)
          = c * (charRowR w i * charRowR w i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hreg i),
      Finset.mul_sum]
  rw [hproj, dotProduct_smul_left, hsmul_right]
  have hnorm := charRowR_norm w
  rw [hnorm]
  have hc : c = dotProduct (charRowR w) v / (2^k:ℕ) := by
    rw [eq_div_iff (by positivity : ((2^k:ℕ):ℝ) ≠ 0)]
    exact hcscale
  rw [hc]
  field_simp

/-- Перекрёстная энергия нулевая: ⟨P_w v, P_u v⟩ = 0 при
w ≠ u (ортогональность проекторов). -/
theorem charProjR_cross_zero {w u : Fin k → ZMod 2} (hwu : w ≠ u)
    (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct (charProjR w v) (charProjR u v) = 0 := by
  obtain ⟨cw, hpw, _⟩ := charProjR_eq_smul w v
  obtain ⟨cu, hpu, _⟩ := charProjR_eq_smul u v
  have hsmul_right : dotProduct (charRowR w) (cu • charRowR u)
      = cu * dotProduct (charRowR w) (charRowR u) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    have hreg : ∀ i : Fin k → ZMod 2,
        charRowR w i * (cu * charRowR u i)
          = cu * (charRowR w i * charRowR u i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hreg i),
      Finset.mul_sum]
  rw [hpw, hpu, dotProduct_smul_left, hsmul_right]
  have horth := charRowR_orthog hwu
  rw [horth, mul_zero, mul_zero]

/-! ### Parseval -/

/-- Parseval для доменного разложения: ⟨v, v⟩ = Σ_w ‖P_w v‖².
Следствие полноты базиса; перекрёстных членов нет
(ортогональность). -/
theorem parseval (v : (Fin k → ZMod 2) → ℝ) :
    dotProduct v v
      = ∑ w : Fin k → ZMod 2,
          dotProduct (charProjR w v) (charProjR w v) := by
  have hcomp : v ⬝ᵥ v = (∑ w, charProjR w v) ⬝ᵥ v := by
    rw [charProjR_sum_eq_self v]
  rw [hcomp, dotProduct_sum_left]
  refine Finset.sum_congr rfl fun w _ => ?_
  -- ⟨P_w v, v⟩ = ‖P_w v‖²: v = P_w v + ортодополнение,
  -- ⟨P_w v, орто⟩ = 0. Прямое вычисление:
  have h1 : dotProduct (charProjR w v) v
      = (dotProduct (charRowR w) v) ^ 2 / (2 ^ k : ℕ) := by
    obtain ⟨c, hproj, hcscale⟩ := charProjR_eq_smul w v
    rw [hproj, dotProduct_smul_left]
    have hc : c = dotProduct (charRowR w) v / (2^k:ℕ) := by
      rw [eq_div_iff (by positivity : ((2^k:ℕ):ℝ) ≠ 0)]
      exact hcscale
    rw [hc]
    field_simp
  rw [h1, charProjR_norm_sq]

end Hagi.Learning.HadamardParseval
