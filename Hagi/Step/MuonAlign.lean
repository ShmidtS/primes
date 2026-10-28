import Mathlib

/-!
# Muon: оптимальность выравнивания (источник №12)

Источник №12: "Muon Optimizes Under Spectral Norm
Constraints" (arXiv 2506.15054): Muon-шаг — ортогональная
полярная часть градиента — steepest descent при спектральной
норме: максимум выравнивания с градиентом среди ортогональных
обновлений.

Ядро в собственном базисе градиента: для G = diag(σ), σ ≥ 0,
Muon-шаг I даёт выравнивание Σσᵢ, не превзойдённое ни одной
унитарной матрицей: Σᵢ σᵢ·Re Qᵢᵢ ≤ Σᵢ σᵢ (|Qᵢᵢ| ≤ 1 из
унитарности — ядро неравенства фон Неймана о следе).
-/

namespace Hagi.Step.MuonAlign

open Matrix

/-- |Q_ii| ≤ 1 для унитарной Q (QᴴQ = 1): столбец нормы 1. -/
theorem unitary_diag_abs_le {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) (i : n) :
    ‖Q i i‖ ≤ 1 := by
  have hexp : (Qᴴ * Q) i i = ∑ j, star (Q j i) * Q j i := by
    simp [Matrix.mul_apply]
  have hdiag : ∑ j, star (Q j i) * Q j i = 1 := by
    have h3 : (Qᴴ * Q) i i = ∑ j, star (Q j i) * Q j i := hexp
    have h4 : (Qᴴ * Q) i i = 1 := by
      have hd := congrFun (congrArg Matrix.diag hQ) i
      simpa [Matrix.diag_apply] using hd
    rw [h3] at h4
    exact h4
  have hpos : ∑ j, ‖Q j i‖ ^ 2 = 1 := by
    have hterm : ∀ j : n, ‖Q j i‖ ^ 2 = (star (Q j i) * Q j i).re :=
      fun j => by
        have h2 : (star (Q j i) * Q j i).re
            = (Q j i).re * (Q j i).re + (Q j i).im * (Q j i).im := by
          simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        rw [h2]
        have hn := Complex.normSq_eq_norm_sq (Q j i)
        rw [← hn, Complex.normSq_apply]
    have hre : ∑ j, (star (Q j i) * Q j i).re
        = (∑ j, star (Q j i) * Q j i).re := by simp
    calc ∑ j, ‖Q j i‖ ^ 2 = ∑ j, (star (Q j i) * Q j i).re :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = (∑ j, star (Q j i) * Q j i).re := hre
      _ = (1 : ℂ).re := by rw [hdiag]
      _ = 1 := by norm_num
  have hkey : ‖Q i i‖ ^ 2 ≤ 1 := by
    have hmem : ‖Q i i‖ ^ 2 ≤ ∑ j, ‖Q j i‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (‖Q j i‖)) (Finset.mem_univ i)
    rw [hpos] at hmem
    exact hmem
  have hnn : 0 ≤ ‖Q i i‖ := norm_nonneg _
  nlinarith [hkey, hnn]

/-- MUON-ОПТИМАЛЬНОСТЬ (диагональное ядро): для
диагонализованного градиента diag(σ), σ ≥ 0, Muon-шаг
(ортогональная полярная часть = I) достигает выравнивания
Σσᵢ, максимального среди унитарных Q: Σᵢ σᵢ·Re Qᵢᵢ ≤ Σᵢ σᵢ —
stepest descent при спектральной норме (ядро источника). -/
theorem muon_alignment_optimal {n : Type*} [Fintype n] [DecidableEq n]
    (sig : n → ℝ) (hsig : ∀ i, 0 ≤ sig i)
    (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) :
    (∑ i, sig i * (Q i i).re) ≤ ∑ i, sig i := by
  have hmain : ∀ i : n, sig i * (Q i i).re ≤ sig i := by
    intro i
    have habs := unitary_diag_abs_le Q hQ i
    have hre' : (Q i i).re ≤ 1 := by
      calc (Q i i).re ≤ |(Q i i).re| := le_abs_self _
        _ ≤ ‖Q i i‖ := by simp [Complex.abs_re_le_norm]
        _ ≤ 1 := habs
    simpa using mul_le_mul_of_nonneg_left hre' (hsig i)
  exact Finset.sum_le_sum fun i _ => hmain i

end Hagi.Step.MuonAlign
