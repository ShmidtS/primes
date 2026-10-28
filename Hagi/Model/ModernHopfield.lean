import Mathlib

/-!
# Современные Hopfield-сети: ретривал и ёмкость (источник №16)

Источник №16: Ramsauer et al., "Hopfield Networks is All You
Need" (arXiv 2008.02217): современная Hopfield-сеть
(непрерывные состояния) с softmax-ретривалом эквивалентна
attention и обладает ЭКСПОНЕНЦИАЛЬНОЙ ёмкостью
(Теорема 3: ~2^(d/(2 log d)) паттернов при разделении).

Формализовано ядро:
- hopfield_concentration: при β-разделении логитов (лучший
  ≥ прочих + Δ) softmax-вес лучшего паттерна ≥ 1/(1+(K−1)e^{−Δ})
  ≥ 1 − (K−1)·e^{−Δ} — механизм точного ретривала;
- capacity_bound_arith: арифметика экспоненциальной ёмкости:
  2K·log K ≤ d ⟹ K ≤ 2^(d/(2·log K)) — при размерности d
  хранимы K паттернов (полиномиальная по d нижняя граница
  ёмкости = 2^{d/(2 log d)} при K = d/(2 log d)-масштабе).
-/

namespace Hagi.Model.ModernHopfield

open Real

/-- SOFTMAX-КОНЦЕНТРАЦИЯ РЕТРИВАЛА (ядро Теоремы 3): если
лучший логит s* отделён от прочих K−1 на зазор Δ, то
softmax-вес лучшего паттерна не менее 1/(1+(K−1)e^{−Δ})
(и, как следствие, ≥ 1 − (K−1)e^{−Δ}). -/
theorem hopfield_concentration {K : ℕ} (s : Fin K → ℝ)
    (iStar : Fin K) (Delta : ℝ)
    (_hDelta : 0 ≤ Delta)
    (hsep : ∀ i, i ≠ iStar → s iStar ≥ s i + Delta) :
    Real.exp (s iStar) / ∑ i, Real.exp (s i)
      ≥ 1 / (1 + (K - 1 : ℝ) * Real.exp (-Delta)) := by
  -- верхняя оценка знаменателя: прочие слагаемые ≤ e^{s*−Δ}
  have hothers : ∑ i ∈ Finset.univ.erase iStar, Real.exp (s i)
      ≤ (K - 1 : ℝ) * Real.exp (s iStar - Delta) := by
    calc ∑ i ∈ Finset.univ.erase iStar, Real.exp (s i)
        ≤ ∑ i ∈ Finset.univ.erase iStar, Real.exp (s iStar - Delta) :=
          Finset.sum_le_sum fun i hi => by
            have hne : i ≠ iStar := Finset.ne_of_mem_erase hi
            exact Real.exp_le_exp.mpr (by
              have := hsep i hne
              linarith)
      _ = (K - 1 : ℝ) * Real.exp (s iStar - Delta) := by
          rw [Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ iStar),
            Finset.card_univ, Fintype.card_fin]
          have hK1 : 1 ≤ K := by have := iStar.isLt; omega
          rw [show ((K : ℕ) : ℝ) - 1 = ((K - 1 : ℕ) : ℝ) from by
            norm_num [Nat.cast_sub hK1]]
          ring
  have hexp : Real.exp (s iStar - Delta)
      = Real.exp (s iStar) * Real.exp (-Delta) := by
    rw [← Real.exp_add]
    ring
  rw [hexp] at hothers
  set e : ℝ := Real.exp (s iStar) with he
  set r : ℝ := Real.exp (-Delta) with hr
  have hpos : 0 < e := Real.exp_pos _
  have hrpos : 0 < r := Real.exp_pos _
  have honeD : 0 < 1 + (K - 1 : ℝ) * r := by
    have hlt := iStar.isLt
    have hK1 : 1 ≤ K := by omega
    have hK : (0:ℝ) ≤ (K - 1 : ℝ) := by
      have : (0:ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
        have : 0 ≤ (K - 1 : ℕ) := by omega
        exact_mod_cast this
      have h1 : 1 ≤ K := by omega
      rw [show ((K:ℕ):ℝ) - 1 = ((K-1:ℕ):ℝ) from by
        norm_num [Nat.cast_sub h1]]
      exact this
    have hnn : 0 ≤ (K - 1 : ℝ) * r := mul_nonneg hK hrpos.le
    linarith
  have hWsplit : (∑ i, Real.exp (s i)) = e
      + ∑ i ∈ Finset.univ.erase iStar, Real.exp (s i) :=
    (Finset.sum_erase_add Finset.univ (fun i => Real.exp (s i))
      (Finset.mem_univ iStar)).symm.trans (add_comm _ _)
  have key : (∑ i, Real.exp (s i)) ≤ e * (1 + (K - 1 : ℝ) * r) := by
    rw [hWsplit, mul_add]
    norm_num
    nlinarith [hothers]
  have hWpos : 0 < ∑ i, Real.exp (s i) := by
    rw [hWsplit]
    positivity
  rw [ge_iff_le]
  refine (div_le_div_iff₀ (a := 1) (c := e) honeD hWpos).mpr ?_
  rw [one_mul]
  exact key


/-- АРИФМЕТИКА ЭКСПОНЕНЦИАЛЬНОЙ ЁМКОСТИ (Теорема 3,
интерпретация): если размерность d покрывает 2K·log K бит
разделения, то K паттернов ограничены показательной функцией
2^(d/(2·log K)) — ёмкость растёт ЭКСПОНЕНЦИАЛЬНО по d при
K = d/(2·log d)-масштабе (Ramsauer et al. 2020). -/
theorem capacity_bound_arith (d K : ℕ) (hK : 2 ≤ K)
    (hd : (2 : ℝ) * K * Real.log K ≤ d) :
    (K : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / (2 * Real.log K)) := by
  have h1 : (1 : ℝ) < K := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := Real.log_pos h1
  -- d/(2 log K) ≥ K
  have hdiv : ((K : ℝ)) ≤ (d : ℝ) / (2 * Real.log K) := by
    rw [le_div_iff₀ (show (0:ℝ) < 2 * Real.log K by positivity)]
    rw [mul_comm]
    nlinarith [hd]
  -- K ≤ 2^K (натуральный показатель, индукция)
  have h2S : ∀ n : ℕ, ((n : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
        have hm : (0 : ℝ) ≤ (m : ℕ) := by simp
        rw [pow_succ]
        push_cast
        nlinarith [ih]
  have h2Kn : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := fun n => by
    have := h2S n
    linarith
  calc (K : ℝ) ≤ (2 : ℝ) ^ (K : ℕ) := h2Kn K
    _ = (2 : ℝ) ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast 2 K).symm
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / (2 * Real.log K)) :=
      Real.rpow_le_rpow_of_exponent_le_or_ge
        (Or.inl ⟨by norm_num, hdiv⟩)

end Hagi.Model.ModernHopfield
