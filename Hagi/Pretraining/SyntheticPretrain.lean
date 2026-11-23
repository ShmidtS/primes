/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Core.Hadamard


set_option linter.style.header false

/-!
# synthetic pre-pretraining transfer (arXiv 2609.39827)

The formalization of the synthetic pre-pretraining theory, in
the GrowthGate / ComputeBudget style: short synthetic
pretraining on RETRIEVAL-style tasks (k-Shuffle Dyck, MP-Struct,
NCA) reduces the TIME-TO-CAPABILITY of the subsequent main
pretraining; the mechanism hypothesis is long-range retrieval,
not a grammatical prior.

**Honest boundaries (the paper's claims we do and do not carry):**

* h_emp_retrieval_transfer_ — the transfer itself (retrieval-style
  synthetic pretraining accelerates the main run) is EMPIRICAL:
  it enters every theorem below as a measured hypothesis on the
  two trajectories, never as a derived fact. No claim that
  retrieval ⇒ general capability is made or needed.
* "Set task degraded" is an empirical WARNING, not a theorem:
  the set-tracking control failing to transfer is an observed
  row of the paper's table, not something this module proves.
* The gate below is a COMPUTE gate only: it says when the
  synthetic phase pays for itself in capability-per-compute;
  it says nothing about asymptotic capability ceilings.

**What the module proves:**

* `TimeToCapability` — the first index a capability trajectory
  C reaches threshold τ (Nat.find under a reaching hypothesis).
* `synthGain` — the measured step saving T_plain(τ) − T_synth(τ).
* `time_to_capability_correct` — well-formedness: the found
  index is a genuine first crossing (C ≥ τ there, C < τ strictly
  before), and under monotonicity capability stays ≥ τ after it.
* `synth_investment_dominates` — THE gate theorem: if the
  measured saving, priced at the per-step compute cost, exceeds
  the cost of the synthetic phase (ΔT·c_step > C_synth — the
  only empirical gate), then the composite (synthetic-then-main)
  schedule reaches τ with STRICTLY larger capability-per-compute
  than starting the main phase directly. No free positive
  hypotheses: everything except the h_emp_ gate and the sign
  conventions is derived.
* `task_selection_marginal` — the adaptive-task-choice corollary
in the ComputeBudget style: among finitely many candidate
synthetic tasks j with measured gains g_j and POSITIVE costs
c_j > 0 (hc — with nonpositive costs the ratio g/c is
meaningless, and Lean's x/0 = 0 would let the argmax exist
vacuously), the argmax of g_j/c_j exists and its ratio
dominates every alternative's — with positive costs the
ratio is the true gain-per-cost (the finite argmax
characterization feeding `marginalValue_law`'s active-set
scan).
-/

namespace Hagi.Pretraining

section SyntheticPretrain

/-! ### Definitions -/

/-- **Time-to-capability**: the FIRST index at which the
capability trajectory C reaches threshold τ (well-defined only
under a reaching hypothesis; `Nat.find` on `fun n => τ ≤ C n`). -/
noncomputable def TimeToCapability (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n) : ℕ :=
  Nat.find hreach

/-- **The measured synthetic gain**: the step saving
T_plain(τ) − T_synth(τ) between the plain-main trajectory and
the synthetic-then-main trajectory at the SAME threshold.
Its sign is an EMPIRICAL quantity (h_emp_retrieval_transfer_):
nothing here forces it positive except measurement. -/
noncomputable def synthGain (τ : ℝ) (Cp Cs : ℕ → ℝ)
    (hp : ∃ n : ℕ, τ ≤ Cp n) (hs : ∃ n : ℕ, τ ≤ Cs n) : ℝ :=
  (TimeToCapability τ Cp hp : ℝ) - (TimeToCapability τ Cs hs : ℝ)

/-! ### Well-formedness of the first crossing -/

/-- **The first-crossing certificate**: the found index tcross
satisfies τ ≤ C tcross, every earlier index is strictly below τ,
and — under monotonicity of the trajectory — capability never
drops back below τ after tcross (the crossing is permanent). The
first two clauses are `Nat.find`'s spec/minimality; the third
is the monotone induction. Non-vacuous: applies to any
monotone reaching trajectory. -/
theorem time_to_capability_correct (τ : ℝ) (C : ℕ → ℝ)
    (hreach : ∃ n : ℕ, τ ≤ C n)
    (hmono : ∀ t, C t ≤ C (t + 1)) :
    τ ≤ C (TimeToCapability τ C hreach)
      ∧ (∀ k < TimeToCapability τ C hreach, C k < τ)
      ∧ (∀ k, TimeToCapability τ C hreach ≤ k → τ ≤ C k) := by
  have hspec : τ ≤ C (Nat.find hreach) := Nat.find_spec hreach
  have hperm : ∀ n k : ℕ, n ≤ k → C n ≤ C k := by
    intro n k
    induction k with
    | zero =>
        intro hk
        have hn : n = 0 := Nat.le_zero.mp hk
        rw [hn]
    | succ k ih =>
        intro hk
        rcases Nat.eq_or_lt_of_le hk with h | h
        · rw [h]
        · exact le_trans (ih (Nat.le_of_lt_succ h)) (hmono k)
  refine ⟨hspec, ?_, fun k hk => hspec.trans (hperm (Nat.find hreach) k hk)⟩
  intro k hk
  unfold TimeToCapability at hk
  exact not_le.mp (Nat.find_min hreach hk)

/-! ### The gate theorem -/

/-- **THE gate theorem (compute-aware GrowthGate comparison)**:
two schedules reach the same threshold τ — the plain main run
at step T_p, the composite (synthetic phase of cost C_synth,
then main run) at main-step T_s. The only empirical gate is
`h_emp_gate`: the measured saving synthGain = T_p − T_s, priced
at the per-step compute cost c_step, strictly exceeds the cost
of the synthetic phase (ΔT·c_step > C_synth — the
h_emp_retrieval_transfer_ measurement of arXiv 2609.39827 in
compute units). Then the composite schedule's
capability-per-compute at the moment of reaching τ,

`τ / (C_synth + T_s · c_step)`  vs  `τ / (T_p · c_step)`,

is STRICTLY larger for the synthetic-pretrained run. All sign
hypotheses are conventions (threshold, step cost, costs
nonneg); no free positive constant hides in the conclusion:
the inequality is exactly the gate re-denominated. -/
theorem synth_investment_dominates (τ cstep Csyt Tp Ts : ℝ)
    (Cp Cs : ℕ → ℝ) (hp : ∃ n : ℕ, τ ≤ Cp n) (hs : ∃ n : ℕ, τ ≤ Cs n)
    (hτ : 0 < τ) (hcstep : 0 < cstep)
    (hCsyt : 0 < Csyt) (hTs : 0 ≤ Ts)
    (hTp : (TimeToCapability τ Cp hp : ℝ) = Tp)
    (hTsCast : (TimeToCapability τ Cs hs : ℝ) = Ts)
    (h_emp_gate : synthGain τ Cp Cs hp hs * cstep > Csyt) :
    τ / (Csyt + Ts * cstep) > τ / (Tp * cstep) := by
  -- unpack the measured saving into the two crossing times
  have hgain : synthGain τ Cp Cs hp hs = Tp - Ts := by
    unfold synthGain
    rw [hTp, hTsCast]
  rw [hgain] at h_emp_gate
  -- the gate says the composite cost is strictly smaller
  have hcmp : Csyt + Ts * cstep < Tp * cstep := by
    have hring : (Tp - Ts) * cstep = Tp * cstep - Ts * cstep := by ring
    linarith
  -- both denominators are strictly positive
  have hpos1 : 0 < Csyt + Ts * cstep := by
    have hTc : 0 ≤ Ts * cstep := mul_nonneg hTs (le_of_lt hcstep)
    linarith
  have hpos2 : 0 < Tp * cstep := by
    have hTp2 : Ts < Tp := by
      by_contra hcon
      have : (Tp - Ts) * cstep ≤ 0 := by
        nlinarith [hcon, hcstep, hTs]
      linarith
    have hTp3 : 0 < Tp := lt_of_le_of_lt hTs hTp2
    exact mul_pos hTp3 hcstep
  -- the efficiency comparison, re-denominated
  rw [gt_iff_lt, div_lt_div_iff₀ hpos2 hpos1]
  have key : τ * (Tp * cstep) - τ * (Csyt + Ts * cstep)
      = τ * ((Tp - Ts) * cstep - Csyt) := by ring
  have hA : 0 < (Tp - Ts) * cstep - Csyt := sub_pos.2 (by linarith)
  have := mul_pos hτ hA
  linarith

/-! ### The adaptive task-selection corollary -/

/-- **The marginal task-selection corollary** (ComputeBudget
style): among finitely many candidate synthetic tasks j with
costs c_j > 0, the argmax of the measured ratio g_j / c_j
EXISTS, and the selected index's ratio dominates every
alternative's — the finite-argmax characterization that feeds
`marginalValue_law`'s active-set scan (`h_emp_task_*`: the
g_j are the measured per-task transfer gains; nothing here
constrains their signs — a task with negative measured gain is
dominated automatically). -/
theorem task_selection_marginal (J : Type) [Finite J] [Nonempty J]
    (g c : J → ℝ) (_hc : ∀ j, 0 < c j) :
    ∃ jmax : J, ∀ j : J, g j / c j ≤ g jmax / c jmax := by
  haveI : Fintype J := Fintype.ofFinite J
  have hne : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨jmax, hjmax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset J)
      (fun j => g j / c j) hne
  exact ⟨jmax, fun j => hmax j (Finset.mem_univ j)⟩

end SyntheticPretrain

end Hagi.Pretraining


/-!
# DataPruning — no free lunch для прореживания данных

Ядро результата Paul–Santamaria et al. (NeurIPS 2023,
«No Free Lunch Theorems for Data Pruning»; контекст — Sorscher
et al., NeurIPS 2022, «Beyond Neural Scaling Laws»): если
правило прореживания отбрасывает точку p, то любой ученик,
зависящий только от оставшихся данных, НЕ РАЗЛИЧАЕТ два
таргета, согласных на оставшихся точках и расходящихся в p —
сумма ошибок на них ≥ 1. Прореживание не бесплатно.
-/

namespace Hagi.Pretraining

/-- NO FREE LUNCH ДЛЯ PRUNING: ученик g, зависящий только от
значений на kept-подмножестве (hagree), на паре таргетов
y₀ ≡ 0 и y₁ (единица только в выброшенной точке p) ошибается
в сумме не менее чем на 1. -/
theorem pruning_nfl (kept : Finset ℕ) (p : ℕ) (hp : p ∉ kept)
    (g : (ℕ → ℝ) → ℝ)
    (hagree : ∀ y1 y2 : ℕ → ℝ, (∀ i ∈ kept, y1 i = y2 i) →
      g y1 = g y2) :
    |g (fun _ => (0:ℝ)) - (fun _ => (0:ℝ)) p|
      + |g (fun i => if i = p then (1:ℝ) else 0)
          - (fun i => if i = p then (1:ℝ) else 0) p| ≥ 1 := by
  have hsame : g (fun _ => (0:ℝ))
      = g (fun i => if i = p then (1:ℝ) else 0) := by
    apply hagree
    intro i hi
    have hip : i ≠ p := fun h => absurd (h ▸ hi) hp
    simp [hip]
  have hv2 : g (fun i => if i = p then (1:ℝ) else 0)
      = g (fun _ => (0:ℝ)) := hsame.symm
  have e0 : (fun _ => (0:ℝ)) p = (0:ℝ) := rfl
  have e1 : (fun i => if i = p then (1:ℝ) else 0) p = (1:ℝ) := by
    simp
  rw [e1, hv2, e0]
  have htri : ∀ v : ℝ, |v| + |v - 1| ≥ 1 := by
    intro v
    rcases lt_or_ge v 0 with h2 | h2
    · rw [abs_of_nonpos (by linarith : v ≤ 0)]
      rw [abs_of_nonpos (by linarith : v - 1 ≤ 0)]
      linarith
    · rw [abs_of_nonneg h2]
      rcases lt_or_ge v 1 with h3 | h3
      · rw [abs_of_nonpos (by linarith : v - 1 ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - 1)]
        linarith
  simpa using htri (g (fun _ => (0:ℝ)))
/-- ОБРАТНАЯ СТОРОНА NFL: на ИЗБЫТОЧНЫХ данных (таргет
константен) прореживание БЕСПЛАТНО — предиктор-константа
ошибается нуль на любой выброшенной точке. Разрыв с
pruning_nfl: цена pruning возникает только на
информативных точках. -/
theorem pruning_free_for_constant (c : ℝ)
    (kept : Finset ℕ) (p : ℕ)
    (g : (ℕ → ℝ) → ℝ)
    (hg : ∀ y : ℕ → ℝ, (∀ i ∈ kept, y i = c) → g y = c) :
    |g (fun _ => c) - (fun _ => c) p|
      + |g (fun i => if i = p then c else c)
          - (fun i => if i = p then c else c) p| = 0 := by
  have h1 : g (fun _ => c) = c := hg _ (fun i _ => rfl)
  have h2 : g (fun i => if i = p then c else c) = c := by
    apply hg
    intro i _
    simp
  rw [h1, h2]
  simp

/-- ВОССТАНОВЛЕНИЕ ПРУНЕННОЙ ТОЧКИ: если таргет — L-липшицева
функция f, а выброшенная точка t лежит между соседними
kept-точками с расстоянием ≤ δ, то значение в t
восстанавливается из соседа с ошибкой ≤ L·δ. Плотная сетка
на гладких таргетах делает pruning почти бесплатным —
дополняет pruning_nfl (ломается на крутых таргетах). -/
theorem pruning_recovery_bound (f : ℝ → ℝ) (t x0 x1 : ℝ)
    (L δ : ℝ)
    (hlip : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hl : x0 ≤ t) (hr : t ≤ x1)
    (hδ : |x1 - x0| ≤ δ) :
    |f t - f x0| ≤ L * δ := by
  have hL : (0:ℝ) ≤ L := by
    have h1 : |f 0 - f 1| ≤ L := by
      simpa using hlip 0 1
    have h2 : (0:ℝ) ≤ |f 0 - f 1| := abs_nonneg _
    linarith
  have h1 : |f t - f x0| ≤ L * |t - x0| := hlip t x0
  have h2 : |t - x0| = t - x0 := abs_of_nonneg (by linarith)
  have h3 : t - x0 ≤ |x1 - x0| := by
    have : x0 ≤ x1 := le_trans hl hr
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h4 : |x1 - x0| ≤ δ := hδ
  calc |f t - f x0| ≤ L * |t - x0| := h1
    _ = L * (t - x0) := by rw [h2]
    _ ≤ L * |x1 - x0| := mul_le_mul_of_nonneg_left h3 hL
    _ ≤ L * δ := mul_le_mul_of_nonneg_left h4 hL

end Hagi.Pretraining

/-!
# Grokking: разделение временных шкал при weight decay

Источник №9: Boursier, Pesme, Dragomir (NeurIPS 2025),
"Interpolation followed by Riemannian Norm Minimisation".

Gradient flow с малым weight decay lam имеет двухфазную
динамику: быстрое схождение к многообразию критических точек,
затем медленный дрейф нормы на времени O(1/lam). Формализовано
ядро механизма: пост-сходимость траектория следует w' = -lamw
(дрейф нормы), норма экспоненциально убывает как e^{-lamt},
время полужизни ln 2/lam → ∞ при lam → 0. Отсюда grokking:
время обобщения (норма-управляемое) сколь угодно позже
времени обучения (фиксированного) при малом lam.
-/

namespace Hagi.Pretraining.Grokking

open Real

/-- РЕШЕНИЕ ДРЕЙФА: w(t) = w₀·e^{-lamt} — траектория
пост-интерполяционного дрейфа (критическое многообразие:
∇F = 0, остаётся только weight decay). -/
theorem drift_solution (lam w0 t : ℝ) :
    (fun s => w0 * exp (-lam * s)) t = w0 * exp (-lam * t) := rfl

/-- ПРОИЗВОДНАЯ ДРЕЙФА: w' = -lam·w вдоль дрейфа —
решение линеаризованного градиентного потока на
критическом многообразии. -/
theorem drift_hasDeriv (lam w0 t : ℝ) :
    HasDerivAt (fun s => w0 * exp (-lam * s))
      (-lam * (w0 * exp (-lam * t))) t := by
  have h1 : HasDerivAt (fun s => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have h2 := (Real.hasDerivAt_exp _).comp t h1
  have h3 : HasDerivAt (fun s => w0 * exp (-lam * s))
      (w0 * (exp (-lam * t) * (-lam))) t := h2.const_mul w0
  convert h3 using 1
  ring

/-- МОНОТОННЫЙ СПАД НОРМЫ: при lam > 0 норма дрейфа
невозрастает — медленная релаксация к минимальной норме
(риаманов дрейф ℓ₂-нормы из источника). -/
theorem drift_norm_nondecreasing (lam w0 t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    |w0 * exp (-lam * t)| ≤ |w0| := by
  have hexp : 0 ≤ exp (-lam * t) := exp_nonneg _
  have hexp_le : exp (-lam * t) ≤ 1 := by
    have h := exp_le_exp.mpr (show -lam * t ≤ 0 by nlinarith)
    simpa using h
  rw [abs_mul, abs_of_nonneg hexp]
  calc |w0| * exp (-lam * t)
      ≤ |w0| * 1 := mul_le_mul_of_nonneg_left hexp_le (abs_nonneg w0)
    _ = |w0| := mul_one _

/-- ПОЛУЖИЗНЬ НОРМЫ: |w(ln 2/lam)| = |w₀|/2 — характерное время
дрейфа равно (ln 2)/lam, т.е. Θ(1/lam). -/
theorem drift_half_life (lam w0 : ℝ) (hlam : 0 < lam) :
    |w0 * exp (-lam * ((log 2) / lam))| = |w0| / 2 := by
  have hmul : -lam * ((log 2) / lam) = -(log 2) := by
    field_simp
  have hval : exp (-lam * ((log 2) / lam)) = 1 / 2 := by
    rw [hmul, exp_neg, exp_log two_pos]
    norm_num
  have hw : w0 * exp (-lam * ((log 2) / lam)) = w0 / 2 := by
    rw [hval, mul_one_div]
  rw [hw]
  simp [abs_div]

/-- РАЗДЕЛЕНИЕ ШКАЛ (grokking-ядро): для любого быстрого
времени обучения T_fast > 0 найдётся lam > 0 такое, что
время полужизни нормы (ln 2)/lam строго больше T_fast·k —
обобщение задержано сколь угодно относительно обучения
при достаточно малом weight decay. -/
theorem grokking_timescale_separation (T_fast k : ℝ)
    (hT : 0 < T_fast) (hk : 0 < k) :
    ∃ lam > 0, (log 2) / lam > k * T_fast := by
  refine ⟨(log 2) / (k * T_fast + 1), ?_, ?_⟩
  · have h1 : 0 < log 2 := by positivity
    have h2 : 0 < k * T_fast + 1 := by nlinarith
    exact div_pos h1 h2
  · have h1 : 0 < log 2 := by positivity
    have h2 : 0 < k * T_fast + 1 := by nlinarith
    field_simp
    nlinarith

open Real intervalIntegral

/-- ДЛИНА ПУТИ ДРЕЙФА ОГРАНИЧЕНА: полная вариация
пост-интерполяционного дрейфа на [0,t] не превосходит
начальную норму — риманов дрейф ℓ₂-нормы имеет конечный
«бюджет движения» |w₀|, независимо от t. -/
theorem drift_total_variation (lam w0 : ℝ) (hlam : 0 < lam) (t : ℝ) :
    ∫ x in (0)..t, |(-lam) * (w0 * exp (-lam * x))| ≤ |w0| := by
  have habs : ∀ x : ℝ, |(-lam) * (w0 * exp (-lam * x))|
      = lam * |w0| * exp (-lam * x) := by
    intro x
    calc |(-lam) * (w0 * exp (-lam * x))|
        = |(-lam)| * |w0 * exp (-lam * x)| := abs_mul _ _
      _ = lam * (|w0| * |exp (-lam * x)|) := by
          rw [abs_of_neg (show (0:ℝ) > -lam by nlinarith), abs_mul]
          ring
      _ = lam * |w0| * exp (-lam * x) := by
          rw [abs_of_nonneg (exp_nonneg _)]
          ring
  have heq := intervalIntegral.integral_congr
    (a := 0) (b := t) (μ := MeasureTheory.volume)
    (f := fun x => |(-lam) * (w0 * exp (-lam * x))|)
    (fun x _ => habs x)
  rw [heq, intervalIntegral.integral_const_mul]
  -- ∫₀^t e^{−λx} dx = (1 − e^{−λt})/λ  через замену u = −λx
  have hint : ∫ x in (0)..t, exp (-lam * x)
      = (1 - exp (-lam * t)) / lam := by
    have hcom : ∀ x : ℝ, exp (-lam * x) = exp (x * (-lam)) :=
      fun x => by congr 1; ring
    have he := intervalIntegral.integral_congr
      (a := 0) (b := t) (μ := MeasureTheory.volume)
      (f := fun x => exp (-lam * x)) (fun x _ => hcom x)
    rw [he, integral_comp_mul_right exp
      (by nlinarith : (-lam : ℝ) ≠ 0), integral_exp]
    rw [zero_mul, mul_neg, smul_eq_mul, exp_zero]
    field_simp
    ring
  rw [hint]
  have hexp : 0 ≤ exp (-lam * t) := exp_nonneg _
  have hle : 1 - exp (-lam * t) ≤ 1 := by nlinarith
  have hcancel : lam * |w0| * ((1 - exp (-lam * t)) / lam)
      = |w0| * (1 - exp (-lam * t)) := by
    field_simp
  rw [hcancel]
  calc |w0| * (1 - exp (-lam * t))
      ≤ |w0| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg w0)
    _ = |w0| := mul_one _

end Hagi.Pretraining.Grokking

open scoped Matrix

set_option linter.style.header false

/-!
# Spectral trust region — orthogonalized optimizer steps (Muon/ANVIL)

The speedrun recipe trains its block matrices with an
orthogonalized-momentum update (`anvil_lr` on block matrices). The
theory anchor (ask.sciencemadereadable: "Muon Optimizes Under
Spectral Norm Constraints", arXiv:2506.15054; "A Note on the
Convergence of Muon", arXiv:2502.02900): the orthogonalized step
lives under a SPECTRAL trust region — the update direction has
unit operator norm, so the step radius IS the step size.

Exact statements (elementary, no approximation):

* `hadamardRows_sup_bound` — for row-orthonormal `Q`
  (`Q * Qᵀ = 1`), every coordinate of the update direction
  `Q *ᵥ δ` is bounded in absolute value by the L2 norm of `δ`
  (rows have unit length; Cauchy–Schwarz via
  `sum_mul_sq_le_sq_mul_sq`): the orthogonalized step moves each
  weight coordinate by at most `η * ‖δ‖₂`;
* `orthonormal_mulVec_isometry` — full Parseval: a row-orthonormal
  square `Q` preserves the L2 norm of the credit vector
  (`Qᵀ * Q = 1` by invertibility): orthogonalized momentum neither
  amplifies nor damps any direction it moves.
-/

namespace Hagi.Pretraining

/-- Auxiliary: a row-orthonormal square matrix satisfies
`Qᵀ * Q = 1` (columns are orthonormal too — invertibility). -/
theorem transpose_mul_self_of_mul_transpose {m : Type*} [Fintype m]
    [DecidableEq m] (Q : Matrix m m ℝ) (hQ : Q * Qᵀ = 1) :
    Qᵀ * Q = 1 := by
  classical
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h2 : (Q * Qᵀ).det = 1 := by rw [hQ]; simp
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h2
    norm_num at h2
  have hUd : IsUnit Q.det := IsUnit.mk0 Q.det hdet
  have hU : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hUd
  have hinv : Qᵀ = Q⁻¹ := by
    rw [← Matrix.mul_one Q⁻¹, ← hQ, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul Q hUd, Matrix.one_mul]
  rw [hinv, Matrix.nonsing_inv_mul Q hUd]

/-- **Per-coordinate trust-region bound** (run.py/ANVIL: the
orthogonalized update direction moves each weight coordinate by at
most the L2 norm of the credit vector): for row-orthonormal `Q`,
every coordinate of `Q *ᵥ δ` satisfies
`|(Q *ᵥ δ) i| ≤ ‖δ‖₂`. -/
theorem hadamardRows_sup_bound {m : Type*} [Fintype m] [DecidableEq m]
    (Q : Matrix m m ℝ) (δ : m → ℝ) (hQ : Q * Qᵀ = 1) (i : m) :
    |(Q *ᵥ δ) i| ≤ Real.sqrt (∑ j, δ j * δ j) := by
  classical
  have hdiag : ∑ j, Q i j * Q i j = 1 := by
    have h := congrArg (fun M : Matrix m m ℝ => M i i) hQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      at h
    simpa using h
  have hnn : (0:ℝ) ≤ ∑ j, δ j * δ j :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hcs : ((Q *ᵥ δ) i) ^ 2 ≤ ∑ j, δ j * δ j := by
    have hx : (Q *ᵥ δ) i = ∑ j, Q i j * δ j := rfl
    have hcsl := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (fun j => Q i j) (fun j => δ j)
    rw [hx]
    have hcsl' : (∑ j, Q i j * δ j) ^ 2
        ≤ (∑ j, Q i j * Q i j) * ∑ j, δ j * δ j := by
      simpa [sq, mul_pow] using hcsl
    rw [hdiag, one_mul] at hcsl'
    exact hcsl'
  have hkey : ((Q *ᵥ δ) i) ^ 2 ≤ (Real.sqrt (∑ j, δ j * δ j)) ^ 2 := by
    rw [Real.sq_sqrt hnn]
    exact hcs
  have h2 := sq_le_sq.mp hkey
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h2

/-- **Orthogonalized momentum is an isometry** (Parseval): for a
row-orthonormal square `Q`, the update direction `Q *ᵥ δ` has
exactly the same L2 norm as the credit vector `δ`. -/
theorem orthonormal_mulVec_isometry {m : Type*} [Fintype m]
    [DecidableEq m] (Q : Matrix m m ℝ) (δ : m → ℝ) (hQ : Q * Qᵀ = 1) :
    ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i = ∑ j, δ j * δ j := by
  classical
  have hTQ := transpose_mul_self_of_mul_transpose Q hQ
  have hstep : ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i
      = δ ⬝ᵥ (Qᵀ * Q) *ᵥ δ := by
    have hdot : ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i
        = (Q *ᵥ δ) ⬝ᵥ (Q *ᵥ δ) := rfl
    rw [hdot]
    rw [← Matrix.dotProduct_transpose_mulVec Q δ (Q *ᵥ δ),
      ← Matrix.mulVec_mulVec]
  rw [hstep, hTQ, Matrix.one_mulVec]
  rfl

end Hagi.Pretraining
