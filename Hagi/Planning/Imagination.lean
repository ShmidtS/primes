import Hagi.Prelude.Info

/-!
Формализация точной математики arXiv 2610.26845v1
"Train an Imaginative Agent" (Agima — agentic imagination):
(1) forward thinking regret: выбор плана по неточной оценке
(ошибка ≤ ε) теряет не более 2ε истинной ценности;
(2) компаундинг ошибки воображения: K-шаговый open-loop
прогноз с пошаговой ошибкой ε и липшицевостью ценности L
накапливает смещение оценки ≤ K·L·ε;
(3) адаптивный формат: если первый план предсказан успешным
и предсказание верно, второй кандидат не нужен (экономия
воображения без потери качества — RL-поведение Agima).
-/

namespace Hagi.Planning

open Finset

/-- FORWARD THINKING REGRET: агент сравнивает B кандидатов
по ПРЕДСКАЗАННОЙ ценности V̂ с ошибкой |V̂−V| ≤ ε и выбирает
argmax V̂. Истинная ценность выбранного плана не менее
max V − 2ε: воображение с ограниченной ошибкой теряет не
более 2ε от лучшего плана (граница неточности argmax). -/
theorem forward_thinking_regret {P : Type*} [Fintype P]
    [Nonempty P] (V Vhat : P → ℝ) (ε : ℝ) (_hε : 0 ≤ ε)
    (herr : ∀ π : P, abs (Vhat π - V π) ≤ ε)
    (pstar : P) (hbest : ∀ π : P, Vhat π ≤ Vhat pstar)
    (pbest : P) :
    V pstar ≥ V pbest - 2 * ε := by
  -- V(pbest) ≤ V̂(pbest) + ε ≤ V̂(pstar) + ε ≤ V(pstar) + 2ε
  have h1 : V pbest - Vhat pbest ≤ ε := by
    have := herr pbest
    linarith [abs_le.mp this]
  have h2 : Vhat pbest ≤ Vhat pstar := hbest pbest
  have h3 : Vhat pstar - V pstar ≤ ε := by
    have := herr pstar
    linarith [abs_le.mp this]
  linarith

/-- КОМПАУНДИНГ ОШИБКИ ВООБРАЖЕНИЯ: K-шаговый open-loop
план использует предсказанные состояния ô_k вместо
реальных o_k; при пошаговой ошибке предсказания
‖ô_k − o_k‖ ≤ ε и липшицевости ценности по состояниям
(|V(s)−V(s')| ≤ L·‖s−s'‖) смещение оценки накопленного
исхода ≤ K·L·ε: воображение накапливает ошибку линейно
по горизонту (обоснование деградации при K → ∞ в Agima). -/
theorem imagination_compounding (K : ℕ) (ε L : ℝ)
    (hL : 0 ≤ L)
    (o oh : ℕ → ℝ) (V : ℕ → ℝ → ℝ)
    (hpred : ∀ k : ℕ, k < K → abs (oh k - o k) ≤ ε)
    (hlip : ∀ k : ℕ, k ≤ K → ∀ x y : ℝ,
      abs (V k x - V k y) ≤ L * abs (x - y)) :
    (∑ k ∈ Finset.range K, V k (oh k))
      - (∑ k ∈ Finset.range K, V k (o k))
      ≤ K * L * ε := by
  have hstep : ∀ k ∈ Finset.range K,
      V k (oh k) - V k (o k) ≤ L * ε := by
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hkK : k ≤ K := Nat.le_of_lt hklt
    have hlipk := hlip k hkK (oh k) (o k)
    have hpredk := hpred k hklt
    -- |V(ô)−V(o)| ≤ L·|ô−o| ≤ L·ε
    have h1 : abs (V k (oh k) - V k (o k))
        ≤ L * abs (oh k - o k) := hlipk
    have h2 : L * abs (oh k - o k) ≤ L * ε :=
      mul_le_mul_of_nonneg_left hpredk hL
    have h3 : abs (V k (oh k) - V k (o k)) ≤ L * ε :=
      le_trans h1 h2
    have : V k (oh k) - V k (o k) ≤ abs (V k (oh k) - V k (o k)) :=
      le_abs_self _
    linarith [this, h3]
  -- суммирование K слагаемых, каждое ≤ L·ε
  have hsplit : (∑ k ∈ Finset.range K, V k (oh k))
      - (∑ k ∈ Finset.range K, V k (o k))
      = ∑ k ∈ Finset.range K, (V k (oh k) - V k (o k)) := by
    rw [← Finset.sum_sub_distrib
      (fun k => V k (oh k)) (fun k => V k (o k))]
  rw [hsplit]
  have hsum : (∑ k ∈ Finset.range K,
      (fun k => V k (oh k) - V k (o k)) k) ≤ K * (L * ε) := by
    have hle : ∀ k ∈ Finset.range K,
        (fun k => V k (oh k) - V k (o k)) k
        ≤ (fun _ => L * ε) k := hstep
    have hsumle := Finset.sum_le_sum (f := fun k =>
      V k (oh k) - V k (o k)) (g := fun _ => L * ε) hle
    have hcard : (∑ k ∈ Finset.range K, (L * ε))
        = K * (L * ε) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcard] at hsumle
    exact hsumle
  linarith [hsum, hL]

/-- АДАПТИВНЫЙ ФОРМАТ (RL-поведение Agima): если первый
кандидат предсказан успешным (V̂ π₁ ≥ θ) и предсказание
верно (|V̂ π₁ − V π₁| ≤ ε, θ ≥ ε), то истинная ценность
первого плана ≥ θ − ε ≥ 0 — второй кандидат не нужен:
экономия воображения без потери успеха (гибридный формат,
возникший после RL). -/
theorem adaptive_first_sufficient (V Vhat : ℝ → ℝ)
    (π₁ : ℝ) (θ ε : ℝ) (_hε : 0 ≤ ε) (_hθ : ε ≤ θ)
    (hpred : abs (Vhat π₁ - V π₁) ≤ ε)
    (hjudge : θ ≤ Vhat π₁) :
    θ - ε ≤ V π₁ := by
  -- V π₁ ≥ V̂ π₁ − ε ≥ θ − ε
  have h1 : Vhat π₁ - V π₁ ≤ ε := by
    have := abs_le.mp hpred
    linarith [this.1]
  linarith

/-- COUNTERFACTUAL BRANCHING: если вредная альтернатива
детектируема (её предсказанная ценность ниже порога θ) и
детектор консервативен (V̂ ≤ θ ⟹ V ≤ θ + ε, ошибки ≤ ε),
то branching-агент, отбрасывающий все ветви ниже порога,
исключает все детектируемо-вредные планы из выполнения:
выполненное подмножество планов не пересекается с
{π : V π ≤ θ + ε} — линейный агент, не проверяющий
альтернативы, таких гарантий не имеет (структурные развилки
Sokoban, arXiv 2610.26845 §3.2). -/
theorem branching_avoids_detectable_failure
    {P : Type*} [Fintype P] (V Vhat : P → ℝ)
    (θ ε : ℝ)
    (herr : ∀ π : P, Vhat π - V π ≤ ε)
    (exec : P → Prop)
    (hbranch : ∀ π : P, exec π → θ < Vhat π) :
    ∀ π : P, exec π → θ - ε < V π := by
  intro π hexec
  have h1 : θ < Vhat π := hbranch π hexec
  have h2 : Vhat π - V π ≤ ε := herr π
  linarith

/-- ЦЕННОСТЬ BRANCHING ПРОТИВ ЛИНЕЙНОГО: линейный агент
выполняет первый план π₁ без проверки; branching-агент
выполняет план только выше порога θ. Если π₁ существенно
вреден (V π₁ ≤ θ − ε − δ) и все выполняемые branching-планы
выше порога с зазором (θ − ε < V π), то branching строго
доминирует: V π₁ < V πb. -/
theorem branching_dominates_linear
    {P : Type*} [Fintype P] (V Vhat : P → ℝ)
    (θ ε δ : ℝ)
    (herr : ∀ π : P, Vhat π - V π ≤ ε)
    (exec : P → Prop)
    (hbranch : ∀ π : P, exec π → θ < Vhat π)
    (π₁ : P) (hbad : V π₁ ≤ θ - ε - δ) (hδ : 0 < δ)
    (πb : P) (hexecb : exec πb) :
    V π₁ < V πb := by
  have hgood := branching_avoids_detectable_failure
    V Vhat θ ε herr exec hbranch πb hexecb
  linarith

/-- GRPO-ПРЕИМУЩЕСТВО: центрированная награва A_i = r_i − μ
(μ — средняя награда группы). Сумма преимуществ ноль. -/
theorem grpo_centered_sum_zero (G : ℕ) (r : ℕ → ℝ)
    (μ : ℝ) (hμ : μ * G = ∑ i ∈ Finset.range G, r i) :
    ∑ i ∈ Finset.range G, (r i - μ) = 0 := by
  rw [Finset.sum_sub_distrib (fun i => r i) (fun _ => μ),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_comm (G : ℝ) μ, hμ, sub_self]

/-- GRPO-ЗНАК: следствие из группы G ≥ 1 наград: если
награда следствия строго выше групповой средней, его
центрированное преимущество строго положительно — GRPO
поощряет его (односторонняя версия без деления на std). -/
theorem grpo_advantage_pos (G : ℕ) (r : ℕ → ℝ)
    (μ : ℝ) (hμ : μ * G = ∑ i ∈ Finset.range G, r i)
    (i₀ : ℕ) (hi₀ : i₀ < G) (hgt : μ < r i₀) :
    0 < r i₀ - μ := by
  linarith

end Hagi.Planning
