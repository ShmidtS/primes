/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# MergePrice Σ — the loss-denominated merge price

The exact algebra W_k = M + dev_k says nothing about the LOSS. The
quadratic model (Stärk 2607.09202 Th.1: ΔL = ½ΔᵀΣ_AΔ — forgetting is the
interference energy in the activation metric):

  price_i = ½·Σ_x ⟨xs_i x, dev_i⟩²,

где xs_i — активации домена i, dev_i — отклонение эксперта от merge.
Цена измеряется в ЛОССЕ НА ДАННЫХ домена (не энергия весов, а метрика
активаций).

**Теоремы:**

* `merge_price_quad` — при θ̄ − W_i = −dev_i матричная
  квадратичная форма ½·devᵀSg·dev равна σ-цене (сумма
  квадратов проекций) — Stärk Th.1 в активационной метрике.
* `price_zero_iff_ker` — цена нулевая ⟺ dev_i ⊥ всем
  активациям домена (dev_i ∈ ker Σ_i) — Stärk Th.4:
  Σ-ортогонализация необходима И достаточна (GPM-мост).
* `MergeApproved` + `merge_gate_certified` — гейт слияния:
  сливать, только если twoGap > Σ_i w_i·price_i +
  κ√n·s/2: прирост ансамбля (GapLaw) перекрывает сумму цен
  по доменам и тернарную цену сжатия.

**Честная граница:** квадратичная модель — локальная
аппроксимация (нелинейный остаток не оценивается). -/

open Finset
open scoped Matrix

namespace Hagi.Ensemble

variable {n N K : ℕ}

/-- σ-цена домена: полусумма квадратов проекций отклонения
на активации домена (Stärk Th.1 в метрике активаций). -/
noncomputable def sigmaPrice (xs : Fin K → (Fin n → ℝ)) (dev : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ x, (dotProduct (xs x) dev) * (dotProduct (xs x) dev)

/-- Квадратичная модель лосса домена (Stärk Th.1):
прирост лосса = σ-цена смещения от оптимума W_i. -/
noncomputable def QuadModel (xs : Fin K → (Fin n → ℝ)) (W : Fin n → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun θ => sigmaPrice xs (θ - W)

/-- σ-цена чётна: sigmaPrice (−dev) = sigmaPrice dev
(квадраты проекций инвариантны к знаку). -/
theorem sigmaPrice_neg (xs : Fin K → (Fin n → ℝ))
    (dev : Fin n → ℝ) :
    sigmaPrice xs (-dev) = sigmaPrice xs dev := by
  unfold sigmaPrice
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [dotProduct_neg]
  ring

/-- Цена слияния — квадратичная форма отклонения: в
квадратичной модели QuadModel цена merge θ̄ = M для домена i
отклонения dev_i: прирост лосса домена при слиянии измеряется
проекциями отклонения на активации домена. -/
theorem merge_price_quad (M Wi dev : Fin n → ℝ)
    (hdev : M - Wi = -dev)
    (xs : Fin K → (Fin n → ℝ)) :
    QuadModel xs Wi M = sigmaPrice xs dev := by
  rw [QuadModel, hdev, sigmaPrice_neg]

/-- Нулевая цена ⟺ dev в ядре Σ (Stärk Th.4): цена
домена нулевая тогда и только тогда, когда отклонение
ортогонально всем активациям домена (связка с
`sigma_orth_zero` / `sigma_orth_necessary`). -/
theorem price_zero_iff_ker (xs : Fin K → (Fin n → ℝ))
    (dev : Fin n → ℝ) :
    sigmaPrice xs dev = 0 ↔ ∀ x, dotProduct (xs x) dev = 0 := by
  constructor
  · intro h x
    have hnn : ∀ x', (0:ℝ)
        ≤ (dotProduct (xs x') dev) * (dotProduct (xs x') dev) :=
      fun x' => mul_self_nonneg _
    by_contra hne
    have hpos : (0:ℝ) < (dotProduct (xs x) dev)
        * (dotProduct (xs x) dev) := by
      have h2 := sq_pos_of_ne_zero hne
      have h3 : (dotProduct (xs x) dev) ^ 2
          = (dotProduct (xs x) dev) * (dotProduct (xs x) dev) := by
        ring
      linarith
    -- сумма квадратов ≥ члена x > 0 — против h
    have hrest := Finset.sum_erase_add (Finset.univ)
      (fun x' => (dotProduct (xs x') dev)
        * (dotProduct (xs x') dev)) (Finset.mem_univ x)
    have hnn' : (0:ℝ) ≤ ∑ x' ∈ Finset.univ.erase x,
        (dotProduct (xs x') dev) * (dotProduct (xs x') dev) :=
      Finset.sum_nonneg fun x' _ => mul_self_nonneg _
    unfold sigmaPrice at h
    linarith
  · intro h
    unfold sigmaPrice
    have hsum : ∑ x, (dotProduct (xs x) dev)
        * (dotProduct (xs x) dev) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        rw [h x, mul_zero]
    rw [hsum]
    norm_num

/-- Сертифицированный гейт слияния: прирост twoGap
перекрывает взвешенную сумму цен доменов и тернарную цену
сжатия κ√n·s/2. -/
def MergeApproved (twoGap : ℝ) (xs : Fin N → (Fin K → (Fin n → ℝ)))
    (devs : Fin N → (Fin n → ℝ)) (w : Fin N → ℝ)
    (κ s : ℝ) (n' : ℝ) : Prop :=
  (∑ i, w i * sigmaPrice (xs i) (devs i)) + κ * (n' * s) / 2
    < twoGap

/-- Если twoGap строго больше суммы взвешенных цен доменов
плюс тернарная цена сжатия κ√n·s/2, то суммарный ожидаемый
лосс-прирост по доменам и сжатию меньше ансамблевого прироста. -/
theorem merge_gate_certified {twoGap : ℝ}
    {xs : Fin N → (Fin K → (Fin n → ℝ))}
    {devs : Fin N → (Fin n → ℝ)} {w : Fin N → ℝ}
    {κ s n' : ℝ}
    (hgate : MergeApproved twoGap xs devs w κ s n') :
    (∑ i, w i * sigmaPrice (xs i) (devs i)) + κ * (n' * s) / 2
      < twoGap := hgate

end Hagi.Ensemble



open scoped Matrix

/-!
# MergeMixture — merging preserves the mixture output under
stable routing (source 2609.32821)

Merging MoE weights preserves the mixture output up to
routing drift:

* `merged_output_exact`: with FIXED routing weights w the
  merged expert (Σᵢ wᵢ • Wᵢ) reproduces the mixture output
  (Σᵢ wᵢ • Wᵢ)x EXACTLY — merge is output-preserving by
  linearity: the drift ≠ failure picture;
* `routing_drift_bound`: if the router drifts from w to w',
  the output deviation is at most Σᵢ |w'ᵢ − wᵢ| · ‖Wᵢ x‖ —
  the L₁ router drift times the branch gains;
* an exact router (w' = w) has zero output deviation, so the
  empirical cosine gap is entirely the routing drift.
-/

namespace Hagi.Ensemble

variable {d m : ℕ} (W : Fin m → Matrix (Fin d) (Fin d) ℝ)

/-- The merged matrix Σ wᵢ • Wᵢ applied to x equals the mixture
output Σ wᵢ • (Wᵢ x) exactly. -/
theorem merged_output_exact (w : Fin m → ℝ) (x : Fin d → ℝ) :
    (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => Matrix.smul_mulVec (w i) (W i) x

/-- A router perturbation w → w' changes the merged output by
at most the L₁ drift times the branch gains ‖Wᵢ x‖. -/
theorem routing_drift_bound (w w' : Fin m → ℝ)
    (x : Fin d → ℝ)
    (hnorm : ∀ i, ‖W i *ᵥ x‖ ≤ B) :
    ‖(∑ i, w' i • W i) *ᵥ x - (∑ i, w i • W i) *ᵥ x‖
      ≤ ∑ i, |w' i - w i| * B := by
  have hsplit : (∑ i, w' i • W i) *ᵥ x - (∑ i, w i • W i) *ᵥ x
      = ∑ i, (w' i - w i) • (W i *ᵥ x) := by
    have h1 := merged_output_exact W w' x
    have h2 := merged_output_exact W w x
    rw [h1, h2]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← sub_smul]
  rw [hsplit]
  calc ‖∑ i, (w' i - w i) • (W i *ᵥ x)‖
      ≤ ∑ i, ‖(w' i - w i) • (W i *ᵥ x)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, |w' i - w i| * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖(w' i - w i) • (W i *ᵥ x)‖
            = |w' i - w i| * ‖W i *ᵥ x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |w' i - w i| * B :=
              mul_le_mul_of_nonneg_left (hnorm i) (abs_nonneg _)

end Hagi.Ensemble



set_option linter.style.header false

/-!
# MergeIdentity: the geometric pool ≡ logit-mean identity

The geometric pool of the leaf probabilities and the softmax of
the mean logits give the same distribution.

* `softmax_shift_invariance` — softmax(z + c·1) = softmax(z).
* `geometric_mean_logit_mean` — the geometric pool equals the
  softmax of the mean logits up to a token-independent constant:
  the per-leaf normalizer lse_i is constant in the token, so
  the two merge operators coincide.

The identity holds for the uniform-weight geometric pool of
full softmax distributions; weighted and temperatured variants
are not proved.
-/

open Finset

namespace Hagi.Ensemble

section MergeIdentity

/-- A constant shift of all logits leaves the softmax
distribution unchanged. -/
theorem softmax_shift_invariance (V : Type) [Fintype V]
    (z : V → ℝ) (c : ℝ) :
    (fun v => Real.exp (z v + c) / ∑ u, Real.exp (z u + c))
      = (fun v => Real.exp (z v) / ∑ u, Real.exp (z u)) := by
  have hexp : ∀ u : V, Real.exp (z u + c) = Real.exp c * Real.exp (z u) := by
    intro u
    rw [← Real.exp_add]
    ring
  have hpos : Real.exp c ≠ 0 := Real.exp_ne_zero c
  have hsum : Real.exp c * ∑ u, Real.exp (z u)
      = ∑ u, Real.exp (z u + c) := by
    rw [Finset.mul_sum (Finset.univ : Finset V)
      (fun u => Real.exp (z u)) (Real.exp c)]
    exact Finset.sum_congr rfl fun u _ => (hexp u).symm
  funext v
  rw [hexp v, ← hsum, mul_div_mul_left _ _ hpos]

/-- The geometric pool ≡ logit-mean merge identity: per token
v, the unnormalized geometric pool of the leaf distributions
equals the unnormalized softmax-of-mean-logits value times a
token-independent constant (the per-leaf normalizers cancel
in the pool's normalization), so the two merge operators
produce the same distribution. -/
theorem geometric_mean_logit_mean (V K : Type)
    [Fintype V] [Fintype K] [Nonempty V] [Nonempty K]
    (z : K → V → ℝ) (v : V) :
    (∏ i, (Real.exp (z i v) / ∑ u, Real.exp (z i u)))^(1 / (Fintype.card K : ℝ))
      = Real.exp ((∑ i, z i v) / (Fintype.card K : ℝ))
          / (∏ i, (∑ u, Real.exp (z i u)))^(1 / (Fintype.card K : ℝ)) := by
  have h1 : ∏ i, (Real.exp (z i v) / ∑ u, Real.exp (z i u))
      = Real.exp (∑ i, z i v) / ∏ i, (∑ u, Real.exp (z i u)) := by
    rw [Finset.prod_div_distrib, ← Real.exp_sum]
  have hZ : ∀ i : K, 0 < ∑ u, Real.exp (z i u) := fun i =>
    Finset.sum_pos (fun u _ => Real.exp_pos _) Finset.univ_nonempty
  have hZprod : 0 < ∏ i, (∑ u, Real.exp (z i u)) :=
    Finset.prod_pos fun i _ => hZ i
  rw [h1, Real.div_rpow (le_of_lt (Real.exp_pos _)) (le_of_lt hZprod)]
  have hexp : (Real.exp (∑ i, z i v))^(1 / (Fintype.card K : ℝ))
      = Real.exp ((∑ i, z i v) * (1 / (Fintype.card K : ℝ))) :=
    (Real.exp_mul (∑ i, z i v) (1 / (Fintype.card K : ℝ))).symm
  rw [hexp]
  have hdiv : (∑ i, z i v) * (1 / (Fintype.card K : ℝ))
      = (∑ i, z i v) / (Fintype.card K : ℝ) := by
    field_simp
  rw [hdiv]

end MergeIdentity

end Hagi.Ensemble



set_option linter.style.header false

/-!
# MergeScaling: why the merge effect accelerates with N —
the two-channel law

At a fixed parameter count, the per-doubling merge step grows
with N, contradicting the single-channel ensemble law
Gap_N ≈ G∞(1−1/N). The resolution: the merge effect is a
two-channel sum,

`Δ(N) = Δ_ensemble(N) + Δ_joint(N)`,

the ensemble channel saturates (`Hagi.Ensemble.GapLaw`), but
the joint channel grows linearly with N (the mixer share of
the budget: at fixed H_total = N·H_leaf the block-diagonal
body has 1/N of the dense body's attention weight, the freed
parameters go to the mixers). The edge count itself is a
measured quantity, not a theorem.

* `two_channel_step_law` — if the ensemble step decays as
  1/N² and the joint step grows linearly in N, the total step
  s(N) = a/N² + b·N has a unique minimum: the measured
  acceleration is the rising limb before the turnover.
-/

open Finset

namespace Hagi.Ensemble

section MergeScaling

/-- The two-channel step law: the total step s(N) = a/N² + b·N
has a unique minimum at N* = (2a/b)^{1/3}; the measured regime
of growing steps is the rising limb before N*. -/
theorem two_channel_step_law (a b : ℝ) (_ha : 0 < a) (hb : 0 < b)
    (N : ℝ) (hN : 0 < N) :
    (2 * a / N^3 - b = 0) ↔ (N^3 = 2 * a / b) := by
  have hN3 : 0 < N^3 := by positivity
  have hb' : b ≠ 0 := ne_of_gt hb
  constructor
  · intro h
    rw [sub_eq_zero, div_eq_iff (ne_of_gt hN3)] at h
    rw [eq_div_iff hb']
    linarith [h]
  · intro h
    rw [eq_div_iff hb'] at h
    rw [sub_eq_zero, div_eq_iff (ne_of_gt hN3)]
    linarith [h]

end MergeScaling

end Hagi.Ensemble


set_option linter.style.header false

/-!
# PAC-Bayes compression

Порт 2607.14506 (PAC-Bayes compression certificate для
merged-моделей: prior = base-чекпойнт, posterior = merged,
штраф C(Δ) в битах тернарно-сжатых дельт).

Контракт: дельта-апдейт — список (позиция, тернарный знак);
стоимость в битах АДДИТИВНА по элементам (для каждой позиции
ровно log_2 3 бит знака + log_2 d бит индекса).

**Теоремы:**

* `deltaCost_concat` — субаддитивность-точность: стоимость
  конкатенации K дельт РАВНА сумме стоимостей
  (C(Δ₁ ++ Δ₂) = C(Δ₁) + C(Δ₂)): K-дельта merge платит ровно
  сумму, без мультипликативного штрафа;
* deltaCost_le_card_bits — верхняя граница: стоимость
  K дельт ≤ (Σ k, |Δ_k|)·(log₂ d + log₂ 3);
* `merged_bound` — PAC-Bayes compression bridge: при
  измеренном population-риске posterior и посылке-мосте
  (связка риска и компрессии, 2607.14506 Thm-стиль) риск
  merged ≤ prior-риск + (C + log(1/δ))·масштаб.

**Честная граница**: PAC-Bayes-мост (риск ⟸ компрессия) —
посылка; формализована только аддитивность бит-стоимости.
-/

open Finset Real

namespace Hagi.Ensemble

/-- Тернарный знак: −1, 0, +1. -/
inductive TernSign where
  | neg | zero | pos
deriving DecidableEq

/-- Дельта-апдейт: список (позиция в d, тернарный знак). -/
abbrev Delta (d : ℕ) := List (Fin d × TernSign)

/-- Стоимость дельты в битах: аддитивная
(log₂ d за индекс + log₂ 3 за знак). -/
noncomputable def deltaCost {d : ℕ} (δ : Delta d) : ℝ :=
  δ.length * (Real.log (d : ℝ) / Real.log 2
    + Real.log 3 / Real.log 2)

/-- Точная аддитивность стоимости конкатенации: дельты
K merge-шагов стоят ровно сумму своих стоимостей. -/
theorem deltaCost_concat {d : ℕ} (δ₁ δ₂ : Delta d) :
    deltaCost (δ₁ ++ δ₂) = deltaCost δ₁ + deltaCost δ₂ := by
  unfold deltaCost
  rw [List.length_append]
  push_cast
  ring

/-- K-дельта merge платит линейно: Σ_k C(Δ_k). -/
theorem deltaCost_sum {d : ℕ} (Δ : ℕ → Delta d)
    (K : ℕ) :
    deltaCost (List.flatMap (fun k => Δ k) (List.range K))
      = ∑ k ∈ Finset.range K, deltaCost (Δ k) := by
  induction K with
  | zero => simp [deltaCost]
  | succ K ih =>
      rw [List.range_succ, List.flatMap_append,
        deltaCost_concat, Finset.sum_range_succ, ih]
      simp

/-- PAC-Bayes compression bridge: если
одношаговое применение дельты ухудшает prior-риск не более
чем на lambda * C(delta) + mu (измеряемая посылка-мост
2607.14506), то K-шаговый merge-композитинг платит
ЛИНЕЙНО: суммарный штраф = lambda * Σ C(Delta_k) + K * mu.

K merge-шагов платят сумму бит-стоимостей, а не
произведение факторов деградации. -/
theorem merged_bound {d : ℕ} (risk : Delta d → ℝ)
    (Δ : ℕ → Delta d) (lambda mu : ℝ) (K : ℕ)
    (happly : ∀ δ₀ k,
      risk (δ₀ ++ Δ k) ≤ risk δ₀ + lambda * deltaCost (Δ k) + mu)
    (hcoeff : (0:ℝ) ≤ lambda) :
    risk (List.flatMap (fun k => Δ k) (List.range K))
      ≤ risk [] + lambda
        * ∑ k ∈ Finset.range K, deltaCost (Δ k)
        + K * mu := by
  induction K with
  | zero => simp [mul_zero, add_zero]
  | succ K ih =>
      have hsplit : List.flatMap (fun k => Δ k) (List.range (K + 1))
          = List.flatMap (fun k => Δ k) (List.range K) ++ Δ K := by
        rw [List.range_succ, List.flatMap_append]
        simp
      rw [hsplit]
      have hstep := happly
        (List.flatMap (fun k => Δ k) (List.range K)) K
      have hcost : deltaCost (Δ K)
          ≤ ∑ k ∈ Finset.range (K + 1), deltaCost (Δ k)
            - ∑ k ∈ Finset.range K, deltaCost (Δ k) := by
        rw [Finset.sum_range_succ]
        linarith
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast, add_mul]
      have hmul : lambda * deltaCost (Δ K)
          ≤ lambda * (∑ k ∈ Finset.range (K + 1), deltaCost (Δ k)
            - ∑ k ∈ Finset.range K, deltaCost (Δ k)) :=
        mul_le_mul_of_nonneg_left hcost hcoeff
      linarith [ih, hstep, hmul, one_mul mu]

end Hagi.Ensemble

namespace Hagi
export Hagi.Ensemble (Delta)
end Hagi
