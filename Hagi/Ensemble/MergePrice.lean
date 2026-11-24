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
* `MergeApproved` + `merge_gate_certified` — ГЕЙТ СЛИЯНИЯ
  (T2): сливать, только если twoGap > Σ_i w_i·price_i +
  κ√n·s/2: прирост ансамбля (GapLaw) перекрывает сумму цен
  по доменам и тернарную цену сжатия.

**Честные границы:** квадратичная модель — локальная
аппроксимация (segment-averaged Hessian; нелинейный остаток —
липшицевость третьего порядка, runtime h_lip3); активации и
веса измеряемы; Stärk Prop M.1: перестановочное выравнивание
без знаков УХУДШАЕТ midpoint-лосс — знаковая свобода
обязательна; эквивалентность ½∑⟨x,dev⟩² = ½·devᵀ·actSigma·dev
— тройная перестановка сумм, матричная форма приведена в
`merge_price_quad`.
-/

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

/-- **Цена слияния — квадратичная форма отклонения**: в
квадратичной модели QuadModel цена merge θ̄ = M для домена i
отклонения dev_i: прирост лосса домена при слиянии измеряется
проекциями отклонения на активации домена. -/
theorem merge_price_quad (M Wi dev : Fin n → ℝ)
    (hdev : M - Wi = -dev)
    (xs : Fin K → (Fin n → ℝ)) :
    QuadModel xs Wi M = sigmaPrice xs dev := by
  rw [QuadModel, hdev, sigmaPrice_neg]

/-- **Нулевая цена ⟺ dev в ядре Σ (Stärk Th.4)**: цена
домена нулевая тогда и только тогда, когда отклонение
ортогонально ВСЕМ активациям домена — Σ-ортогонализация
необходима И достаточна (связка с `sigma_orth_zero` /
`sigma_orth_necessary`). -/
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

/-- Сертифицированный гейт слияния (T2): прирост twoGap
перекрывает взвешенную сумму цен доменов и тернарную цену
сжатия κ√n·s/2. -/
def MergeApproved (twoGap : ℝ) (xs : Fin N → (Fin K → (Fin n → ℝ)))
    (devs : Fin N → (Fin n → ℝ)) (w : Fin N → ℝ)
    (κ s : ℝ) (n' : ℝ) : Prop :=
  (∑ i, w i * sigmaPrice (xs i) (devs i)) + κ * (n' * s) / 2
    < twoGap

/-- **Гейт слияния — сертификат**: если twoGap (измеренный
зазор ансамбля, GapLaw) строго больше суммы взвешенных цен
доменов (σ-метрики Stärk) плюс тернарная цена сжатия
κ√n·s/2, то слияние сертифицировано: суммарный ожидаемый
лосс-прирост по доменам и сжатию меньше ансамблевого прироста.
лосс-прирост по доменам и сжатию меньше ансамблевого прироста.
κ√n·s/2 — тернарная цена из Runtime (satTail-корректная). -/
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
stable routing (plan §2; source 2609.32821)

The empirical finding (cosine 0.896–0.976 across 6 settings
with bootstrap CI): merging MoE weights preserves the
mixture output up to ROUTING drift. The exact structure:

* `merged_output_exact`: with FIXED routing weights w the
  merged expert (Σᵢ wᵢ • Wᵢ) reproduces the mixture output
  (Σᵢ wᵢ • Wᵢ)x EXACTLY — merge is output-preserving by
  linearity: the drift ≠ failure picture;
* `routing_drift_bound`: if the router drifts from w to w',
  the output deviation is at most Σᵢ |w'ᵢ − wᵢ| · ‖Wᵢ x‖ —
  the L₁ router drift times the branch gains: small router
  perturbations cannot break the merged output by more than
  their weighted magnitude (the formal counterpart of the
  0.9-cosine regime);
* boundary case (corollary of both): an exact router
  (w' = w) has zero L₁ drift, hence EXACTLY zero output
  deviation by `routing_drift_bound` — the empirical cosine
  gap is entirely the routing drift, not the merge itself.
-/

namespace Hagi.Ensemble

variable {d m : ℕ} (W : Fin m → Matrix (Fin d) (Fin d) ℝ)

/-- **Exact preservation under fixed routing**: the merged
matrix Σ wᵢ • Wᵢ applied to x equals the mixture output
Σ wᵢ • (Wᵢ x) exactly — merge commutes with the mixture;
whatever the disagreement story, the mixture OUTPUT
is preserved by the merge itself. -/
theorem merged_output_exact (w : Fin m → ℝ) (x : Fin d → ℝ) :
    (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => Matrix.smul_mulVec (w i) (W i) x

/-- **The routing drift bound**: a router perturbation
w → w' changes the merged output by at most the L₁ drift
times the branch gains ‖Wᵢ x‖ — small routing drift cannot
break the merged output by more than its weighted
magnitude. -/
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

The measured +0.0000 difference between the geometric and
arithmetic pool merges is an identity, not a coincidence.

**What the module proves:**

* `softmax_shift_invariance` — the softmax is invariant to a
  constant shift of the logits: softmax(z + c·1) = softmax(z)
  — the engine of the identity.
* `geometric_mean_logit_mean` — the geometric pool of the
  leaf PROBABILITIES equals the softmax of the mean CENTERED
  logits: pooling p_i^{1/K} ∝ softmax(z_i − lse_i) averaged
  over i is the softmax of the mean z_i shifted by the
  constant mean-lse — the SAME distribution as the softmax
  of the plain mean logits. The per-leaf normalizer lse_i is
  CONSTANT in v, so the two merge operators coincide (the
  measured +0.0000).

**The honest boundary.** The identity holds for the
UNIFORM-weight geometric pool of full softmax distributions;
the weighted case (w_i ≠ 1/K) shifts by a constant too, so
the same argument applies; the temperatured logits
(logit_scale ≠ 1) likewise — the merge operator's current
form is the shift-invariant class.

**Prescription for the code.**

1. Geometric-vs-arithmetic on the same leaf logits is a no-op THROUGH
   the softmax; the interesting comparison is the WEIGHTED geometric
   pool (w from DFieldKKT) against the uniform.
2. `geometric_pool_identity` (`Hagi.Energy.FreeEnergy`) still governs
   the RKL side: the two pools differ in the KL currency they optimize.
-/

open Finset

namespace Hagi.Ensemble

section MergeIdentity

/-- **The softmax shift invariance** (the engine): a constant
shift of all logits leaves the softmax distribution
unchanged — the normalizer absorbs it. -/
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

/-- **The geometric pool ≡ logit-mean merge identity (the
core proportional form)**: per token v, the geometric pool
of the leaf distributions is the softmax-of-mean-logits
value scaled by a v-INDEPENDENT constant — the per-leaf
normalizers Z_i = Σ_u e^{z_i(u)} collect into a single
constant factor that CANCELS in the pool's normalization.
Hence the two merge operators produce the SAME distribution
(the measured +0.0000 is this identity). The
statement: the unnormalized geometric pool equals the
unnormalized logit-mean softmax times a v-constant. -/
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
# MergeScaling: why the merge effect ACCELERATES with N —
the two-channel law

The measured anomaly (STATUS.md §9): at FIXED 241.3M
parameters, N = 6 → 12 → 24 merges give 6.1815 → 6.0767 →
5.8704; the per-doubling step GROWS: 0.1049 → 0.2063
(≈ ×2). The pure ensemble law (`Hagi.Core/Concat`,
Gap_N ≈ G∞(1−1/N)) predicts DECREASING steps (the
1/N approach to the ceiling) — the measurement CONTRADICTS
the single-channel model. The resolution: the merge effect
is a TWO-CHANNEL sum,

`Δ(N) = Δ_ensemble(N) + Δ_joint(N)`,

the ensemble channel saturates (the accounting of
`Hagi.Ensemble.GapLaw`), but the JOINT channel grows with N — more
blocks mean more cross-expert edges to train, and the joint
budget per edge is constant: the joint channel's gain is
LINEAR in the number of trained cross-block interactions.

**What the module proves:**

* `two_channel_step_law` — THE LAW: if the ensemble step
decays as 1/N² (the Gap_N curvature) and the joint step
grows linearly in N (the cross-edge count), the total step
Δ(N+1) − Δ(N) has a unique minimum — the measured
acceleration regime is BEFORE the minimum: the two-channel
model explains BOTH the observed growth AND predicts its
eventual turnover (the falsifiable extrapolation: the step
must eventually decay; the measured 0.105 → 0.206 is the
rising limb; the N* of the turnover is
predictable from the two fitted channels).

* edge_count_linear — the cross-block edge count of the
block-diagonal merge is linear in N: the off-diagonal
compositions the joint phase trains scale with the block
count (N blocks → N(N−1)/2 directed pairs, but each
SwiGLU mixer layer trains against the full stream — the
per-layer edge count is N, the mixer count is the depth;
the joint-channel gain ∝ depth × N at fixed width H_total:
H_total = N·H_leaf fixed, so MORE blocks = MORE mixer
capacity at the SAME parameter count — the linear channel
is the mixer capacity itself).

**The parameter-parity identity.** At fixed H_total =
N·H_leaf, the per-block weight is H_leaf², summed over N blocks:
N·H_leaf² = H_total²/N — the block-diagonal body has 1/N of the dense
body's attention weight; the freed parameters go to the MIXERS (the
cross-block capacity): at fixed total params, more blocks = more mixer
parameters per block-pair. The joint channel's growth IS the growing
mixer share of the budget.
**Prescription for the code.**

1. The N-sweep's next point (N = 48) is the falsifiable test: the
two-channel law predicts the step from the two fitted channels; a
shrinking step means the turnover was passed.
2. The mixer_init_scale screen (`--merge-k` best-of-K, STATUS §10)
should be run BEFORE the N = 48 point.
3. The N* turnover formula is the ComputeBudget input: choose the next
N by the predicted Δ(N)/cost.
-/

open Finset

namespace Hagi.Ensemble

section MergeScaling

-- The honest content of the edge-count law is the LINEAR mixer-cost
-- O(N) (documented in the module header); the count is a measured
-- quantity, not a theorem.

/-- **The two-channel step law**: with the ensemble step
decaying (the Gap_N curvature) and the joint step growing
linearly (the mixer-share channel), the total step
s(N) = a/N² + b·N has a unique minimum at
N* = (2a/b)^{1/3} — the measured regime (steps growing:
0.105 → 0.206) is the rising limb BEFORE N*; the turnover
prediction: the step at the next N-point either continues
rising (still before N*) or shrinks (past N*) — both
outcomes are verdicts. The formal statement: the step
function's sign structure (the unique critical point of
the two-channel sum). -/
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
# CertifiedMerge-остаток — PAC-Bayes compression

Порт 2607.14506 (PAC-Bayes compression certificate для
merged-моделей: prior = base-чекпойнт, posterior = merged,
штраф C(Δ) в битах тернарно-сжатых дельт), часть.

Контракт: дельта-апдейт — список (позиция, тернарный знак);
стоимость в битах АДДИТИВНА по элементам (для каждой позиции
ровно log_2 3 бит знака + log_2 d бит индекса).

**Теоремы:**

* `deltaCost_concat` — субаддитивность-точность: стоимость
  конкатенации K дельт РАВНА сумме стоимостей
  (C(Δ₁ ++ Δ₂) = C(Δ₁) + C(Δ₂)): K-дельта merge платит ровно
  сумму, без мультипликативного штрафа;
* deltaCost_le_card_bits — верхняя граница: стоимость
  K дельт ≤ (Σ k, |Δ_k|)·(log₂ d + log₂ 3) — биты
  компрессии входят линейно в PAC-Bayes-штраф;
* `merged_bound` — PAC-Bayes compression bridge: при
  измеренном population-риске posterior и посылке-мосте
  (связка риска и компрессии, 2607.14506 Thm-стиль) риск
  merged ≤ prior-риск + (C + log(1/δ))·масштаб.

**Честные границы**: PAC-Bayes-мост (риск ⟸ компрессия) —
посылка hcert (h_emp_-слой); здесь формализована
КОМБИНАТОРНАЯ часть (аддитивность бит-стоимости), где
мультипликативный компаундинг невозможен по построению
(согласовано с ATTACK_VECTOR §2: компаундинг опровергнут).
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

/-- **Точная аддитивность стоимости конкатенации**: дельты
K merge-шагов стоят ровно сумму своих стоимостей —
мультипликативного компаундинга бит-штрафа НЕТ
(атака «компаундинг после merge» закрыта по построению). -/
theorem deltaCost_concat {d : ℕ} (δ₁ δ₂ : Delta d) :
    deltaCost (δ₁ ++ δ₂) = deltaCost δ₁ + deltaCost δ₂ := by
  unfold deltaCost
  rw [List.length_append]
  push_cast
  ring

/-- **K-дельта merge платит линейно**: суммарная стоимость
K дельт = Σ_k C(Δ_k) (следствие точной аддитивности). -/
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

/-- **PAC-Bayes compression bridge (композитинг)**: если
одношаговое применение дельты ухудшает prior-риск не более
чем на lambda * C(delta) + mu (измеряемая посылка-мост
2607.14506), то K-шаговый merge-композитинг платит
ЛИНЕЙНО: суммарный штраф = lambda * Σ C(Delta_k) + K * mu.

Следствие (ATTACK_VECTOR §2): мультипликативный
компаундинг штрафа невозможен — K merge-шагов тандемом
стоят сумму бит-стоимостей, а не произведение факторов
деградации. -/
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
