import Hagi.Contracts.BatchCETrajectory.FixedBatch
import Hagi.Probability.EmpiricalBernstein
import Hagi.Probability.Azuma


/-!
# BatchGlobalTelescope — от per-batch certified drop к глобальному objective

Три уровня (C647, разбор негатива `batch_drop_not_global`):

- (A) batch = весь датасет ⇒ batch-objective и есть глобальный
  objective; телескоп уже дан `Hagi.Theory.MasterTheoremV3.master_theorem_v3`
  (клоз 3, абстракция над `step`) и `fixedBatchObjective_sum_certifiedDrop_le_telescope`.
- (B) фиксированный batch: certified drops телескопируют в
  batch-objective (`batch_telescope_fixed`, `fixedBatch_telescope`), но
  глобальный objective контролируется только вероятностно —
  `batch_drop_generalizes` через эмпирический Bernstein
  (`empirical_bernstein_mean_bound`): среднее по iid-выборке отклоняется
  от среднего по распределению не более чем на зазор; посылки —
  диапазон `b` и дисперсия `sig` per-sample приращений.
  Композиция с certified drop — `certified_batch_drop_global`.
- (C) случайный batch на каждом шаге: без модели батчей не
  формализуется; сводится к (B) + union bound по шагам (здесь НЕ делается).

Код-факт (HAGI_v2 @ca52eb4, hagi/lm.py `train_guarded`, refine-фаза,
lm.py:978-1005): `rng.choice(..., size=min(64, N), replace=False)` — до 64
позиций БЕЗ возвращения; далее 8 раундов `rng.permutation`, срезы по 32;
каждый `_certified_finite_step(bx, by)` сертифицирует CE своего
минибатча, принимается любой `d > 0`, ledger = сумма per-batch (`"scope":
"per-batch-sum, no telescoping guarantee"`). Это не (A) и не чистый (B):
iid-модель ниже — КОНСЕРВАТИВНАЯ ИДЕАЛИЗАЦИЯ выборки без возвращения.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchGlobalTelescope

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
  Hagi.Contracts.BatchCEStep Hagi.Contracts.BatchCETrajectory Hagi.Probability

/-- Абстрактный телескоп по ОДНОМУ objective: если каждый шаг `t < T`
уменьшает `f` минимум на `d t`, итог не превышает старт минус сумма
certified drops. -/
theorem batch_telescope_fixed (f d : ℕ → ℝ) (T : ℕ)
    (hstep : ∀ t < T, f (t + 1) ≤ f t - d t) :
    f T + ∑ t ∈ Finset.range T, d t ≤ f 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 : f (T + 1) + ∑ t ∈ Finset.range (T + 1), d t
          ≤ f T + ∑ t ∈ Finset.range T, d t := by
        rw [Finset.sum_range_succ]
        linarith [hstep T (Nat.lt_succ_self T)]
      linarith [ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))]

/-- Специализация на фиксированный batch: certified drops вдоль
`fixedBatchState` телескопируют в batch-objective (нижний bound
`fixedBatchObjective_sum_certifiedDrop_le_telescope`, переписанный как
«финал ≤ старт − сумма»). -/
theorem fixedBatch_telescope {V : Type} [Fintype V] [Nonempty V]
    {B n a r c k : ℕ}
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    fixedBatchObjective X y S opCost opRisk write T ≤
      batchCEObjective X y S -
        ∑ t ∈ Finset.range T, batchCertifiedDrop X
          (coreParameters (fixedBatchState X y S opCost opRisk write t)) y := by
  have h := fixedBatchObjective_sum_certifiedDrop_le_telescope X y S opCost opRisk write T
  linarith

/-- Зазор эмпирического Bernstein между средним по iid-выборке объёма `n`
и средним по распределению. -/
noncomputable def ebGap (b sig : ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ))
    + 2 * b * Real.log (2 / alpha) / (n : ℝ)

/-- Приращение мартингалы Эб-Бернштейна: «последний сэмпл префикса минус
среднее по `q`»; на пустом префиксе — 0. -/
noncomputable def centeredSample {V : Type} [Fintype V] (q δ : V → ℝ) (t : ℕ)
    (pref : Fin t → V) : ℝ :=
  match t with
  | 0 => 0
  | t + 1 => δ (pref (Fin.last t)) - ∑ v, q v * δ v

/-- На `Fin.snoc` берётся ровно последний (новый) сэмпл. -/
theorem centeredSample_snoc {V : Type} [Fintype V] (q δ : V → ℝ) (t : ℕ)
    (pref : Fin t → V) (v : V) :
    centeredSample q δ (t + 1) (Fin.snoc pref v)
      = δ v - ∑ v, q v * δ v := by
  change δ (Fin.snoc (α := fun _ => V) pref v (Fin.last t)) - ∑ v, q v * δ v = _
  rw [Fin.snoc_last]

/-- `azumaSum` по `centeredSample` — это сумма сэмплов минус `n`-кратное
среднее по `q`. -/
theorem azumaSum_centeredSample {V : Type} [Fintype V] (q δ : V → ℝ) (n : ℕ)
    (ω : Fin n → V) :
    azumaSum (centeredSample q δ) n ω =
      (∑ i : Fin n, δ (ω i)) - (n : ℝ) * ∑ v, q v * δ v := by
  induction n with
  | zero => simp [azumaSum]
  | succ n ih =>
      change azumaSum (centeredSample q δ) n (fun i => ω i.castSucc)
          + centeredSample q δ (n + 1) ω = _
      rw [ih]
      show _ + (δ (ω (Fin.last n)) - ∑ v, q v * δ v) = _
      rw [Fin.sum_univ_castSucc]
      have hbeta : (∑ i : Fin n, δ ((fun i : Fin n => ω i.castSucc) i))
          = ∑ i : Fin n, δ (ω i.castSucc) := Finset.sum_congr rfl (fun i _ => rfl)
      rw [hbeta]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- **(batch_drop_generalizes)**: `δ v` — per-sample приращение loss на
сэмпле `v` (θ' против θ), `∑ v, q v * δ v` — его среднее по
распределению `q`, то есть глобальный рост objective. Для iid-выборки
объёма `n` с вероятностью ≥ `1 − alpha` среднее приращение по выборке
не превосходит глобальное больше чем на `ebGap b sig n alpha`. Посылки:
диапазон `|δ v − среднее| ≤ b`, взвешенная дисперсия `≤ sig`, `sig > 0`. -/
theorem batch_drop_generalizes {V : Type} [Fintype V] [Nonempty V] (q δ : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ v, |δ v - ∑ v, q v * δ v| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hvar : ∑ v, q v * (δ v - ∑ v, q v * δ v) ^ 2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun ω => (∑ i : Fin n, δ (ω i)) / (n : ℝ) <
        (∑ v, q v * δ v) + ebGap b sig n alpha) := by
  classical
  have hmean : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * centeredSample q δ (t + 1)
          (Fin.snoc (α := fun _ => V) pref v) = 0 := by
    intro t pref
    simp only [centeredSample_snoc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1]
    simp
  have hbnd' : ∀ (t : ℕ) (pref : Fin t → V), |centeredSample q δ t pref| ≤ b := by
    intro t pref
    cases t with
    | zero => simp only [centeredSample, abs_zero, hb]
    | succ t =>
        show |δ (pref (Fin.last t)) - ∑ v, q v * δ v| ≤ b
        exact hbnd _
  have hvar' : ∀ (t : ℕ) (pref : Fin t → V),
      ∑ v, q v * (centeredSample q δ (t + 1)
        (Fin.snoc (α := fun _ => V) pref v)) ^ 2 ≤ sig := by
    intro t pref
    simp only [centeredSample_snoc]
    exact hvar
  have h := empirical_bernstein_mean_bound q hq0 hq1 (centeredSample q δ)
    b hb hbnd' sig hsig hmean hvar' n hn alpha halpha1 halpha2
  refine le_trans h (prodPq_mono (fun _ : Fin n => q) (fun _ => ⟨hq0, hq1⟩) _ _ ?_)
  intro ω hω
  rw [azumaSum_centeredSample q δ n ω] at hω
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : (∑ i : Fin n, δ (ω i)) - (n : ℝ) * ∑ v, q v * δ v
      < ebGap b sig n alpha * (n : ℝ) := by
    obtain ⟨_, h2⟩ := (abs_lt).mp hω
    exact (div_lt_iff₀ hn').1 h2
  have hgap : ebGap b sig n alpha * (n : ℝ)
      = Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ)) * (n : ℝ)
        + 2 * b * Real.log (2 / alpha) := by
    unfold ebGap
    field_simp
  rw [hgap] at h2
  refine (div_lt_iff₀ hn').2 ?_
  linarith

/-- **(certified_batch_drop_global)**: композиция уровня (B). `loss v θ` —
loss на сэмпле `v`, глобальный objective — его среднее по `q`. Если
per-sample приращения ограничены по диапазону и дисперсии, то с
вероятностью ≥ `1 − alpha` КАЖДОГО сэмпла, на котором certified drop
`dropB` не превосходит фактического drop по выборке, верно
`obj_G θ' ≤ obj_G θ − dropB + ebGap`. Условие «certified ≤ фактического
по выборке» даётся per-batch леммой (`batchCertifiedDrop_le_actualDrop`);
вероятность — только над сэмплом, не над параметрами. -/
theorem certified_batch_drop_global {V : Type} [Fintype V] [Nonempty V] {Θ : Type}
    (q : V → ℝ) (loss : V → Θ → ℝ) (θ θ' : Θ) (dropB : ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (b : ℝ) (hb : 0 ≤ b)
    (hbnd : ∀ v, |loss v θ' - loss v θ - ∑ v, q v * (loss v θ' - loss v θ)| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hvar : ∑ v, q v * ((loss v θ' - loss v θ) - ∑ v, q v * (loss v θ' - loss v θ)) ^ 2 ≤ sig)
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun (ω : Fin n → V) => dropB ≤ (∑ i : Fin n, (loss (ω i) θ - loss (ω i) θ')) / (n : ℝ) →
        ∑ v, q v * loss v θ' ≤ ∑ v, q v * loss v θ - dropB + ebGap b sig n alpha) := by
  classical
  set G : ℝ := ∑ v, q v * (loss v θ' - loss v θ) with hGdef
  have hGneg : ∀ v : V, q v * (loss v θ - loss v θ') = -(q v * (loss v θ' - loss v θ)) := by
    intro v; ring
  have hGnegS : ∑ v, q v * (loss v θ - loss v θ') = -G := by
    rw [hGdef, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun v _ => hGneg v)
  have hbnd' : ∀ v, |loss v θ - loss v θ' - -G| ≤ b := by
    intro v
    have hpt : loss v θ - loss v θ' - -G = -(loss v θ' - loss v θ - G) := by ring
    rw [hpt, abs_neg]
    exact hbnd v
  have hvar' : ∑ v, q v * (loss v θ - loss v θ' - -G) ^ 2 ≤ sig := by
    have heq : (∑ v, q v * (loss v θ - loss v θ' - -G) ^ 2)
        = ∑ v, q v * (loss v θ' - loss v θ - G) ^ 2 :=
      Finset.sum_congr rfl (fun v _ => by ring)
    rw [heq]
    exact hvar
  have hbnd'' : ∀ v, |loss v θ - loss v θ' - ∑ v, q v * (loss v θ - loss v θ')| ≤ b := by
    intro v
    rw [hGnegS]
    exact hbnd' v
  have hvar'' : ∑ v, q v * (loss v θ - loss v θ'
      - ∑ v, q v * (loss v θ - loss v θ')) ^ 2 ≤ sig := by
    rw [hGnegS]
    exact hvar'
  have h := batch_drop_generalizes q (fun v => loss v θ - loss v θ') hq0 hq1 b hb hbnd''
    sig hsig hvar'' n hn alpha halpha1 halpha2
  refine le_trans h (prodPq_mono (fun _ : Fin n => q) (fun _ => ⟨hq0, hq1⟩) _ _ ?_)
  intro ω hω hdrop
  rw [hGnegS] at hω
  have hlt : dropB < -G + ebGap b sig n alpha := lt_of_le_of_lt hdrop hω
  have hobj : ∑ v, q v * loss v θ' - ∑ v, q v * loss v θ = G := by
    rw [hGdef]
    simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-! ### Уровень (C): k независимых раундов, union bound + телескоп -/

/-- Плотность одного раунда: iid-выборка объёма `n` из `q`. -/
noncomputable def roundDens {V : Type} (q : V → ℝ) {n : ℕ} (ω : Fin n → V) : ℝ :=
  ∏ i, q (ω i)

/-- Мера на `k` независимых раундов: координата `i` — плотность раунда
`ω i`. Это и есть гипотеза-модель «раунды независимы». -/
noncomputable def roundP {V : Type} (q : V → ℝ) {n k : ℕ} (_i : Fin k)
    (ω : Fin n → V) : ℝ := roundDens q ω

theorem roundP_isProb {V : Type} [Fintype V] [Nonempty V] {n k : ℕ} (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    IsProbSys (roundP q (n := n) (k := k)) := by
  intro i
  constructor
  · intro ω
    show (0 : ℝ) ≤ roundDens q ω
    unfold roundDens
    exact Finset.prod_nonneg fun j _ => hq0 _
  · show (∑ ω : Fin n → V, roundDens q ω) = 1
    unfold roundDens
    rw [sum_prod_factor]
    exact Finset.prod_eq_one fun _ _ => hq1

/-- Маргинал раунда `i` под произведением мер равен мере одного раунда. -/
theorem round_marginal {V : Type} [Fintype V] [Nonempty V] {n k : ℕ} (q : V → ℝ)
    (hq1 : ∑ v, q v = 1) (i : Fin k)
    (A : (Fin n → V) → Prop) [DecidablePred A] :
    prodPq (roundP q (n := n) (k := k)) (fun ω => A (ω i)) = prodPq (fun _ => q) A := by
  classical
  have hL : prodPq (roundP q (n := n) (k := k)) (fun ω => A (ω i))
      = ∑ Ω : Fin k → Fin n → V, ∏ j, prodDens (fun _ => q) (Ω j)
          * (if j = i then (if A (Ω j) then (1:ℝ) else 0) else 1) := by
    unfold prodPq prodE
    refine Finset.sum_congr rfl fun Ω _ => ?_
    show (prodDens (roundP q) Ω * (if A (Ω i) then (1:ℝ) else 0)) = _
    have h1 : prodDens (roundP (V := V) q (n := n) (k := k)) Ω
        = ∏ j, prodDens (fun _ => q) (Ω j) := rfl
    rw [h1]
    symm
    rw [Finset.prod_mul_distrib]
    have hsingle : (∏ j : Fin k, if j = i then (if A (Ω j) then (1:ℝ) else 0) else 1)
        = if A (Ω i) then (1:ℝ) else 0 := by
      have hs := Finset.prod_eq_single
        (f := fun j => if j = i then (if A (Ω j) then (1:ℝ) else 0) else 1) i
        (fun j _ hj => by rw [if_neg hj])
        (fun h => absurd (Finset.mem_univ i) h)
      rw [if_pos rfl] at hs
      exact hs
    rw [hsingle]
  rw [hL, sum_prod_factor (n := k) (V := Fin n → V)
    (f := fun j (x : Fin n → V) =>
      prodDens (fun _ => q) x * (if j = i then (if A x then (1:ℝ) else 0) else 1))]
  have hsingle2 : (∏ j : Fin k, ∑ x : Fin n → V,
      prodDens (fun _ => q) x * (if j = i then (if A x then (1:ℝ) else 0) else 1))
      = ∑ x : Fin n → V, prodDens (fun _ => q) x * (if A x then (1:ℝ) else 0) := by
    simpa using Finset.prod_eq_single
      (f := fun j => ∑ x : Fin n → V,
        prodDens (fun _ => q) x * (if j = i then (if A x then (1:ℝ) else 0) else 1)) i
      (fun j _ hj => by
        simp only [hj, ite_false, mul_one]
        show (∑ x : Fin n → V, ∏ l, q (x l)) = 1
        rw [sum_prod_factor]
        exact Finset.prod_eq_one fun _ _ => hq1)
      (fun h => absurd (Finset.mem_univ i) h)
  rw [hsingle2]
  unfold prodPq prodE
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- **(rounds_union)**: union bound по `k` независимым раундам. Если
событие `A i` (утверждение о выборке раунда `i`) имеет вероятность
≥ `1 − eps i`, то все `A i` вместе — вероятность ≥ `1 − ∑ eps`
(`prodPq_union_finset` + `round_marginal`). -/
theorem rounds_union {V : Type} [Fintype V] [Nonempty V] {n k : ℕ} (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (A : Fin k → (Fin n → V) → Prop) [∀ i, DecidablePred (A i)]
    (eps : Fin k → ℝ)
    (hA : ∀ i, 1 - eps i ≤ prodPq (fun _ => q) (A i)) :
    1 - ∑ i, eps i ≤
      prodPq (roundP q (n := n) (k := k)) (fun ω => ∀ i, A i (ω i)) := by
  classical
  have hp := roundP_isProb q hq0 hq1 (n := n) (k := k)
  have hu : prodPq (roundP q (n := n) (k := k)) (fun ω => ∃ i, ¬ A i (ω i))
      ≤ ∑ i, prodPq (roundP q (n := n) (k := k)) (fun ω => ¬ A i (ω i)) := by
    have h := prodPq_union_finset _ hp Finset.univ (fun i ω => ¬ A i (ω i))
    simpa only [Finset.mem_univ, exists_prop, true_and] using h
  have hqp : IsProbSys (fun (_ : Fin n) => q) := fun _ => ⟨fun v => hq0 v, hq1⟩
  have hm : ∀ i, prodPq (roundP q (n := n) (k := k)) (fun ω => ¬ A i (ω i))
      = 1 - prodPq (fun _ => q) (A i) := by
    intro i
    rw [round_marginal q hq1 i (fun ω => ¬ A i ω), prodPq_compl (fun _ : Fin n => q) hqp (A i)]
  rw [Finset.sum_congr rfl (fun i _ => hm i)] at hu
  have hc := prodPq_compl _ hp (fun ω => ∀ i, A i (ω i))
  have hsplit : prodPq (roundP q (n := n) (k := k)) (fun ω => ∀ i, A i (ω i))
      = 1 - prodPq (roundP q (n := n) (k := k)) (fun ω => ∃ i, ¬ A i (ω i)) := by
    have hle : prodPq (roundP q (n := n) (k := k)) (fun ω => ∃ i, ¬ A i (ω i))
        ≤ prodPq (roundP q (n := n) (k := k)) (fun ω => ¬ ∀ i, A i (ω i)) :=
      prodPq_mono _ hp _ _ (fun ω hω => by
        simp only [not_forall]
        exact hω)
    have hge : prodPq (roundP q (n := n) (k := k)) (fun ω => ¬ ∀ i, A i (ω i))
        ≤ prodPq (roundP q (n := n) (k := k)) (fun ω => ∃ i, ¬ A i (ω i)) :=
      prodPq_mono _ hp _ _ (fun ω hω => by
        simp only [not_forall] at hω
        exact hω)
    linarith
  rw [hsplit]
  have hsum : (∑ i, ((1 : ℝ) - prodPq (fun _ => q) (A i))) ≤ ∑ i, eps i :=
    Finset.sum_le_sum fun i _ => by linarith [hA i]
  linarith

/-- Телескоп по `k` раундам: если каждый раунд даёт
`obj (i+1) ≤ obj i − dropB i + g`, то
`obj k ≤ obj 0 − ∑ dropB + k·g` (из `batch_telescope_fixed`). -/
theorem rounds_telescope (obj : ℕ → ℝ) (dropB : ℕ → ℝ) (g : ℝ) (k : ℕ)
    (hstep : ∀ i < k, obj (i + 1) ≤ obj i - dropB i + g) :
    obj k ≤ obj 0 - ∑ i ∈ Finset.range k, dropB i + k * g := by
  have h := batch_telescope_fixed obj (fun i => dropB i - g) k (fun i hi => by
    have := hstep i hi
    linarith)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range] at h
  linarith

/-- «Хороший» раунд `i`: как только certified drop `dropB i` не превосходит
фактического drop по выборке раунда, глобальный objective (среднее `loss`
по `q`) падает минимум на `dropB i − g`. -/
@[reducible] def roundGood {V : Type} [Fintype V] (q : V → ℝ) (loss : V → ℕ → ℝ)
    (dropB : ℕ → ℝ) (g : ℝ) {n : ℕ} (i : ℕ) (ω : Fin n → V) : Prop :=
  dropB i ≤ (∑ j, (loss (ω j) i - loss (ω j) (i + 1))) / (n : ℝ) →
    (∑ v, q v * loss v (i + 1)) ≤ (∑ v, q v * loss v i) - dropB i + g

/-- **(certified_rounds_union)**: композиция уровня (C). `loss v t` — loss
на сэмпле `v` после `t` раундов, `dropB i` — certified drop раунда `i`;
на раунд берётся зазор `ebGap` при уровне `alpha / k`. В модели независимых
раундов с вероятностью ≥ `1 − alpha` КАЖДЫЙ раунд хороший (стоит на выборке
раунда), и тогда при выполнении в каждом раунде посылки «certified ≤
фактического drop по выборке» глобальный objective телескопирует:
`obj k ≤ obj 0 − ∑ dropB + k·ebGap` — суммарный certified drop ослабляется
на `k` зазоров. Посылки — те же, что в `certified_batch_drop_global`, для
каждого раунда. -/
theorem certified_rounds_union {V : Type} [Fintype V] [Nonempty V]
    (q : V → ℝ) (loss : V → ℕ → ℝ) (dropB : ℕ → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (b : ℝ) (hb : 0 ≤ b)
    (hbnd : ∀ (i : ℕ) (v : V), |loss v (i + 1) - loss v i
      - ∑ v, q v * (loss v (i + 1) - loss v i)| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hvar : ∀ i : ℕ, ∑ v, q v * ((loss v (i + 1) - loss v i)
      - ∑ v, q v * (loss v (i + 1) - loss v i)) ^ 2 ≤ sig)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (alpha : ℝ)
    (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (roundP q (n := n) (k := k))
      (fun Ω => (∀ i : Fin k, roundGood q loss dropB (ebGap b sig n (alpha / k)) i (Ω i)) ∧
        ((∀ i : Fin k, dropB i ≤ (∑ j, (loss (Ω i j) i - loss (Ω i j) (i + 1))) / (n : ℝ)) →
          (∑ v, q v * loss v k) ≤ (∑ v, q v * loss v 0)
            - (∑ i ∈ Finset.range k, dropB i) + k * ebGap b sig n (alpha / k))) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hper : ∀ i : Fin k, 1 - alpha / k ≤ prodPq (fun _ : Fin n => q)
      (roundGood q loss dropB (ebGap b sig n (alpha / k)) (n := n) (i : ℕ)) :=
    fun i => by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_le_of_lt hk
      have h := @certified_batch_drop_global V _ _ Bool q
        (fun v t => loss v (if t then (i : ℕ) + 1 else i)) false true
        (dropB i) hq0 hq1 b hb (by simpa using hbnd i) sig hsig (by simpa using hvar i)
        n hn (alpha / k) (div_pos halpha1 hkR)
        (by rw [div_lt_one hkR]; exact lt_of_lt_of_le halpha2 hk1)
      have h' : 1 - alpha / k ≤ prodPq (fun _ => q)
          (fun ω : Fin n → V => dropB ↑i ≤ (∑ j, (loss (ω j) ↑i - loss (ω j) (↑i + 1))) / (n : ℝ) →
            (∑ v, q v * loss v (↑i + 1)) ≤ (∑ v, q v * loss v ↑i) - dropB ↑i
              + ebGap b sig n (alpha / k)) := h
      exact h'
  have hu := rounds_union q hq0 hq1
    (fun (i : Fin k) => roundGood q loss dropB (ebGap b sig n (alpha / k)) (i : ℕ))
    (fun _ => alpha / k) hper
  have hkR0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hk
  have hsum : (∑ _i : Fin k, alpha / (k : ℝ)) = alpha := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum] at hu
  refine le_trans hu (prodPq_mono _ (roundP_isProb q hq0 hq1) _ _ (fun Ω hΩ => ⟨hΩ, ?_⟩))
  intro hd
  exact rounds_telescope (fun t => ∑ v, q v * loss v t) dropB _ k
    (fun i hi => hΩ ⟨i, hi⟩ (hd ⟨i, hi⟩))

end Hagi.Contracts.BatchGlobalTelescope
