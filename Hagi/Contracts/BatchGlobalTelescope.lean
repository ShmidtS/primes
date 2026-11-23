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

end Hagi.Contracts.BatchGlobalTelescope
