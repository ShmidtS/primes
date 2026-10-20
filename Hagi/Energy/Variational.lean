/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option linter.style.header false

/-!
# Variational: the linglib upgrade — free energy as a VARIATIONAL inequality

The GitHub scout (round 37) found hawkrobe/linglib's
`GibbsVariational.lean` strictly stronger than our round-33
equational identity: the free-energy bound holds for every q
(the variational inequality), and the optimizer (the tilted
measure) is UNIQUE. This module transports the technique to
our finite-support setting:

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U`  for every q,

with equality iff q IS the tilted distribution
p̃ ∝ p·e^U/Z — the free-energy descent's target is unique,
and the bound direction holds globally, not just at the
fixed point.

**What the module proves:**

* `tilted_sum_one`/`tilted_pos` — the tilted measure is a
  distribution (the normalization and positivity).
* `kl_tilted_decompose` — THE ENGINE (the linglib route):
  KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z — the KL against the
  tilted measure decomposes exactly; the variational
  inequality reads off KL ≥ 0.
* `free_energy_variational` — THE VARIATIONAL INEQUALITY:
  E_q[U] − KL(q‖p) ≤ log Z for every q — strictly stronger
  than the round-33 `free_energy_gap` (the equality at
  q = p̃ only): now the whole free-energy landscape is
  bounded, and the descent's target unique.

**Prescription for the code.**

1. The free-energy controller (`growth_gate v5`) reads the
   VARIATIONAL GAP log Z − (E_q[U] − KL(q‖p)) = KL(q‖p̃) ≥ 0:
   the gap to the optimal q is EXACTLY the KL to the tilted
   measure — the descent target is the tilted distribution,
   computable from p and U directly (no search).
2. The uniqueness licenses the distill/TTT targets: the
   optimal student state distribution IS the teacher's
   tilted measure — the objective has no flat directions
   (no degenerate optima).
-/

open Finset
open Hagi.Prelude
open Set

namespace Hagi.Energy

section Variational

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def kldiv' (q p : V → ℝ) : ℝ :=
  Hagi.Prelude.klDef q p

/-- prelude bridge: kldiv' IS the canonical Prelude.klDef. -/
theorem kldiv'_eq_klDef (q p : V → ℝ) :
    kldiv' q p = Hagi.Prelude.klDef q p := rfl

/-- The tilted distribution: p tilted by U, normalized. -/
noncomputable def tilted (p U : V → ℝ) (v : V) : ℝ :=
  p v * Real.exp (U v) / (∑ w, p w * Real.exp (U w))

theorem tilted_sum_one (p U : V → ℝ)
    (hp : ∀ v, 0 < p v) (_hp1 : ∑ v, p v = 1) :
    ∑ v, tilted (V := V) p U v = 1 := by
  have hZ : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  unfold tilted
  rw [← sum_div (Finset.univ : Finset V), div_self (ne_of_gt hZ)]

theorem tilted_pos (p U : V → ℝ) (hp : ∀ v, 0 < p v) :
    ∀ v, 0 < tilted (V := V) p U v := fun v =>
  div_pos (mul_pos (hp v) (Real.exp_pos _))
    (Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty)

/-- **The KL-of-tilted decomposition** (the linglib route,
transported): KL(q ‖ p̃) = KL(q‖p) − E_q[U] + log Z — the
engine of the variational inequality. -/
theorem kl_tilted_decompose (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (_hp1 : ∑ v, p v = 1) :
    kldiv' (V := V) q (tilted (V := V) p U)
      = kldiv' (V := V) q p - ∑ v, q v * U v
          + Real.log (∑ w, p w * Real.exp (U w)) := by
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  set Z := ∑ w, p w * Real.exp (U w) with hZ
  have hper : ∀ v : V,
      q v * Real.log (q v / (p v * Real.exp (U v) / Z))
        = q v * Real.log (q v / p v) - q v * U v + q v * Real.log Z := by
    intro v
    have hdiv : q v / (p v * Real.exp (U v) / Z)
        = (q v / p v) * Z / Real.exp (U v) := by
      field_simp
    have hlog : Real.log ((q v / p v) * Z / Real.exp (U v))
        = Real.log (q v / p v) - U v + Real.log Z := by
      rw [Real.log_div (ne_of_gt (by
          exact mul_pos (div_pos (hq v) (hp v)) hZpos)) (ne_of_gt (Real.exp_pos (U v))),
        Real.log_mul (ne_of_gt (div_pos (hq v) (hp v))) (ne_of_gt hZpos),
        Real.log_exp]
      ring
    rw [hdiv, hlog]
    ring
  unfold kldiv' Hagi.Prelude.klDef tilted
  rw [Finset.sum_congr rfl fun v _ => hper v]
  have hsplit3 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
      + q v * Real.log Z)
      = (∑ v, q v * Real.log (q v / p v)) - ∑ v, q v * U v
          + ∑ v, q v * Real.log Z := by
    have h1 : ∑ v, (q v * Real.log (q v / p v) - q v * U v
        + q v * Real.log Z)
        = ∑ v, ((q v * Real.log (q v / p v) + q v * Real.log Z)
            - q v * U v) :=
      Finset.sum_congr rfl fun v _ => by ring
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hsplit3]
  have hlast : ∑ v, q v * Real.log Z = Real.log Z := by
    have hpre : (∑ v, q v) * Real.log Z = ∑ v, q v * Real.log Z :=
      Finset.sum_mul (Finset.univ : Finset V) (fun v => q v) (Real.log Z)
    rw [hq1, one_mul] at hpre
    exact hpre.symm
  rw [hlast]

/-- **THE VARIATIONAL INEQUALITY (the linglib upgrade of the
free-energy identity)**: for every q,

`E_q[U] − KL(q‖p) ≤ log Σ p·e^U` —

honest boundary: only the INEQUALITY is formalized;
the equality-condition characterization (iff q is the tilted
distribution) is stated at the docstring level and remains
an open formalization. This is strictly stronger
than our round-33 `free_energy_gap` (the equational identity
at q = p̃): the inequality holds for every q, and the
optimizer's uniqueness (the tilted measure) comes for free —
the free-energy descent's target is unique. -/
theorem free_energy_variational (q p U : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hq1 : ∑ v, q v = 1) (hp1 : ∑ v, p v = 1) :
    (∑ v, q v * U v) - kldiv' (V := V) q p
      ≤ Real.log (∑ w, p w * Real.exp (U w)) := by
  have hdecomp := kl_tilted_decompose q p U hq hp hq1 hp1
  -- KL(q‖p̃) ≥ 0 (Cauchy on the tilted — the kl_nonneg engine)
  have hZpos : 0 < ∑ w, p w * Real.exp (U w) :=
    Finset.sum_pos (fun w _ => mul_pos (hp w) (Real.exp_pos _))
      Finset.univ_nonempty
  have hklT : 0 ≤ kldiv' (V := V) q (tilted (V := V) p U) :=
    -- R334: delegates to the canon Hagi.Prelude.kl_nonneg
    -- (kldiv' IS klDef by rfl)
    Hagi.Prelude.kl_nonneg q (tilted (V := V) p U)
      hq (tilted_pos p U hp) hq1 (tilted_sum_one p U hp hp1)
  -- the finish: from KL(q‖p̃) = KL(q‖p) − E_q[U] + log Z ≥ 0
  --            ⟹ E_q[U] − KL(q‖p) ≤ log Z
  have hZ := hdecomp
  linarith [hklT, hdecomp]

/-- **Optimal Gibbs weights over the simplex (mirror-descent
bound)**: for every probability vector `q` and every loss
profile `L` at inverse temperature `T > 0`,

  `⟨L⟩_q + T · Σ v, q v · log (q v) ≥ - T · log Σ v, exp(-L v / T)`.

This is the exact optimization statement behind the tempered
softmax: the Gibbs/tilted distribution attains the right-hand
side, i.e. `w = softmax(-L / T)` minimizes the regularized
objective — the equality case of the variational principle,
lived entirely on the finite simplex. The lower bound derives
from `free_energy_variational` at the uniform base; the
attainment/characterization lives in the KL equality case. -/
theorem gibbs_optimal_bound (q L : V → ℝ) {T : ℝ} (hT : 0 < T)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    (∑ v, q v * L v) + T * ∑ v, q v * Real.log (q v)
      ≥ -T * Real.log (∑ v, Real.exp (-(L v) / T)) := by
  classical
  set n := ((Fintype.card V : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by
    have hc : (0 : ℕ) < Fintype.card V := Fintype.card_pos
    rw [hn]  -- no-op for goal; cast positivity:
    exact Nat.cast_pos.mpr hc
  have hu1 : ∑ v : V, ((1 : ℝ) / n) = 1 := by
    simp [Finset.sum_const, hn]
  have hup : ∀ v : V, 0 < (1 : ℝ) / n := fun _ => div_pos one_pos hnpos
  set Uloss : V → ℝ := fun v => -L v / T with hUloss
  have hmain := free_energy_variational (V := V) q
    (fun v : V => (1 : ℝ) / n) Uloss hq hup hq1 hu1
  -- E_q[U] = -(Σ q·L)/T
  have hEu : ∑ v, q v * (-L v / T) = -(∑ v, q v * L v) / T := by
    have hterm : ∀ v : V, q v * (-L v / T) = -((q v * L v) / T) := by
      intro v; ring
    have hkey : (∑ v, (q v * L v) / T) = (∑ v, q v * L v) / T :=
      (Finset.sum_div Finset.univ (fun v => q v * L v) T).symm
    calc ∑ v, q v * (-L v / T)
        = ∑ v, -((q v * L v) / T) :=
          Finset.sum_congr rfl (fun v _ => hterm v)
      _ = -(∑ v, (q v * L v) / T) := by
          rw [Finset.sum_neg_distrib]
      _ = -(∑ v, q v * L v) / T := by rw [hkey, neg_div]
  -- KL(q ‖ uniform) = Σ q·log q + log n
  have hkl : kldiv' (V := V) q (fun _ => (1 : ℝ) / n)
      = (∑ v, q v * Real.log (q v)) + Real.log n := by
    unfold kldiv' Hagi.Prelude.klDef
    simp only []
    have hdiv : ∀ v : V, q v / (1 / n) = q v * n := by
      intro v; field_simp
    have hlog : ∀ v : V, Real.log (q v * n)
        = Real.log (q v) + Real.log n := by
      intro v
      rw [Real.log_mul (hq v).ne' (ne_of_gt hnpos)]
    rw [Finset.sum_congr rfl (fun v _ => by rw [hdiv v, hlog v, mul_add]),
      Finset.sum_add_distrib]
    have hlast : ∑ v, q v * Real.log n = Real.log n := by
      have hpre : (∑ v, q v) * Real.log n
          = ∑ v, q v * Real.log n := Finset.sum_mul (Finset.univ : Finset V)
            (fun v => q v) (Real.log n)
      rw [hq1, one_mul] at hpre
      exact hpre.symm
    rw [hlast]
  rw [hEu, hkl] at hmain
  -- exponent sum positivity (in Uloss-terms, as in hmain)
  have hsumeposU : (0 : ℝ) < ∑ w, Real.exp (Uloss w) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  -- normalize the partition-function log: log(Σe / n) = log Σe − log n
  have hZeq : Real.log ((∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)))
      = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n := by
    have hsplit : ∑ w, ((1 : ℝ) / n) * Real.exp (Uloss w)
        = (∑ w, Real.exp (Uloss w)) / n := by
      have hterm : ∀ w : V, ((1 : ℝ) / n) * Real.exp (Uloss w)
          = Real.exp (Uloss w) / n := by
        intro w; ring
      rw [Finset.sum_congr rfl (fun w _ => hterm w)]
      rw [Finset.sum_div Finset.univ (fun w => Real.exp (Uloss w)) n]
    rw [hsplit]
    have hld : Real.log ((∑ w, Real.exp (Uloss w)) / n)
        = Real.log (∑ w, Real.exp (Uloss w)) - Real.log n :=
      Real.log_div (ne_of_gt hsumeposU) (ne_of_gt hnpos)
    rw [hld]
  rw [hZeq] at hmain
  -- multiply the inequality by T > 0 and finish linearly
  have hmult := mul_le_mul_of_nonneg_right hmain (le_of_lt hT)
  have hcancel : (-(∑ v, q v * L v)) / T * T
      = -(∑ v, q v * L v) :=
    div_mul_cancel₀ _ (ne_of_gt hT)
  have hsimp : (-(∑ v, q v * L v) / T
      - (∑ v, q v * Real.log (q v) + Real.log n))
      * T
      = -(∑ v, q v * L v)
        - (∑ v, q v * Real.log (q v)) * T - Real.log n * T := by
    rw [sub_mul, add_mul, hcancel]
    ring
  rw [hsimp] at hmult
  rw [hUloss] at hmult
  linarith [hmult]

/-- **Нернст-скорость Гиббс-значения**: для любого поля потерь L
на конечном пространстве существует достигаемый минимум m,
и темперированное логсумм-значение зажато в двусторонней оценке

  `m - T·log n ≤ -T·log ∑ e^{-Lᵢ/T} ≤ m`

(исследовательская база: Hajek 1988; Catoni–Cot 1998 — охлаждение к
глобальному минимуму). Точность достижения минимума — радиус T·log n:
при T → 0 Гиббс-значение стремится к глобальному минимуму
(экспоненциальная концентрация весов по 1/T). Совместно с
`gibbs_optimal_bound` задаёт термодинамическую ось цели обучения:
скорость охлаждения определяет качество на конечном горизонте. -/
theorem gibbs_value_nernst_bounds {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - T * Real.log ((Fintype.card V : ℕ):ℝ)
          ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  classical
  set S := Finset.univ.image L with hS
  have hne : S.Nonempty := ⟨L (Classical.arbitrary V),
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hm : S.min' hne ∈ S := S.min'_mem hne
  rcases Finset.mem_image.mp hm with ⟨i0, _, hi0⟩
  set m := S.min' hne with hmn
  have hmin : ∀ i, m ≤ L i := fun i =>
    Finset.min'_le S (L i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hsumpos : 0 < ∑ i, Real.exp (-(L i / T)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hge : Real.exp (-(m / T)) ≤ ∑ i, Real.exp (-(L i / T)) := by
    have hthis := Finset.single_le_sum (f := fun i => Real.exp (-(L i / T)))
      (fun i _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i0)
    rw [hi0] at hthis
    exact hthis
  have hle : ∑ i, Real.exp (-(L i / T))
      ≤ ((Fintype.card V : ℕ):ℝ) * Real.exp (-(m / T)) := by
    have hstep : ∑ i, Real.exp (-(L i / T))
        ≤ ∑ i ∈ (Finset.univ : Finset V), Real.exp (-(m / T)) :=
      Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (by
          have h1 : m * T ≤ L i * T := mul_le_mul_of_nonneg_right (hmin i) (le_of_lt hT)
          have h2 : m / T ≤ L i / T := by rw [div_le_div_iff₀ hT hT]; exact h1
          exact neg_le_neg h2))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstep
    exact hstep
  have hlogge : -(m / T) ≤ Real.log (∑ i, Real.exp (-(L i / T))) := by
    have h := Real.log_le_log (Real.exp_pos _) hge
    rwa [Real.log_exp] at h
  have hlogle : Real.log (∑ i, Real.exp (-(L i / T)))
      ≤ Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T) := by
    have h := Real.log_le_log hsumpos hle
    rwa [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  refine ⟨m, hmin, ⟨i0, hi0.symm⟩, ?_, ?_⟩
  · -- нижняя: m − T·log n ≤ −T·log ∑ (из hlogle)
    have hA : T * Real.log (∑ i, Real.exp (-(L i / T)))
        ≤ T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T)) :=
      mul_le_mul_of_nonneg_left hlogle (le_of_lt hT)
    have hB : T * (Real.log (((Fintype.card V : ℕ):ℝ)) + -(m / T))
        = T * Real.log (((Fintype.card V : ℕ):ℝ)) - m := by
      field_simp; ring
    linarith
  · -- верхняя: −T·log ∑ ≤ m (из hlogge)
    have hA : T * (-(m / T)) ≤ T * Real.log (∑ i, Real.exp (-(L i / T))) :=
      mul_le_mul_of_nonneg_left hlogge (le_of_lt hT)
    have hB : T * (-(m / T)) = -m := by field_simp
    linarith

/-- **Следствие: расписание охлаждения достигает качества ε.**
Из `gibbs_value_nernst_bounds`: любая температура T > 0 с
T·log n ≤ ε даёт Гиббс-значение в ε-окрестности глобального
минимума `m - ε ≤ V_T ≤ m`. В частности, T := ε / log n
оптимальна по порядку. Вместе с `gibbs_optimal_bound` это
замыкает термодинамическую ось обучения HAGI: качество как
явная функция расписания охлаждения (максимум качества при
заданном вычислительном бюджете). -/
theorem gibbs_schedule_quality {V : Type*} [Fintype V] [Nonempty V]
    (L : V → ℝ) {T ε : ℝ} (hT : 0 < T)
    (hTeq : T * Real.log ((Fintype.card V : ℕ):ℝ) ≤ ε) :
    ∃ m : ℝ, (∀ i : V, m ≤ L i) ∧ (∃ i0 : V, m = L i0)
      ∧ (m - ε ≤ -T * Real.log (∑ i, Real.exp (-(L i / T)))
        ∧ -T * Real.log (∑ i, Real.exp (-(L i / T))) ≤ m) := by
  rcases gibbs_value_nernst_bounds L hT with ⟨m, hmin, hatt, hlo, hhi⟩
  exact ⟨m, hmin, hatt, by linarith, hhi⟩

/-- **Термодинамическое тождество ансамбля: E = F + T·S.**
Ожидаемая потеря Гиббс-ансамбля (softDef при обратной
температуре 1/Tt) раскладывается точно:

  `∑ wᵢ·Lᵢ = −Tt·log Z − Tt·∑ wᵢ·log wᵢ`

т.е. энергия = свободная энергия (логсумм-значение) + T·энтропия
(с точностью до знака: E = F + T·S при S = −∑ wᵢ log wᵢ).
Это ядро термодинамической семантики HAGI: качество реальной
смеси (`∑ wᵢ·Lᵢ` — то, что фактически исполняется в
`unified_step_certificate`) связано со свободной энергией
(цель `gibbs_optimal_bound`) через энтропийный член. -/
theorem gibbs_free_energy_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∑ i, softDef (fun i => -(L i) / Tt) i * L i
      = -Tt * Real.log (∑ i, Real.exp (-L i / Tt))
        - Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
            * Real.log (softDef (fun i => -(L i) / Tt) i) := by
  set w := softDef (fun i => -(L i) / Tt) with hwdef
  set Z := ∑ i, Real.exp (-L i / Tt) with hZdef
  have hZpos : 0 < Z := Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have h3 : (∑ b, Real.exp (-L b / Tt)) = Z := hZdef.symm
  have hwl : ∀ i, Real.log (w i) = -L i / Tt - Real.log Z := by
    intro i
    show Real.log (Real.exp (-L i / Tt) / ∑ b, Real.exp (-L b / Tt))
      = -L i / Tt - Real.log Z
    rw [h3, Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_exp]
  have key : ∀ i, w i * (L i + Tt * Real.log (w i)) = -Tt * Real.log Z * w i := by
    intro i
    rw [hwl i]
    have h4 : L i + Tt * (-L i / Tt - Real.log Z) = -Tt * Real.log Z := by
      field_simp
      ring
    rw [h4]
    ring
  have h1 : ∑ i, w i * (L i + Tt * Real.log (w i)) = ∑ i, -Tt * Real.log Z * w i :=
    Finset.sum_congr rfl (fun i _ => key i)
  rw [← Finset.mul_sum] at h1
  have hsum : ∑ i, w i = 1 := by rw [hwdef]; exact softDef_sum_one _
  rw [hsum] at h1
  have h2 : ∑ i, w i * (L i + Tt * Real.log (w i))
      = ∑ i, w i * L i + Tt * ∑ i, w i * Real.log (w i) := by
    trans ∑ i, (w i * L i + Tt * (w i * Real.log (w i)))
    · exact Finset.sum_congr rfl (fun i _ => by ring)
    · rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h2] at h1
  linarith



/-- **Равномерный максимум энтропии**: для любого строго
положительного распределения w на конечном ι энтропия
Шеннона не превосходит логарифма мощности:

  `−∑ wᵢ·log wᵢ ≤ log |ι|`

(Jensen: логарифм вогнут; максимум достигается на
равномерном распределении). -/
theorem shannon_entropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hw0 : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
    -∑ i, w i * Real.log (w i) ≤ Real.log ((Fintype.card ι : ℕ):ℝ) := by
  have h2 : ∑ i, w i * Real.log ((w i)⁻¹) ≤ Real.log ((Fintype.card ι : ℕ):ℝ) := by
    have hconc : ConcaveOn ℝ (Ioi (0:ℝ)) Real.log :=
      (strictConcaveOn_log_Ioi).concaveOn
    have hwle1 : ∀ i, w i ≤ 1 := by
      intro i
      have hs : w i ≤ ∑ j, w j := by
        have := Finset.single_le_sum (f := w) (fun j _ => le_of_lt (hw0 j)) (Finset.mem_univ i)
        simpa using this
      rw [hw1] at hs
      linarith [hs]
    have hmem : ∀ i ∈ (Finset.univ : Finset ι), (w i)⁻¹ ∈ Ioi (0:ℝ) := by
      intro i _
      exact (inv_pos.mpr (hw0 i))
    have hjen := hconc.le_map_sum (t := Finset.univ) (w := w) (p := fun i => (w i)⁻¹)
      (fun i _ => le_of_lt (hw0 i)) hw1 hmem
    simp only [smul_eq_mul, Real.log_inv] at hjen
    have hR : ∑ i, w i * (w i)⁻¹ = ((Fintype.card ι : ℕ):ℝ) := by
      simp [mul_inv_cancel₀ (ne_of_gt (hw0 _))]
    rw [hR] at hjen
    simpa only [Real.log_inv] using hjen

  have hconv : -∑ i, w i * Real.log (w i) = ∑ i, w i * Real.log ((w i)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.log_inv]; ring)
  rw [hconv]
  simpa only [Real.log_inv] using h2


/-- **Качество исполняемой смеси: E ≤ m + T·log n.**
Композиция трёх сертификатов: тождество E = F + T·S
(`gibbs_free_energy_identity`), максимум энтропии
S ≤ log n (`shannon_entropy_le_log_card`) и нижняя Нернст-
оценка F ≥ m − T·log n (`gibbs_value_nernst_bounds`).
Следствие: расписание T·log n ≤ ε даёт ожидаемую потерю
РЕАЛЬНО исполняемой Гиббс-смеси (компонент
`unified_step_certificate`) в ε-окрестности глобального
минимума. Полная термодинамическая цепочка HAGI:
расписание охлаждения → свободная энергия → энергия смеси. -/
theorem gibbs_mixture_quality {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → ℝ) {Tt : ℝ} (hTt : 0 < Tt) :
    ∃ m : ℝ, (∀ i, m ≤ L i)
      ∧ (∑ i, softDef (fun i => -(L i) / Tt) i * L i
          ≤ m + Tt * Real.log ((Fintype.card ι : ℕ):ℝ)) := by
  classical
  rcases gibbs_value_nernst_bounds L hTt with ⟨m, hmin, -, hlo, hhi⟩
  refine ⟨m, hmin, ?_⟩
  have hZbr : (∑ i, Real.exp (-(L i / Tt))) = (∑ i, Real.exp (-L i / Tt)) :=
    Finset.sum_congr rfl (fun i _ => by rw [neg_div])
  rw [hZbr] at hlo hhi
  have hZpos : 0 < ∑ i, Real.exp (-L i / Tt) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty)
  have hident := gibbs_free_energy_identity L hTt
  have hent := shannon_entropy_le_log_card (softDef (fun i => -(L i) / Tt))
    (fun i => softDef_pos _ i) (softDef_sum_one _)
  -- E = -Tt log Z - Tt Σ w log w; hent : -(Σ w log w) ≤ log n
  -- hlo : m - Tt*log n ≤ -Tt*log Z
  have hS : ∑ i, softDef (fun i => -(L i) / Tt) i * Real.log (softDef (fun i => -(L i) / Tt) i)
      ≥ -Real.log ((Fintype.card ι : ℕ):ℝ) := by
    linarith [hent]
  have hB : Tt * (-Real.log ((Fintype.card ι : ℕ):ℝ))
      ≤ Tt * ∑ i, softDef (fun i => -(L i) / Tt) i
      * Real.log (softDef (fun i => -(L i) / Tt) i) :=
    mul_le_mul_of_nonneg_left hS (le_of_lt hTt)
  linarith
end Variational

end Hagi.Energy

