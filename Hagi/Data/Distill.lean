/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.Info

set_option linter.style.header false

/-!
# Distill: the exact CE/KL identities of the distillation axis

 honesty fix: `crossEntropy` now carries the standard
minus sign (CE_q(p) = −Σ q log p), `klDiv` is defined as
Σ q log(q/p), and the two identities are proved against
these REAL definitions (the pre- versions were trivial
algebra on a signless pseudo-CE).

**The exact identities (THEOREMS):**

* `kl_eq_ce_gap` — KL(q‖p) = CE_q(p) − CE_q(q) for
  positive distributions: the divergence is the excess
  cross-entropy over the entropy baseline.

* `ce_gap_kl_identity` — THE master identity: for any data
  distribution q and models p_E, p_θ:

`CE_q(p_θ) − CE_q(p_E) = KL(q‖p_θ) − KL(q‖p_E)` —

  the CE gap IS the KL gap against the DATA distribution;
  the data q appears irreducibly (the naive bound
  CE_θ ≤ CE_ens + KL(p_E‖p_θ) is FALSE in general — hard
  labels do not transmit the teacher's calibration).

* `teacher_generated_identity` — THE distillation theorem:
  when the targets ARE the teacher's distribution (q = p_E,
  the soft-target protocol):

`CE_{p_E}(p_θ) = H(p_E) + KL(p_E‖p_θ)` —

  the student's soft-target CE is the teacher's entropy plus
  the teacher-student divergence; the distillable gap is
  EXACTLY the divergence.

**The expressivity hypothesis (not a theorem).** Whether an
H=384 student can drive E[KL(p_E‖p_θ)] ≤ δ is the open
expressivity question (round 22 P4): recorded as the
explicit hypothesis DistillExpressivity(H, δ) with the
practical go/no-go — the distill run's plateau behavior
(KL plateau vs continued descent).

**Prescription for the code.**

1. The distillation objective is the soft-target CE
   (q = p_E): minimize KL(p_E‖p_θ) — the identity certifies
   this is EXACTLY the distillable gap.
2. The stopping rule: both plateaus (KL and held-out CE)
   checked separately.
3. The verdict telemetry: E[KL(p_E‖p_θ)] per checkpoint +
   exact held-out CE; a high KL plateau is the expressivity
   wall — record REFUTED honestly.
-/

open Finset

namespace Hagi.Data

section Distill

variable {V : Type*} [Fintype V]

/-- The cross-entropy of model p against distribution q:
CE_q(p) = −Σ q log p (the standard sign — fix). -/
noncomputable def crossEntropy (q p : V → ℝ) : ℝ :=
  -∑ v, q v * Real.log (p v)

/-- The Kullback–Leibler divergence KL(q‖p) = Σ q log(q/p)
(the real definition — fix). -/
noncomputable def klDiv (q p : V → ℝ) : ℝ :=
  --: = Prelude.klDef (kept under the historical name)
  Hagi.Prelude.klDef q p

/-- **KL is the excess cross-entropy** over the entropy
baseline: KL(q‖p) = CE_q(p) − CE_q(q) for strictly positive
distributions (q a distribution, p positive). -/
theorem kl_eq_ce_gap (q p : V → ℝ) (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    klDiv q p = crossEntropy q p - crossEntropy q q := by
  unfold klDiv crossEntropy Hagi.Prelude.klDef
  have hsplit : ∀ v : V, q v * Real.log (q v / p v)
      = q v * Real.log (q v) - q v * Real.log (p v) := by
    intro v
    rw [Real.log_div (hq v).ne' (hp v).ne']
    ring
  rw [show ∑ v, q v * Real.log (q v / p v)
      = ∑ v, (q v * Real.log (q v) - q v * Real.log (p v)) from
      Finset.sum_congr rfl (fun v _ => hsplit v)]
  rw [show ∑ v : V, (q v * Real.log (q v) - q v * Real.log (p v))
      = (∑ v : V, q v * Real.log (q v)) - (∑ v : V, q v * Real.log (p v)) from
      sum_sub_distrib (fun v : V => q v * Real.log (q v))
        (fun v : V => q v * Real.log (p v))]
  ring

/-- **The master identity (theorem, real version).**
For any data distribution q and models p_E, p_θ (all
positive):

`CE_q(p_θ) − CE_q(p_E) = KL(q‖p_θ) − KL(q‖p_E)` —

the CE gap IS the KL gap against the data; q is
irreducible. The naive hard-label bound is FALSE in general
(hard labels do not carry the teacher's calibration) — this
identity is the honest replacement. -/
theorem ce_gap_kl_identity (q pE pTheta : V → ℝ)
    (hq : ∀ v, 0 < q v) (hpE : ∀ v, 0 < pE v) (hpT : ∀ v, 0 < pTheta v) :
    crossEntropy q pTheta - crossEntropy q pE
      = klDiv q pTheta - klDiv q pE := by
  rw [kl_eq_ce_gap q pTheta hq hpT, kl_eq_ce_gap q pE hq hpE]
  ring

/-- **The teacher-generated distillation identity
(theorem, real version).** When the targets are the
teacher's own distribution (the soft-target protocol,
q = p_E):

`CE_{p_E}(p_θ) = CE_{p_E}(p_E) + KL(p_E‖p_θ)` —

CE_{p_E}(p_E) is the teacher's entropy H(p_E): the
student's soft CE is the teacher's entropy plus the
teacher-student divergence — the distillable gap is EXACTLY
the divergence. -/
theorem teacher_generated_identity (pE pTheta : V → ℝ)
    (hpE : ∀ v, 0 < pE v) (hpT : ∀ v, 0 < pTheta v) :
    crossEntropy pE pTheta = crossEntropy pE pE + klDiv pE pTheta := by
  rw [kl_eq_ce_gap pE pTheta hpE hpT]
  ring

variable [DecidableEq V]

/-- Top-K усечение распределения на S с перенормировкой
удержанной массой Z > 0. -/
noncomputable def truncNorm (p : V → ℝ) (S : Finset V) (Z : ℝ)
    (v : V) : ℝ := if v ∈ S then p v / Z else 0

/-- Точная формула смещения кросс-энтропии при Top-K
усечении учителя: если носители q, p лежат в S (p > 0 на S)
и q — вероятностное распределение, то
CE(q, p|_S/Z) = CE(q, p) + log Z — усечение смещает
функционал дистилляции ровно на логарифм удержанной массы
(log Z ≤ 0 при Z ≤ 1): меньше K — ниже CE на носителе,
но уже область применимости. -/
theorem ce_topk_shift (q p : V → ℝ) (S : Finset V)
    (hq : ∀ v ∉ S, q v = 0) (hpOut : ∀ v ∉ S, p v = 0)
    (hpos : ∀ v ∈ S, 0 < p v)
    (hq1 : ∑ v, q v = 1) (hZ : 0 < Z) :
    crossEntropy q (truncNorm p S Z)
      = crossEntropy q p + Real.log Z := by
  -- масса q на S равна 1
  have hqS : ∑ v ∈ S, q v = 1 := by
    have hcompl : ∑ v ∈ Sᶜ, q v = 0 :=
      Finset.sum_eq_zero fun v hv => hq v (Finset.mem_compl.mp hv)
    have hsplit := Finset.sum_add_sum_compl S q
    rw [hq1, hcompl, add_zero] at hsplit
    exact hsplit
  -- члены вне S обнуляются с обеих сторон
  have hqout : ∀ v, v ∉ S → q v * Real.log (truncNorm p S Z v) = 0 := by
    intro v hv
    have hz : truncNorm p S Z v = 0 := by simp [truncNorm, hv]
    rw [hz, Real.log_zero, mul_zero]
  have hpout' : ∀ v, v ∉ S → q v * Real.log (p v) = 0 := by
    intro v hv
    rw [hq v hv, zero_mul]
  -- редукция сумм к S
  have hL : ∑ v, q v * Real.log (truncNorm p S Z v)
      = ∑ v ∈ S, q v * Real.log (p v / Z) := by
    have hsum : ∑ v ∈ S, q v * Real.log (truncNorm p S Z v)
        = ∑ v, q v * Real.log (truncNorm p S Z v) :=
      Finset.sum_subset (Finset.subset_univ S)
        (fun v _ hv => hqout v hv)
    rw [← hsum]
    exact Finset.sum_congr rfl fun v hv => by simp [truncNorm, hv]
  have hR : ∑ v, q v * Real.log (p v) = ∑ v ∈ S, q v * Real.log (p v) :=
    (Finset.sum_subset (Finset.subset_univ S)
      (fun v _ hv => hpout' v hv)).symm
  -- разложение логарифма отношения на S
  have hlog : ∀ v, v ∈ S →
      Real.log (p v / Z) = Real.log (p v) - Real.log Z := fun v hv =>
    Real.log_div (ne_of_gt (hpos v hv)) (ne_of_gt hZ)
  -- финальная перегруппировка
  unfold crossEntropy
  rw [hL, hR]
  have hsplit : ∑ v ∈ S, q v * Real.log (p v / Z)
      = (∑ v ∈ S, q v * Real.log (p v)) - (∑ v ∈ S, q v) * Real.log Z := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hlog v hv]
    ring
  rw [hsplit, hqS]
  ring

/-- KL-версия формулы Top-K: усечение учителя до S с
перенормировкой смещает KL-дивергенцию ученика к учителю
ровно на log Z — Top-K-дистилляция не добавляет скрытых
штрафов сверх явной цены усечения хвоста. -/
theorem kl_topk_shift (q p : V → ℝ) (S : Finset V) (Z : ℝ)
    (hq : ∀ v ∉ S, q v = 0)
    (hqS : ∑ v ∈ S, q v = 1) (hZ : 0 < Z)
    (hqpos : ∀ v ∈ S, 0 < q v) (hppos : ∀ v ∈ S, 0 < p v) :
    klDiv q (truncNorm p S Z) = klDiv q p + Real.log Z := by
  -- члены вне S нулевые с обеих сторон (q v = 0)
  have hqout : ∀ v, v ∉ S →
      q v * Real.log (q v / truncNorm p S Z v) = 0 := by
    intro v hv
    rw [hq v hv, zero_mul]
  have hqout' : ∀ v, v ∉ S → q v * Real.log (q v / p v) = 0 := by
    intro v hv
    rw [hq v hv, zero_mul]
  -- редукция обеих сумм к S
  have hL : ∑ v, q v * Real.log (q v / truncNorm p S Z v)
      = ∑ v ∈ S, q v * Real.log (Z * q v / p v) := by
    have hsum : ∑ v ∈ S, q v * Real.log (q v / truncNorm p S Z v)
        = ∑ v, q v * Real.log (q v / truncNorm p S Z v) :=
      Finset.sum_subset (Finset.subset_univ S)
        (fun v _ hv => hqout v hv)
    rw [← hsum]
    refine Finset.sum_congr rfl fun v hv => ?_
    have htz : truncNorm p S Z v = p v / Z := by simp [truncNorm, hv]
    rw [htz]
    congr 1
    field_simp
  have hR : ∑ v, q v * Real.log (q v / p v)
      = ∑ v ∈ S, q v * Real.log (q v / p v) :=
    (Finset.sum_subset (Finset.subset_univ S)
      (fun v _ hv => hqout' v hv)).symm
  unfold klDiv Hagi.Prelude.klDef
  rw [hL, hR]
  have hlog : ∀ v, v ∈ S →
      Real.log (Z * q v / p v) = Real.log (q v / p v) + Real.log Z := by
    intro v hv
    have h1 : Z * q v / p v = (q v / p v) * Z := by field_simp
    rw [h1, Real.log_mul (ne_of_gt (div_pos (hqpos v hv) (hppos v hv)))
      (ne_of_gt hZ)]
  have hsplit : ∀ v, v ∈ S → q v * Real.log (Z * q v / p v)
      = q v * Real.log (q v / p v) + q v * Real.log Z := by
    intro v hv
    rw [hlog v hv]
    ring
  calc ∑ v ∈ S, q v * Real.log (Z * q v / p v)
      = ∑ v ∈ S, (q v * Real.log (q v / p v)
          + q v * Real.log Z) :=
        Finset.sum_congr rfl hsplit
    _ = (∑ v ∈ S, q v * Real.log (q v / p v))
          + ∑ v ∈ S, q v * Real.log Z := by exact Finset.sum_add_distrib
    _ = (∑ v ∈ S, q v * Real.log (q v / p v))
          + (∑ v ∈ S, q v) * Real.log Z := by rw [Finset.sum_mul]
    _ = (∑ v ∈ S, q v * Real.log (q v / p v)) + Real.log Z := by
        rw [hqS, one_mul]

/-- Передача бюджета Top-K-дистилляции: если удержанная
масса учителя Z ≥ exp(−β) (хвост дешевле β в лог-метрике)
и ученик достиг KL ≤ α против УСЕЧЁННОГО учителя, то его
KL против ПОЛНОГО учителя ≤ α + β — смещение усечения
входит в бюджет дистилляции аддитивно и контролируется
порогом удержанной массы. -/
theorem topk_distill_budget (q p : V → ℝ) (S : Finset V) (Z : ℝ)
    (hq : ∀ v ∉ S, q v = 0)
    (hqS : ∑ v ∈ S, q v = 1) (hZ0 : 0 < Z)
    (hqpos : ∀ v ∈ S, 0 < q v) (hppos : ∀ v ∈ S, 0 < p v)
    (α β : ℝ) (hβ : 0 ≤ β)
    (hZ : Real.exp (-β) ≤ Z)
    (hstudent : klDiv q (truncNorm p S Z) ≤ α) :
    klDiv q p ≤ α + β := by
  have hshift := kl_topk_shift q p S Z hq hqS hZ0 hqpos hppos
  -- log Z ≥ −β из Z ≥ e^(−β)
  have hlogZ : -β ≤ Real.log Z := by
    have h1 := Real.log_le_log (Real.exp_pos (-β)) hZ
    rw [Real.log_exp] at h1
    exact h1
  linarith

/-- Логарифмическая цена усечения в линейных единицах:
−log Z ≤ (1−Z)/Z для 0 < Z ≤ 1 (log x ≤ x−1 при x = 1/Z). -/
theorem topk_tail_bound (Z : ℝ) (hZ0 : 0 < Z) (hZ1 : Z ≤ 1) :
    -Real.log Z ≤ (1 - Z) / Z := by
  have hinvpos : (0:ℝ) < 1 / Z := div_pos one_pos hZ0
  have hlog := Real.log_le_sub_one_of_pos hinvpos
  rw [Real.log_div one_ne_zero (ne_of_gt hZ0), Real.log_one, zero_sub] at hlog
  rw [le_div_iff₀ hZ0]
  have hkey : (1 / Z - 1) * Z = 1 - Z := by field_simp
  have hlog' : -Real.log Z * Z ≤ (1 / Z - 1) * Z :=
    mul_le_mul_of_nonneg_right hlog (le_of_lt hZ0)
  rw [hkey] at hlog'
  linarith

/-- Бюджет Top-K-дистилляции в линейных единицах хвоста:
если удержанная масса Z ∈ (0,1] и ученик достиг KL ≤ α
против усечённого учителя, то KL против полного ≤
α + (1−Z)/Z — порог допуска выражается относительной
массой хвоста без логарифмов. -/
theorem topk_distill_budget_tv (q p : V → ℝ) (S : Finset V) (Z : ℝ)
    (hq : ∀ v ∉ S, q v = 0)
    (hqS : ∑ v ∈ S, q v = 1) (hZ0 : 0 < Z) (hZ1 : Z ≤ 1)
    (hqpos : ∀ v ∈ S, 0 < q v) (hppos : ∀ v ∈ S, 0 < p v)
    (α : ℝ)
    (hstudent : klDiv q (truncNorm p S Z) ≤ α) :
    klDiv q p ≤ α + (1 - Z) / Z := by
  have hexp : Real.exp (-((1 - Z) / Z)) ≤ Z := by
    have h1 := topk_tail_bound Z hZ0 hZ1
    -- −log Z ≤ (1−Z)/Z ⟹ exp(−(1−Z)/Z) ≤ exp(log Z) = Z
    have h3 : -((1 - Z) / Z) ≤ Real.log Z := neg_le.mp h1
    have h2 : Real.exp (-((1 - Z) / Z)) ≤ Real.exp (Real.log Z) :=
      Real.exp_le_exp.mpr h3
    rwa [Real.exp_log hZ0] at h2
  exact topk_distill_budget q p S Z hq hqS hZ0 hqpos hppos α
    ((1 - Z) / Z) (div_nonneg (sub_nonneg.mpr hZ1) (le_of_lt hZ0))
    hexp hstudent

variable {V : Type*} [Fintype V] [Nonempty V]

omit [Nonempty V] in
/-- Хвостовая масса Гиббса за энергетическим зазором: суммарный
вес состояний с L > m + s экспоненциально мал по s/T. -/
theorem gibbs_tail_mass (L : V → ℝ) (m T s : ℝ) (hT : 0 < T)
    (hm : ∀ v, m ≤ L v) :
    ∑ v ∈ Finset.univ.filter (fun v => m + s < L v),
        Real.exp (-(L v / T))
      ≤ (Fintype.card V : ℝ) * Real.exp (-((m + s) / T)) := by
  have hkey : ∀ v ∈ Finset.univ.filter (fun v => m + s < L v),
      Real.exp (-(L v / T)) ≤ Real.exp (-((m + s) / T)) := by
    intro v hv
    have hv' : m + s < L v := by simpa using hv
    have hdiv : (m + s) / T ≤ L v / T := by
      rw [div_le_div_iff₀ hT hT]
      nlinarith [hv', hT]
    have : -(L v / T) ≤ -((m + s) / T) := by linarith
    exact Real.exp_le_exp.mpr this
  calc ∑ v ∈ Finset.univ.filter (fun v => m + s < L v),
        Real.exp (-(L v / T))
      ≤ ∑ v ∈ Finset.univ.filter (fun v => m + s < L v),
          Real.exp (-((m + s) / T)) := Finset.sum_le_sum hkey
    _ = (Finset.univ.filter (fun v => m + s < L v)).card •
          Real.exp (-((m + s) / T)) := Finset.sum_const _
    _ ≤ (Fintype.card V : ℝ) * Real.exp (-((m + s) / T)) := by
        have hcard : ((Finset.univ.filter (fun v => m + s < L v)).card : ℝ)
            ≤ (Fintype.card V : ℝ) := by
          exact_mod_cast Finset.card_filter_le Finset.univ
            (fun v => m + s < L v)
        have hexp : (0:ℝ) ≤ Real.exp (-((m + s) / T)) := Real.exp_nonneg _
        rw [nsmul_eq_mul]
        calc ((Finset.univ.filter (fun v => m + s < L v)).card : ℝ)
              * Real.exp (-((m + s) / T))
            ≤ (Fintype.card V : ℝ) * Real.exp (-((m + s) / T)) :=
              mul_le_mul_of_nonneg_right hcard hexp

/-- Термодинамическое затухание смещения Top-K: при
температуре T и зазоре s (n·e^{-s/T} < 1) смещение
усечения Гиббс-учителя до низкоэнергетического
множества {L ≤ m+s} ограничено (n·e^{-s/T})/(1−n·e^{-s/T})
— при T → 0 цена усечения Top-K-дистилляции обнуляется:
охлаждение учителя автоматически восстанавливает
допустимость. -/
theorem cooling_topk_bias (L : V → ℝ) (m T s : ℝ) (hT : 0 < T)
    (hm : ∀ v, m ≤ L v) (hm0 : ∃ v0 : V, L v0 = m)
    (hsep : (Fintype.card V : ℝ) * Real.exp (-(s / T)) < 1) :
    -Real.log (1 - (∑ v ∈ Finset.univ.filter (fun v => m + s < L v),
            Real.exp (-(L v / T)))
        / (∑ v, Real.exp (-(L v / T))))
      ≤ ((Fintype.card V : ℝ) * Real.exp (-(s / T)))
        / (1 - (Fintype.card V : ℝ) * Real.exp (-(s / T))) := by
  set n := (Fintype.card V : ℝ) with hn
  set r := n * Real.exp (-(s / T)) with hr
  set tail := ∑ v ∈ Finset.univ.filter (fun v => m + s < L v),
      Real.exp (-(L v / T)) with htail
  set total := ∑ v, Real.exp (-(L v / T)) with htotal
  obtain ⟨v0, hv0⟩ := hm0
  have htotalm : Real.exp (-(m / T)) ≤ total := by
    have h1 := Finset.single_le_sum (f := fun v => Real.exp (-(L v / T)))
      (fun v _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ v0)
    rw [hv0] at h1
    exact h1
  have htaille := gibbs_tail_mass L m T s hT hm
  have hrdiv : tail / total ≤ r := by
    have hBpos : (0:ℝ) < Real.exp (-(m / T)) := Real.exp_pos _
    have hNnn : (0:ℝ) ≤ n * Real.exp (-((m + s) / T)) :=
      mul_nonneg (by exact_mod_cast Nat.cast_nonneg _) (Real.exp_nonneg _)
    have h1 : tail / total
        ≤ (n * Real.exp (-((m + s) / T))) / Real.exp (-(m / T)) := by
      rw [div_le_div_iff₀ (Finset.sum_pos
        (fun v _ => Real.exp_pos _) (Finset.univ_nonempty)) hBpos]
      exact mul_le_mul htaille htotalm (le_of_lt hBpos) hNnn
    have h2 : (n * Real.exp (-((m + s) / T))) / Real.exp (-(m / T)) = r := by
      have hexp1 : Real.exp (-((m + s) / T)) = Real.exp (-(m / T))
          * Real.exp (-(s / T)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp1, mul_div_assoc,
        mul_comm (Real.exp (-(m / T))) (Real.exp (-(s / T))),
        mul_div_cancel_right₀ _ (ne_of_gt hBpos), hr]
    exact le_trans h1 (h2 ▸ le_refl r)
  have htotalpos : 0 < total := Finset.sum_pos
    (fun v _ => Real.exp_pos _) (Finset.univ_nonempty)
  have htailnn : 0 ≤ tail := Finset.sum_nonneg
    (fun v _ => le_of_lt (Real.exp_pos _))
  have hZ1 : 1 - tail / total ≤ 1 := by
    have : 0 ≤ tail / total := div_nonneg htailnn (le_of_lt htotalpos)
    linarith
  have hZ0 : 0 < 1 - tail / total := by
    have hle : tail / total ≤ r := hrdiv
    rw [hr] at hle
    linarith
  have hmain := topk_tail_bound (1 - tail / total) hZ0 hZ1
  have hmono : (1 - (1 - tail / total)) / (1 - tail / total)
      ≤ r / (1 - r) := by
    have hr1 : r < 1 := by rw [hr] at hsep; linarith
    rw [div_le_div_iff₀ hZ0 (by linarith)]
    nlinarith [hrdiv]
  rw [hr] at hmono
  linarith


end Distill

end Hagi.Data

namespace Hagi
export Hagi.Data (crossEntropy klDiv kl_eq_ce_gap ce_gap_kl_identity teacher_generated_identity)
end Hagi
