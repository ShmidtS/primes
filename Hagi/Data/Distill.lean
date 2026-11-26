/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Info.InfoCore
import Hagi.Data.DField

set_option linter.style.header false

/-!
# Distill: the exact CE/KL identities of the distillation axis

`crossEntropy` carries the standard minus sign
(CE_q(p) = −Σ q log p), `klDiv` is Σ q log(q/p); both
identities are proved against these definitions.

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
expressivity question, recorded as the
explicit hypothesis DistillExpressivity(H, δ) with the
practical go/no-go — the distill run's plateau behavior
(KL plateau vs continued descent).

**Prescription for the code.**

1. The distillation objective is the soft-target CE
   (q = p_E): minimize KL(p_E‖p_θ) — exactly the distillable gap.
2. The verdict telemetry: E[KL(p_E‖p_θ)] per checkpoint +
   exact held-out CE; a high KL plateau is the expressivity
   wall — record REFUTED honestly.
-/

open Finset

namespace Hagi.Data

section Distill

variable {V : Type*} [Fintype V]

/-- The cross-entropy of model p against distribution q:
CE_q(p) = −Σ q log p — canonical delegation to `Hagi.Prelude.ceDef`. -/
noncomputable def crossEntropy (q p : V → ℝ) : ℝ :=
  Hagi.Prelude.ceDef q p

/-- Bridge: `crossEntropy` IS the canonical `ceDef`. -/
theorem crossEntropy_eq_ceDef (q p : V → ℝ) :
    crossEntropy q p = Hagi.Prelude.ceDef q p := rfl


set_option linter.unusedVariables false in
/-- **KL is the excess cross-entropy** over the entropy
baseline: KL(q‖p) = CE_q(p) − CE_q(q) for strictly positive
distributions (q a distribution, p positive). -/
theorem kl_eq_ce_gap (q p : V → ℝ) (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    Hagi.Prelude.klDef q p = crossEntropy q p - crossEntropy q q :=
  Hagi.Prelude.klDef_eq_ceDef_sub q p (fun v => (hp v).ne')

/-- **The master identity.**
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
      = Hagi.Prelude.klDef q pTheta - Hagi.Prelude.klDef q pE := by
  rw [kl_eq_ce_gap q pTheta hq hpT, kl_eq_ce_gap q pE hq hpE]
  ring

/-- **The teacher-generated distillation identity.** When the
teacher's own distribution (the soft-target protocol,
q = p_E):

`CE_{p_E}(p_θ) = CE_{p_E}(p_E) + KL(p_E‖p_θ)` —

CE_{p_E}(p_E) is the teacher's entropy H(p_E): the
student's soft CE is the teacher's entropy plus the
teacher-student divergence — the distillable gap is EXACTLY
the divergence. -/
theorem teacher_generated_identity (pE pTheta : V → ℝ)
    (hpE : ∀ v, 0 < pE v) (hpT : ∀ v, 0 < pTheta v) :
    crossEntropy pE pTheta = crossEntropy pE pE + Hagi.Prelude.klDef pE pTheta := by
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
  unfold crossEntropy Hagi.Prelude.ceDef
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
    Hagi.Prelude.klDef q (truncNorm p S Z) = Hagi.Prelude.klDef q p + Real.log Z := by
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
  simp only [Hagi.Prelude.klDef]
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
    (hstudent : Hagi.Prelude.klDef q (truncNorm p S Z) ≤ α) :
    Hagi.Prelude.klDef q p ≤ α + β := by
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
    (hstudent : Hagi.Prelude.klDef q (truncNorm p S Z) ≤ α) :
    Hagi.Prelude.klDef q p ≤ α + (1 - Z) / Z := by
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
export Hagi.Data (crossEntropy teacher_generated_identity)
end Hagi

set_option linter.style.header false

/-!
# Recursive self-distillation: the entropy floor of model collapse

The conditional core of the model-collapse /
entropy-preservation theorem.

**The setting.** Recursive self-distillation across generations:
generation k+1 trains toward the target mixture

`m_k = (1−ν)·p_k + ν·p_data` —

the previous model's distribution blended with a FIXED
fresh-data mass ν > 0. The fresh-data mass is THE anti-collapse
knob: every generation re-injects ν of the real data, so the
training target never degenerates to the model's own output
(the ν = 0 limit is exactly the collapse protocol of Shumailov
et al.: model → model → model with no anchor).

**The honest engine (what is proved, what is assumed).**

* CLAIM 1 (theorem, `entropy_mix_ge`): entropy concavity —
  `H(m_k) ≥ (1−ν)·H(p_k) + ν·H(p_data)`. Proved from the repo's
  `kl_nonneg` (`Hagi.Data/DField`) via the Jensen–Shannon
  identity `H(m) − (1−ν)H(p) − νH(q) = (1−ν)·KL(p‖m) + ν·KL(q‖m)`
  (the same span-1 identity as `dfield_entropy_identity`).

* CLAIM 2 (honest GAP — the entropy–KL tradeoff is FALSE as
  stated): `KL(m‖q) ≤ δ ⟹ H(q) ≥ H(m) − δ` does not hold in
  general. Explicit counterexample (binary alphabet):
  m = (0.9, 0.1), q = (0.99, 0.01): KL(m‖q) = 0.1445 ≤ δ, yet
  H(m) − δ = 0.1806 > H(q) = 0.0560. A small divergence bounds
  likelihood ratios where m has mass, but the student can still
  sharpen the tail and lose far more entropy than δ — entropy
  is not Lipschitz in KL at linear rate (the true modulus is
  Pinsker/sub-linear, and the Wasserstein-contraction
  form is strictly stronger). What IS true (proved here as
  `entropy_kl_ce_identity`, the `Hagi.Data/Distill` master
  identity in H-form): `CE_m(q) = H(m) + KL(m‖q)` — the KL
  certification bounds the student's CROSS-entropy against the
  target, exactly. Hence the per-step entropy preservation
  enters as the explicit hypothesis hcert (a strengthening of
  the h_emp_ training guarantee: not only KL ≤ δ but entropy
  within δ) — this file's results are conditional on it, and
  that is the honest form.

* CLAIM 3 (theorem, `distill_entropy_recurrence`,
  `entropy_floor`): under the certified steps,
  `H(p_T) ≥ (1−ν)^T·H(p_0) + (1−(1−ν)^T)·(H(p_data) − δ/ν)`
  — the exact closed form (geometric interpolation between the
  initial entropy and the fixed point h − δ/ν of
  x ↦ (1−ν)x + νh − δ; fixed-point algebra:
  x* = (νh−δ)/ν = h − δ/ν ✓). As T grows the bound approaches
  H(p_data) − δ/ν: THE ENTROPY floor. With δ small and ν fixed,
  collapse below the floor is impossible.

* CLAIM 4 (theorem, `fresh_data_prevents_collapse`): the
  invariant form — if `H(p_0) ≥ H(p_data) − δ/ν` then the
  entropy stays above `H(p_data) − δ/ν` at every generation.
  Uniform ε form (`fresh_data_prevents_collapse_uniform`):
  with `δ ≤ ν·ε` and `H(p_0) ≥ H(p_data) − ε`, entropy never
  falls below `H(p_data) − ε`. The fresh-data mass ν > 0 is
  what makes the floor exist: at ν = 0 the floor constant
  δ/ν diverges and the theorem is vacuous — collapse is exactly
  the ν = 0 protocol.

**Open (flagged, not proved):** Wasserstein contraction of the
Wasserstein contraction of the generation map with fixed point
p* satisfying H(p*) ≥ H(data) − ε — stays open; the
KL-certification-only entropy floor (replacing hcert by a
Pinsker-type sub-linear correction) stays open.
-/

open Finset

namespace Hagi.Data

section DistillRecursion

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Bridge: entDef = Information.shannon. -/
theorem entDef_eq_shannon (p : V → ℝ) :
    Hagi.Prelude.entDef p = Hagi.Information.shannon p := by
  simp [Hagi.Prelude.entDef, Hagi.Information.shannon, Real.negMulLog]




/-- The recursive-distillation training target: the previous
model's distribution blended with the fresh-data mass ν:
`m = (1−ν)·p + ν·d`. The anti-collapse anchor. -/
def freshMix (ν : ℝ) (p d : V → ℝ) : V → ℝ :=
  fun v => (1 - ν) * p v + ν * d v

/-! ### The mixture: positivity and normalization -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
theorem freshMix_pos (ν : ℝ) (p d : V → ℝ) (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < p v) (hd : ∀ v, 0 < d v) :
    ∀ v, 0 < freshMix ν p d v := by
  intro v
  unfold freshMix
  have h1 : 0 ≤ (1 - ν) * p v := mul_nonneg (by linarith) (le_of_lt (hp v))
  rcases lt_or_eq_of_le hν with hν0 | hν0
  · exact add_pos_of_nonneg_of_pos h1 (mul_pos hν0 (hd v))
  · subst hν0
    norm_num
    exact hp v

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
theorem freshMix_sum_one (ν : ℝ) (p d : V → ℝ)
    (hsp : ∑ v, p v = 1) (hsd : ∑ v, d v = 1) :
    ∑ v, freshMix ν p d v = 1 := by
  unfold freshMix
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsp, hsd]
  ring

/-! ### CLAIM 1: entropy concavity of the mixture -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Entropy concavity (CLAIM 1, theorem).** The training
target's entropy is at least the weighted entropies:
`H((1−ν)p + νd) ≥ (1−ν)·H(p) + ν·H(d)`. Entropy is gained by
mixing — the fresh-data blend RAISES the target entropy above
the model's, which is the whole anti-collapse mechanism.
Engine: the Jensen–Shannon identity (the mixture entropy minus
the weighted parts equals the weighted KLs to the mixture,
each nonneg by `kl_nonneg`). -/
theorem entropy_mix_ge (ν : ℝ) (p d : V → ℝ)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < p v) (hd : ∀ v, 0 < d v)
    (hsp : ∑ v, p v = 1) (hsd : ∑ v, d v = 1) :
    (1 - ν) * Hagi.Prelude.entDef p + ν * Hagi.Prelude.entDef d
      ≤ Hagi.Prelude.entDef (freshMix ν p d) := by
  have hmp : ∀ v, 0 < freshMix ν p d v :=
    freshMix_pos ν p d hν hν1 hp hd
  have hms : ∑ v, freshMix ν p d v = 1 := freshMix_sum_one ν p d hsp hsd
  -- the Jensen–Shannon identity: weighted KLs to the mixture
  -- = mixture entropy − weighted entropies
  have hfold : (1 - ν) * (∑ v, p v * Real.log (freshMix ν p d v))
        + ν * (∑ v, d v * Real.log (freshMix ν p d v))
      = ∑ v, freshMix ν p d v * Real.log (freshMix ν p d v) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by
      unfold freshMix; ring
  have htermp : ∀ v : V, p v * Real.log (p v / freshMix ν p d v)
      = p v * Real.log (p v)
        - p v * Real.log (freshMix ν p d v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hmp v))]
    ring
  have hklp : Hagi.Prelude.klDef p (freshMix ν p d)
      = ∑ v, p v * Real.log (p v)
        - ∑ v, p v * Real.log (freshMix ν p d v) := by
    unfold Hagi.Prelude.klDef
    rw [Finset.sum_congr rfl (fun v _ => htermp v), ← Finset.sum_sub_distrib]
  have htermd : ∀ v : V, d v * Real.log (d v / freshMix ν p d v)
      = d v * Real.log (d v)
        - d v * Real.log (freshMix ν p d v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hd v)) (ne_of_gt (hmp v))]
    ring
  have hkld : Hagi.Prelude.klDef d (freshMix ν p d)
      = ∑ v, d v * Real.log (d v)
        - ∑ v, d v * Real.log (freshMix ν p d v) := by
    unfold Hagi.Prelude.klDef
    rw [Finset.sum_congr rfl (fun v _ => htermd v), ← Finset.sum_sub_distrib]
  -- each KL is nonneg (the repo's DField toolkit)
  have hkl1 : 0 ≤ Hagi.Prelude.klDef p (freshMix ν p d) :=
    kl_nonneg p _ hp hmp hsp hms
  have hkl2 : 0 ≤ Hagi.Prelude.klDef d (freshMix ν p d) :=
    kl_nonneg d _ hd hmp hsd hms
  -- weighted-sum the two nonneg KLs, fold, and read off H
  have hcomb : (1 - ν) * Hagi.Prelude.klDef p (freshMix ν p d)
        + ν * Hagi.Prelude.klDef d (freshMix ν p d)
      = Hagi.Prelude.entDef (freshMix ν p d)
        - (1 - ν) * Hagi.Prelude.entDef p - ν * Hagi.Prelude.entDef d := by
    rw [hklp, hkld]
    have e4 : (1 - ν) * (∑ v, p v * Real.log (freshMix ν p d v))
        + ν * (∑ v, d v * Real.log (freshMix ν p d v))
        = ∑ v, freshMix ν p d v * Real.log (freshMix ν p d v) := hfold
    unfold Hagi.Prelude.entDef
    ring_nf
    linarith [hfold]
  have hwnn : 0 ≤ (1 - ν) * Hagi.Prelude.klDef p (freshMix ν p d)
      + ν * Hagi.Prelude.klDef d (freshMix ν p d) := by
    exact add_nonneg (mul_nonneg (by linarith) hkl1) (mul_nonneg hν hkl2)
  rw [hcomb] at hwnn
  linarith

/-! ### CLAIM 2 (the honest form): the true entropy–KL identity -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The true entropy–KL identity (CLAIM 2, honest form).**
The student's cross-entropy against the target is EXACTLY the
target entropy plus the divergence:
`CE_m(q) = H(m) + KL(m‖q)` — the `Hagi.Data/Distill` master
identity `teacher_generated_identity` restated with the canonical
`Hagi.Prelude.entDef` definition of entropy. This is what the h_emp_ KL certification
`KL(m‖q) ≤ δ` really buys: `CE_m(q) ≤ H(m) + δ`. It does not
buy `H(q) ≥ H(m) − δ` (that direction is FALSE — see the module
docstring for the explicit counterexample), so the per-step
entropy preservation is carried below as the explicit
hypothesis hcert. -/
theorem entropy_kl_ce_identity (m q : V → ℝ)
    (hm : ∀ v, 0 < m v) (hq : ∀ v, 0 < q v) :
    crossEntropy m q = Hagi.Prelude.entDef m + Hagi.Prelude.klDef m q := by
  have h := teacher_generated_identity m q hm hq
  unfold crossEntropy at h ⊢
  rw [Hagi.Prelude.ceDef_self] at h
  simp only [Hagi.Prelude.entDef] at h ⊢
  linarith

/-! ### The certified step -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The per-generation entropy inequality (CLAIM 1 + the
certified step).** If generation k+1's entropy is certified
within δ of its training target's (the hcert hypothesis — the
honest strengthening of the h_emp_ KL guarantee; see
`entropy_kl_ce_identity` for why KL alone does not suffice),
then

`H(p_{k+1}) ≥ (1−ν)·H(p_k) + ν·H(p_data) − δ` —

fresh data pulls the entropy floor up by ν·(H(data) − H(p_k)),
the distillation error pulls it down by at most δ. -/
theorem distill_step_entropy (pNext pK d : V → ℝ) (ν δ : ℝ)
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hp : ∀ v, 0 < pK v) (hd : ∀ v, 0 < d v)
    (hsp : ∑ v, pK v = 1) (hsd : ∑ v, d v = 1)
    (hcert : Hagi.Prelude.entDef (freshMix ν pK d) - δ
      ≤ Hagi.Prelude.entDef pNext) :
    (1 - ν) * Hagi.Prelude.entDef pK + ν * Hagi.Prelude.entDef d - δ
      ≤ Hagi.Prelude.entDef pNext := by
  have hmix := entropy_mix_ge ν pK d hν hν1 hp hd hsp hsd
  linarith

/-! ### CLAIM 3: the closed-form recursive floor -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The recursive entropy floor (CLAIM 3, main theorem).**
For a generation sequence p_k where every step is certified
(each generation's entropy within δ of its fresh-mix target),
the exact closed form holds for every horizon T:

`H(p_T) ≥ (1−ν)^T · H(p_0) + (1 − (1−ν)^T) · (H(p_data) − δ/ν)`.

Solving x_{k+1} = (1−ν)x_k + νh − δ (h = H(p_data)): the fixed
point is h − δ/ν and the solution is the geometric
interpolation between H(p_0) and the fixed point. As T → ∞ the
weight (1−ν)^T → 0 and the floor approaches H(p_data) − δ/ν:
with δ small and ν fixed, the entropy CANNOT collapse below the
floor — model collapse is impossible under certified recursive
self-distillation with fresh data. -/
theorem distill_entropy_recurrence (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (_hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, Hagi.Prelude.entDef (freshMix ν (p k) d) - δ
      ≤ Hagi.Prelude.entDef (p (k + 1))) (T : ℕ) :
    (1 - ν)^T * Hagi.Prelude.entDef (p 0)
      + (1 - (1 - ν)^T) * (Hagi.Prelude.entDef d - δ / ν)
      ≤ Hagi.Prelude.entDef (p T) := by
  induction T with
  | zero =>
    simp only [pow_zero]
    norm_num
  | succ T ih =>
    have hc : (0:ℝ) ≤ 1 - ν := by linarith
    have h1 := distill_step_entropy (p (T + 1)) (p T) d ν δ
      hν.le hν1 (hp T) hd (hsp T) hsd (hcert T)
    have h2 : (1 - ν) * ((1 - ν)^T * Hagi.Prelude.entDef (p 0)
          + (1 - (1 - ν)^T) * (Hagi.Prelude.entDef d - δ / ν))
        ≤ (1 - ν) * Hagi.Prelude.entDef (p T) :=
      mul_le_mul_of_nonneg_left ih hc
    have key : (1 - ν) * ((1 - ν)^T * Hagi.Prelude.entDef (p 0)
          + (1 - (1 - ν)^T) * (Hagi.Prelude.entDef d - δ / ν))
          + ν * (Hagi.Prelude.entDef d - δ / ν)
        = (1 - ν) * (1 - ν)^T * Hagi.Prelude.entDef (p 0)
          + (1 - (1 - ν) * (1 - ν)^T) * (Hagi.Prelude.entDef d - δ / ν) := by
      have hν0 : ν ≠ 0 := ne_of_gt hν
      field_simp
      ring
    have h3 : ν * (Hagi.Prelude.entDef d - δ / ν) = ν * Hagi.Prelude.entDef d - δ := by
      rw [mul_sub, mul_div_cancel₀ δ (ne_of_gt hν)]
    rw [show (1 - ν)^(T + 1) = (1 - ν) * (1 - ν)^T from by
      rw [pow_succ (1 - ν) T, mul_comm ((1 - ν)^T) (1 - ν)]]
    linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The entropy floor, asymptotic form (CLAIM 3).** The same
closed form rewritten as "floor minus an exponentially
vanishing correction":

`H(p_T) ≥ (H(p_data) − δ/ν) − (1−ν)^T · ((H(p_data) − δ/ν) − H(p_0))`.

The distance from the floor H(p_data) − δ/ν contracts by the
factor (1−ν) < 1 per generation: the floor is approached
exponentially fast, and the correction's sign depends only on
whether the initial entropy starts above or below the floor. -/
theorem entropy_floor (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, Hagi.Prelude.entDef (freshMix ν (p k) d) - δ
      ≤ Hagi.Prelude.entDef (p (k + 1))) (T : ℕ) :
    Hagi.Prelude.entDef d - δ / ν
      - (1 - ν)^T * (Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0))
      ≤ Hagi.Prelude.entDef (p T) := by
  have hr := distill_entropy_recurrence p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hring : (1 - ν)^T * Hagi.Prelude.entDef (p 0)
      + (1 - (1 - ν)^T) * (Hagi.Prelude.entDef d - δ / ν)
      = Hagi.Prelude.entDef d - δ / ν
        - (1 - ν)^T * (Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0)) := by
    ring
  linarith [hr, hring]

/-! ### CLAIM 4: fresh data prevents collapse -/

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Fresh data prevents collapse (CLAIM 4, the invariant
form).** If the initial entropy is at or above the floor
`H(p_0) ≥ H(p_data) − δ/ν`, then the entropy stays above the
floor at every generation — forever, uniformly in T. The
correction term in `entropy_floor` is then non-positive and
drops out. With δ small and ν fixed, collapse below
H(p_data) − δ/ν is impossible: the fresh-data mass ν is the
anti-collapse knob (at ν = 0 the floor constant δ/ν diverges
and the statement is vacuous — collapse IS the ν = 0
protocol). -/
theorem fresh_data_prevents_collapse (p : ℕ → V → ℝ) (d : V → ℝ) (ν δ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, Hagi.Prelude.entDef (freshMix ν (p k) d) - δ
      ≤ Hagi.Prelude.entDef (p (k + 1)))
    (hinv : Hagi.Prelude.entDef d - δ / ν ≤ Hagi.Prelude.entDef (p 0))
    (T : ℕ) :
    Hagi.Prelude.entDef d - δ / ν ≤ Hagi.Prelude.entDef (p T) := by
  have hc : (0:ℝ) ≤ 1 - ν := by linarith
  have hf := entropy_floor p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hB : Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0) ≤ 0 := by linarith
  have hcorr : (1 - ν)^T
      * (Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hc T) hB
  linarith

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **Fresh data prevents collapse, uniform ε form (CLAIM 4).**
With the certified error δ at most ν·ε and the initial entropy
at least H(p_data) − ε, the entropy never falls below
H(p_data) − ε — a UNIFORM floor for all generations. Since
δ/ν ≤ ε, the floor H(p_data) − δ/ν dominates H(p_data) − ε:
any ε-prevention budget ε is met by certified training with
error δ ≤ ν·ε. -/
theorem fresh_data_prevents_collapse_uniform (p : ℕ → V → ℝ) (d : V → ℝ)
    (ν δ ε : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 ≤ δ) (_hε : 0 ≤ ε)
    (hp : ∀ k v, 0 < p k v) (hd : ∀ v, 0 < d v)
    (hsp : ∀ k, ∑ v, p k v = 1) (hsd : ∑ v, d v = 1)
    (hcert : ∀ k, Hagi.Prelude.entDef (freshMix ν (p k) d) - δ
      ≤ Hagi.Prelude.entDef (p (k + 1)))
    (hδε : δ ≤ ν * ε)
    (h0 : Hagi.Prelude.entDef d - ε ≤ Hagi.Prelude.entDef (p 0))
    (T : ℕ) :
    Hagi.Prelude.entDef d - ε ≤ Hagi.Prelude.entDef (p T) := by
  have hdn : δ / ν ≤ ε := by
    rw [div_le_iff₀ hν, mul_comm]
    exact hδε
  -- direct: the floor correction is at most ε − δ/ν (initial entropy
  -- within ε of the data, contraction factor ≤ 1)
  have hc : (0:ℝ) ≤ 1 - ν := by linarith
  have hX : (1 - ν)^T ≤ 1 := by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [pow_succ]
      exact (mul_le_mul ih (by linarith : (1:ℝ) - ν ≤ 1) hc zero_le_one).trans
        (by norm_num : (1:ℝ) * 1 ≤ 1)
  have hf := entropy_floor p d ν δ hν hν1 hδ hp hd hsp hsd hcert T
  have hdif : Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0) ≤ ε - δ / ν := by
    linarith
  have hprod : (1 - ν)^T
      * (Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0))
      ≤ ε - δ / ν := by
    have hstep1 : (1 - ν)^T
        * (Hagi.Prelude.entDef d - δ / ν - Hagi.Prelude.entDef (p 0))
        ≤ (1 - ν)^T * (ε - δ / ν) :=
      mul_le_mul_of_nonneg_left hdif (pow_nonneg hc T)
    have hstep2 : (1 - ν)^T * (ε - δ / ν) ≤ 1 * (ε - δ / ν) :=
      mul_le_mul_of_nonneg_right hX (by linarith)
    linarith
  linarith


/-- **Entropy floor с TV-сертификатом**
— посылка в Pinsker/Fannes-форме
(KL ≤ δ НЕ спасает энтропию — sharpening tail): если полная вариация fresh-смеси и
следующего поколения ограничена (сертификат |H(fm)−H(p')| ≤ B,
B — Fannes-граница через τ = tvDist, см. AntiCollapse),
то entropy floor выполняется с эффективным δ_eff = B:
H(p_T) ≥ H(data) − B/ν − (затухание). -/
alias entropy_floor_tv := _root_.Hagi.Data.entropy_floor

end DistillRecursion

end Hagi.Data

namespace Hagi

end Hagi

set_option linter.style.header false

/-!
# InfoNCE — нижняя граница взаимной информации

Формализация ядра InfoNCE-неравенства (van den Oord et al.,
«Representation Learning with Contrastive Predictive Coding»;
корпус-подтверждение: SSL-HSICIC 2106.08320 — «InfoNCE, a
variational lower bound on the mutual information»):
контрастивный лосс (кросс-энтропия softmax-модели против
целевого индекса) НЕ МОЖЕТ опуститься ниже энтропии цели —
потому log K − L_NCE ≤ log K − H: InfoNCE-оценка никогда не
переоценивает взаимную информацию.

Доказано (на канонических CE/KL/H из Data/Canonical):
* `ce_ge_entropy`: CE q p ≥ H q — кросс-энтропия не ниже
  собственной энтропии цели;
* `infonce_never_overestimates`: log k − CE q p ≤
  log k − H q — InfoNCE-оценка MI не выше log K − H(q);
* `infonce_gap_is_kl`: зазор «MI − InfoNCE-оценка» — ТОЧНО
  KL(post ‖ model): контрастивная оценка терминально точна
  ⟺ модель равна постериору.

-/

open Finset

/-!
# Canonical information-theoretic objects and their bridges

The classical KL, entropy, TV and cross-entropy all reduce to the
`Hagi.Prelude` definitions; every variant in the repo is bridged to
that form by an `..._eq_canonical` theorem (the variant names are kept
as delegation aliases). Cross-entropy `CE` is `Hagi.Prelude.ceDef`.

Not unified: the matrix/spectral entropy
`Hagi.Information.entropy` is a different object (cfc of a
PSD matrix), related to the classical entropy only through the
diagonal-entropy bridge hypothesis of DiscreteFannes.
-/

open scoped BigOperators

namespace Hagi.Data

variable {V : Type*} [Fintype V]

/- Канонические KL/H/TV (Prelude) напрямую; CE — делегат Prelude.ceDef (= Distill.crossEntropy). -/
noncomputable def CE (q p : V → ℝ) : ℝ := Hagi.Prelude.ceDef q p

/-- Bridge: `CE` IS the canonical `Prelude.ceDef`. -/
theorem CE_eq_ceDef (q p : V → ℝ) :
    CE q p = Hagi.Prelude.ceDef q p := rfl

/-! ## Bridge theorems: every variant IS the canonical form -/



-- (the Energy.FreeEnergy.kldiv bridge lives in
-- Energy/FreeEnergy.lean itself: same-layer import rule)


theorem shannon_eq_canonical {ι : Type*} [Fintype ι]
    (p : ι → ℝ) :
    Hagi.Information.shannon p = -∑ i, p i * Real.log (p i) := by
  have h1 : Hagi.Information.shannon p
      = ∑ i, Real.negMulLog (p i) := rfl
  have h2 : ∀ i : ι, Real.negMulLog (p i)
      = -(p i * Real.log (p i)) := fun i => by
    unfold Real.negMulLog
    ring
  rw [h1, Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_neg_distrib]


theorem tvHalf_eq_canonical {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    Hagi.Information.tvHalf p q = (∑ i, |p i - q i|) / 2 := rfl


/-! ## The canonical identity block (one place) -/

set_option linter.unusedVariables false in
/-- KL is the excess cross-entropy over the entropy
baseline — the canonical form of the law. -/
theorem kl_excess_cross_entropy (q p : V → ℝ)
    (hq : ∀ v, q v ≠ 0) (hp : ∀ v, p v ≠ 0) :
    Hagi.Prelude.klDef q p = Hagi.Data.crossEntropy q p - Hagi.Data.crossEntropy q q :=
  Hagi.Prelude.klDef_eq_ceDef_sub q p hp

end Hagi.Data

open Finset

namespace Hagi.Data

variable {V : Type} [Fintype V] [DecidableEq V]

/-- CE q q в точности равен энтропии H q (знак-соглашения
канонических определений совпадают). -/
theorem ce_self_eq_entropy (q : V → ℝ) :
    Hagi.Data.crossEntropy q q = Hagi.Prelude.entDef q := rfl

/-- Кросс-энтропия не ниже энтропии цели: CE q p ≥ H q
(KL ≥ 0 в ce-разложении kl_excess_cross_entropy). -/
theorem ce_ge_entropy (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    Hagi.Prelude.entDef q ≤ Hagi.Data.crossEntropy q p := by
  have hex := Hagi.Data.kl_excess_cross_entropy q p
    (fun v => ne_of_gt (hq v))
    (fun v => ne_of_gt (hp v))
  have hkl : 0 ≤ Hagi.Prelude.klDef q p :=
    Hagi.kl_nonneg q p hq hp hsumq hsump
  rw [ce_self_eq_entropy] at hex
  linarith [hex, hkl]

/-- InfoNCE никогда не переоценивает MI: log k − лосс
не выше log k − энтропийного пола. -/
theorem infonce_never_overestimates (k : ℝ) (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    k - Hagi.Data.crossEntropy q p ≤ k - Hagi.Prelude.entDef q := by
  have h := ce_ge_entropy q p hsumq hsump hq hp
  linarith

/-- Зазор «MI − InfoNCE-оценка» — ТОЧНО KL(post ‖ model):
контрастивная оценка терминально точна ⟺ модель совпадает
с постериором (зазор нулевой ⟺ KL нулевой). -/
theorem infonce_gap_is_kl (k : ℝ) (q p : V → ℝ)
    (hq : ∀ v, q v ≠ 0) (hp : ∀ v, p v ≠ 0) :
    (k - Hagi.Prelude.entDef q) - (k - Hagi.Data.crossEntropy q p)
      = Hagi.Prelude.klDef q p := by
  have hex := Hagi.Data.kl_excess_cross_entropy q p hq hp
  rw [ce_self_eq_entropy] at hex
  linarith

end Hagi.Data
