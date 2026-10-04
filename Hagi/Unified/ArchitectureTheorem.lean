/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Autonomy.Universality
import Hagi.Growth.StateClosedRenewal
import Hagi.Growth.Saturation
import Hagi.Step.SafeQPPL
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.DistillTransfer
set_option linter.style.header false

/-!
# R138 (rev.2): HAGI Synthesis — honest-horizon capstone

REVISION (audit 2026-10-04): the original capstone quantified
step premises over ALL t while C*=100 and sigma=1/2 were
hardcoded. Combined with the PL-window this made the premise
set UNSATISFIABLE for gamma*k > 0 (the takeoff cone forces
C_t >= C0*(1+gamma*k)^t to infinity against C_t <= Cstar):
the theorem was TRUE BUT VACUOUS - a specification defect
that "0 sorry" does not catch. This revision fixes it:

* all step premises are quantified over the HORIZON ONLY
  (t ∈ Finset.range T);
* Cstar and sigma are certificate PARAMETERS (with window
  hypotheses 0 < sigma, sigma <= 1, 0 < Cstar);
* the T3 operator premise is stated in the NAT metric of
  R134 (distillEfficiency): an abstract measurable gain
  stream `g : ℕ → ℝ` in nats/step, replacing the weight-space
  devEnergy of the INTERIM R130 (deprecated per plan §7);
* truncated band lemmas below prove the growth band at T
  from horizon-only premises - no shadow global assumptions;
* `band_witness` - a CONCRETE numeric sequence pair
  (C t = 100 - 99*(1/2)^t, D t = 990*(1/2)^t at
  Cstar=100, sigma=1/2, gamma=1/20, k=1/1000, T=10)
  satisfying every truncated premise - the certificate is
  demonstrably NON-vacuous.

The band interpretation stays per the R132-REV FREEZE: the
certificate is usable exactly while
C0*(1+gamma*k)^T <= Cstar, i.e.
T <= T* = ln(Cstar/C0)/ln(1+gamma*k).
-/

open Finset

namespace Hagi

variable {Xs V : Type*} [NormedAddCommGroup Xs]
  [InnerProductSpace ℝ Xs]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Truncated cone invariant: from the cone at 0 and
horizon-only step/dynamics premises, D t >= k * C t holds
for every t <= T. -/
theorem cone_invariant_trunc (C D : ℕ → ℝ) (γ ρ β k : ℝ) (T : ℕ)
    (hCpos : ∀ t ∈ Finset.range (T + 1), 0 < C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := by
  have hmain : ∀ t : ℕ, t ≤ T → k * C t ≤ D t := by
    intro t
    induction t with
    | zero => intro _; exact hcone0
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T :=
          Finset.mem_range.mpr (by omega)
        have hs := hstep t htlt
        have hd := hdyn t htlt
        have hCp : 0 < C t := hCpos t
          (Finset.mem_range.mpr (by omega))
        have hkey : ρ * D t + β * C t - k * (C t + γ * D t)
            = (ρ - γ * k) * (D t - k * C t)
              + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
          field_simp
          ring
        have hnn1 : (0:ℝ) ≤ (ρ - γ * k) * (D t - k * C t) :=
          mul_nonneg (by linarith)
            (by linarith [ih (by omega)])
        have hnn2 : (0:ℝ)
            ≤ (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
          mul_nonneg (by linarith) hCp.le
        have hsum : (0:ℝ)
            ≤ (ρ - γ * k) * (D t - k * C t)
              + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
          add_nonneg hnn1 hnn2
        rw [hs]
        linarith [hd, hkey, hsum]
  intro t ht
  exact hmain t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))

/-- Truncated takeoff lower bound: C T >= C 0 * (1+gamma k)^T
from horizon-only premises (steps t < T only). -/
theorem takeoff_lower_trunc (C D : ℕ → ℝ) (γ k : ℝ) (T : ℕ)
    (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hcone : ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t) :
    C 0 * (1 + γ * k) ^ T ≤ C T := by
  have hmain : ∀ t : ℕ, t ≤ T →
      C 0 * (1 + γ * k) ^ t ≤ C t := by
    intro t ht
    induction t with
    | zero => simpa using le_refl (C 0)
    | succ t ih =>
        have hs := hstep t (Finset.mem_range.mpr (by omega))
        have hc := hcone t (Finset.mem_range.mpr (by omega))
        have hγk : (0:ℝ) ≤ γ * k := by positivity
        have hmul : (1 + γ * k) * C t
            ≥ (1 + γ * k) * (C 0 * (1 + γ * k) ^ t) :=
          mul_le_mul_of_nonneg_left (ih (by omega))
            (by linarith)
        have hsplit : C t + γ * (k * C t)
            = (1 + γ * k) * C t := by ring
        have hge : γ * D t ≥ γ * (k * C t) :=
          mul_le_mul_of_nonneg_left hc hγ
        rw [hs, pow_succ]
        nlinarith [hmul, hsplit, hge]
  exact hmain T (le_refl T)

/-- Truncated saturation upper bound: from the PL window at
steps t < T, Cstar - C T <= (1-sigma)^T * (Cstar - C 0). -/
theorem pl_gap_upper_trunc (C : ℕ → ℝ) (Cstar σ : ℝ) (T : ℕ)
    (hσ1 : σ ≤ 1)
    (hpl_lo : ∀ t ∈ Finset.range T,
      C t + σ * (Cstar - C t) ≤ C (t + 1)) :
    Cstar - C T ≤ (1 - σ) ^ T * (Cstar - C 0) := by
  have hmain : ∀ t : ℕ, t ≤ T →
      Cstar - C t ≤ (1 - σ) ^ t * (Cstar - C 0) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
        have h := hpl_lo t (Finset.mem_range.mpr (by omega))
        have hstep : Cstar - C (t + 1)
            ≤ (1 - σ) * (Cstar - C t) := by
          have hE : (1 - σ) * (Cstar - C t)
              = Cstar - C t - σ * (Cstar - C t) := by ring
          linarith [hE]
        rw [pow_succ]
        calc Cstar - C (t + 1) ≤ (1 - σ) * (Cstar - C t) :=
              hstep
          _ ≤ (1 - σ) * ((1 - σ) ^ t * (Cstar - C 0)) :=
              mul_le_mul_of_nonneg_left (ih (by omega))
                (by linarith)
          _ = (1 - σ) ^ t * (1 - σ) * (Cstar - C 0) := by ring
  exact hmain T (le_refl T)

/-- Truncated band UPPER bound: from the upper PL form at
steps t < T, (1-sigma)^T * (Cstar - C 0) <= Cstar - C T,
i.e. C T <= Cstar - (1-sigma)^T * (Cstar - C 0). -/
theorem pl_gap_lower_trunc (C : ℕ → ℝ) (Cstar σ : ℝ) (T : ℕ)
    (hσ1 : σ ≤ 1)
    (hpl_up : ∀ t ∈ Finset.range T,
      C (t + 1) ≤ C t + σ * (Cstar - C t)) :
    (1 - σ) ^ T * (Cstar - C 0) ≤ Cstar - C T := by
  have hmain : ∀ t : ℕ, t ≤ T →
      (1 - σ) ^ t * (Cstar - C 0) ≤ Cstar - C t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro hle
        have h := hpl_up t (Finset.mem_range.mpr (by omega))
        have hstep : (1 - σ) * (Cstar - C t) ≤ Cstar - C (t + 1) := by
          have hE : (1 - σ) * (Cstar - C t)
              = Cstar - C t - σ * (Cstar - C t) := by ring
          linarith [hE]
        rw [pow_succ]
        calc (1 - σ) ^ t * (1 - σ) * (Cstar - C 0)
            = (1 - σ) * ((1 - σ) ^ t * (Cstar - C 0)) := by ring
          _ ≤ (1 - σ) * (Cstar - C t) :=
              mul_le_mul_of_nonneg_left (ih (by omega))
                (by linarith)
          _ ≤ Cstar - C (t + 1) := hstep
  exact hmain T (le_refl T)

/-- Пошаговые сертификаты цикла HAGI НА ГОРИЗОНТЕ T (все
измеряемы): рост (шаг состояния + оператор T3 в НАТАХ -
абстрактный измеряемый gain-поток g : N -> R, нат/шаг;
мотивация - distillEfficiency R134), ёмкость (PL-окно с
ПАРАМЕТРАМИ Cstar и sigma), универсальность/безопасность
(Hedge + суммируемый дрейф).

Каждая пошаговая посылка квантифицирована по
t ∈ Finset.range T - ТОЛЬКО горизонт, никаких глобальных
посылок: сертификат выполним ровно пока
C0*(1+gamma*k)^T <= Cstar (см. band_witness ниже -
не-вакуозный числовой свидетель). -/
structure HAGICert (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ) where
  hCpos : ∀ t ∈ Finset.range (T + 1), 0 < (S t).capability
  hstep : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    = (S t).capability + γ * usableFrontier (S t)
  hop : ∀ t ∈ Finset.range T, ρ * usableFrontier (S t)
    + ηT * g t - ξ
      ≤ usableFrontier (S (t + 1))
  hsuff : ∀ t ∈ Finset.range T, γ * k ^ 2 * (S t).capability
    + (1 - ρ) * k * (S t).capability + ξ
    ≤ ηT * g t
  hrhogk : γ * k ≤ ρ
  hcone0 : k * (S 0).capability ≤ usableFrontier (S 0)
  hpl_up : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    ≤ (S t).capability + σ * (Cstar - (S t).capability)
  hpl_lo : ∀ t ∈ Finset.range T, (S t).capability
    + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability
  hCstar : 0 < Cstar
  hσ0 : 0 < σ
  hσ1 : σ ≤ 1
  hC0 : (S 0).capability ≤ Cstar
  hrisk : ∀ t ∈ Finset.range T,
    risk t (0 : Fin 1) ≤ best (0 : Fin 1) + r t + ε0 * ρe ^ t
  hregret : ∑ t ∈ Finset.range T, r t ≤ R
  hε0 : 0 ≤ ε0
  hρe : 0 ≤ ρe
  hρe1 : ρe < 1

/-- **CAPSTONE (горизонт-форма)**: при живых пошаговых
сертификатах НА ГОРИЗОНТЕ T цикл HAGI ОДНОВРЕМЕННО даёт:

1. РОСТ с ёмкостью: C₀(1+γk)^T ≤ C_T
   ≤ C* − (1−σ)^T·(C* − C₀) - все посылки только при
   t < T (усечённые леммы выше), C* и σ - параметры;
2. УНИВЕРСАЛЬНОСТЬ + LONG-HORIZON SAFETY: Σ risk ≤ T·best +
   R + ε₀/(1−ρe).

Выполнимость сертификата = условие горизонта
C₀(1+γk)^T ≤ C*; band_witness предъявляет конкретные
числа (T = 10, C* = 100): НЕ вакуозно. -/
theorem hagi_synthesis (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k)
    (cert : HAGICert S g risk best r
      γ ρ k ξ ηT Cstar σ ε0 ρe R T) :
    ((S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability))
    ∧ (∑ t ∈ Finset.range T, risk t (0 : Fin 1)
      ≤ T * best (0 : Fin 1) + R + ε0 / (1 - ρe)) := by
  obtain ⟨hCpos, hstep, hop, hsuff, hrhogk, hcone0, hpl_up,
    hpl_lo, hCstar, hσ0, hσ1, hC0, hrisk, hregret, hε0,
    hρe, hρe1⟩ := cert
  constructor
  · -- полоса роста: динамика на горизонте ⟹ конус
    have hdyn : ∀ t ∈ Finset.range T,
        ρ * usableFrontier (S t)
        + (γ * k ^ 2 + (1 - ρ) * k) * (S t).capability
        ≤ usableFrontier (S (t + 1)) := by
      intro t ht
      have h1 := hop t ht
      have h2 := hsuff t ht
      linarith
    have hcone := cone_invariant_trunc
      (fun t => (S t).capability)
      (fun t => usableFrontier (S t))
      γ ρ (γ * k ^ 2 + (1 - ρ) * k) k T
      hCpos hstep hdyn hrhogk
      (by linarith) hcone0
    constructor
    · exact takeoff_lower_trunc
        (fun t => (S t).capability)
        (fun t => usableFrontier (S t)) γ k T
        (le_of_lt hγ) (le_of_lt hk) hstep hcone
    · have hband := pl_gap_lower_trunc
        (fun t => (S t).capability) Cstar σ T hσ1 hpl_up
      linarith
  · exact universality_longhorizon risk best r (0 : Fin 1) R ε0 ρe
      hrisk hregret hε0 hρe hρe1

/-- The powers of 1/2 stay in [0,1]. -/
theorem half_pow_bounds (t : ℕ) :
    0 < (1/2 : ℝ) ^ t ∧ (1/2 : ℝ) ^ t ≤ 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [pow_succ]
      obtain ⟨h0, h1⟩ := ih
      constructor
      · positivity
      · nlinarith

/-- Powers of 1/2 are antitone in the exponent. -/
theorem half_pow_anti (t s : ℕ) (h : s ≤ t) :
    (1/2 : ℝ) ^ t ≤ (1/2 : ℝ) ^ s := by
  induction t with
  | zero =>
      have hs : s = 0 := Nat.le_zero.mp h
      subst hs
      rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · have hstep := ih (by omega)
        have hp : 0 < (1/2 : ℝ) ^ s := by positivity
        rw [pow_succ]
        nlinarith
      · have hseq : s = t + 1 := by omega
        rw [hseq]

/-- **Vacuity catcher**: a CONCRETE numeric witness of the
truncated band premises -
C t = 100 - 99*(1/2)^t, D t = 990*(1/2)^t with
Cstar = 100, sigma = 1/2, gamma = 1/20, k = 1/1000,
rho = gamma*k = 1/20000, T = 10 (any T <= 10): step,
dynamics, cone and the PL window ALL hold. The horizon
certificate is satisfiable - hagi_synthesis is NOT
vacuous. (The risk/Hedge side of HAGICert is supplied by
the runtime h_emp layer; here the band core is witnessed.) -/
theorem band_witness :
    (∀ T ≤ 10,
      (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ (t + 1))
            = (100 - 99 * (1/2 : ℝ) ^ t)
              + (1/20) * (990 * (1/2 : ℝ) ^ t))
        ∧ (∀ t ∈ Finset.range T,
          (1/20000) * (990 * (1/2 : ℝ) ^ t)
            + ((1/20) * (1/1000) ^ 2
                + (1 - 1/20000) * (1/1000))
                * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ (t + 1))
        ∧ (∀ t ∈ Finset.range (T + 1),
          (1/1000) * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ t)
        ∧ (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ t)
            + (1/2) * (100 - (100 - 99 * (1/2 : ℝ) ^ t))
            ≤ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
            ∧ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
              ≤ (100 - 99 * (1/2 : ℝ) ^ t)
                + (1/2)
                  * (100 - (100 - 99 * (1/2 : ℝ) ^ t)))) := by
  intro T _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _
    rw [pow_succ]
    field_simp
    ring
  · -- dynamics: 0.00005*D + beta*C <= D'
    intro t _
    -- t < T <= 10  =>  h := (1/2)^t >= (1/2)^9
    have ht9 : t ≤ 9 := by
      have hmem := Finset.mem_range.mp ‹t ∈ Finset.range T›
      have := ‹T ≤ 10›
      omega
    have hlo : (1/512 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have hanti := half_pow_anti 9 t ht9
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    rw [show 990 * (1/2 : ℝ) ^ (t + 1)
        = 495 * (1/2 : ℝ) ^ t from by
      rw [pow_succ]
      ring]
    linarith
  · intro t _
    have hlo : (1/1024 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have ht10 : t ≤ 10 := by
        have hmem := Finset.mem_range.mp ‹t ∈ Finset.range (T + 1)›
        omega
      have hanti := half_pow_anti 10 t ht10
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    linarith
  · intro t _
    -- PL window: EXACT equality at sigma = 1/2
    constructor
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith

end Hagi
