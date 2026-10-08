/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.DisagreementChain
import Hagi.Foundations.ConeTakeoff

/-!
# ChainToCone — the measured disagreement chain FEEDS the
growth cone (R247; the audit-§41 bridge, chain side)

The external audit's central demand: connect the measurable
conversion chain (E_dev → G_cap) to the growth-theory
premises, so that a runtime γ̂-certificate plugs into the
cone. This module provides the chain side of that bridge:

* `chain_feeds_cone` — if the four conversion factors each
  clear a floor β (runtime certificate), and raw
  disagreement energy is at least a κ-share of the frontier
  (measured premise: diversity tracks headroom), then the
  cone gain premise holds with γ := β⁴·κ:

    γ · D ≤ G_cap

  — the disagreement chain is not just diagnostic, it IS
  the fuel line of the growth cone.

* `cone_two_sided_certificate` — the cone survives a
  CERTIFIED step: the increment G_t is pinned from BOTH
  sides (γ·D_t ≤ G_t ≤ γ̄·D_t, both sides measured), and
  the cone condition uses γ̄ for preservation. A one-sided
  (lower-bound-only) certificate does NOT preserve the
  cone — a too-large realized increment can overshoot
  k·C ≤ D; honesty note recorded in the docstring.

* `takeoff_from_certificate` — the full audit-§41 arc for
  the chain side: per-step two-sided certificates + cone
  dynamics ⟹ C₀(1+γk)^T ≤ C_T. The runtime measures the
  α's, Lean concludes takeoff.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- **The chain feeds the cone**: with a runtime
certificate that each conversion factor is at least β, and
the diversity-tracks-frontier premise E_raw ≥ κ·D, the cone
gain premise holds with γ := β⁴·κ. -/
theorem chain_feeds_cone (s : DisagreementStages)
    {β κ D : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (hD : 0 ≤ D)
    (hcert : β ≤ s.α_align ∧ β ≤ s.α_trunc
      ∧ β ≤ s.α_safe ∧ β ≤ s.α_cap)
    (hdiv : κ * D ≤ s.E_raw) :
    (β^4 * κ) * D ≤ s.G_cap := by
  obtain ⟨h1, h2, h3, h4⟩ := hcert
  have ha1 : 0 ≤ s.α_align := le_trans hβ h1
  have ha2 : 0 ≤ s.α_trunc := le_trans hβ h2
  have ha3 : 0 ≤ s.α_safe := le_trans hβ h3
  have ha4 : 0 ≤ s.α_cap := le_trans hβ h4
  have hchain : s.G_cap
      = s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw :=
    disagreement_chain s
  have hb : 0 ≤ β * β := mul_nonneg hβ hβ
  have m1 : β * β ≤ s.α_align * s.α_trunc :=
    mul_le_mul h1 h2 hβ ha1
  have m2 : β * β ≤ s.α_safe * s.α_cap :=
    mul_le_mul h3 h4 hβ ha3
  have m3 : (β * β) * (β * β)
      ≤ (s.α_align * s.α_trunc) * (s.α_safe * s.α_cap) :=
    mul_le_mul m1 m2 hb (by positivity)
  have hprod : β^4 ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap := by
    nlinarith [m3]
  have hA : 0 ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap :=
    mul_nonneg (mul_nonneg (mul_nonneg ha1 ha2) ha3) ha4
  have hfinal : β^4 * (κ * D)
      ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw :=
    mul_le_mul hprod hdiv (mul_nonneg hκ hD) hA
  have hrew : β^4 * κ * D = β^4 * (κ * D) := by ring
  rw [hchain]
  nlinarith [hfinal, hrew]

/-- **Cone invariant under a two-sided certified step**: the
realized increment G_t is pinned from BOTH sides,

  γ·D_t ≤ G_t ≤ γ̄·D_t,

the step law is exact (C_{t+1} = C_t + G_t), and the cone
constant uses the UPPER certificate γ̄ (k·γ̄ ≤ ρ). A
one-sided lower certificate alone does NOT preserve the
cone: an increment larger than (ρ/k)·D_t can overshoot
k·C ≤ D — recorded here so the runtime certificate must be
two-sided. -/
theorem cone_two_sided_certificate (C D G : ℕ → ℝ)
    (gamma gbar rho beta k : ℝ) (T : ℕ)
    (hk : 0 ≤ k)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hlow : ∀ t ∈ Finset.range T, gamma * D t ≤ G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ gbar * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + beta * C t ≤ D (t + 1))
    (hrhogk : gbar * k ≤ rho)
    (hbeta : gbar * k ^ 2 + (1 - rho) * k ≤ beta)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := by
  have hmain : ∀ t : ℕ, t ≤ T → k * C t ≤ D t := by
    intro t
    induction t with
    | zero => intro _; exact hcone0
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T := by
          rw [Finset.mem_range]; omega
        have htlte : t ∈ Finset.range (T + 1) := by
          rw [Finset.mem_range]; omega
        have hc := ih (by omega)
        have hDt : 0 ≤ D t := hD t htlte
        have hCt : 0 ≤ C t := hC t htlte
        have hGup := hup t htlt
        have hd := hdyn t htlt
        have hkey : rho * D t + beta * C t
            - k * (C t + gbar * D t)
            = (rho - gbar * k) * (D t - k * C t)
              + (beta - (gbar * k ^ 2 + (1 - rho) * k)) * C t := by
          field_simp
          ring
        have hnn1 : (0:ℝ) ≤ (rho - gbar * k) * (D t - k * C t) :=
          mul_nonneg (sub_nonneg.mpr hrhogk) (sub_nonneg.mpr hc)
        have hnn2 : (0:ℝ)
            ≤ (beta - (gbar * k ^ 2 + (1 - rho) * k)) * C t :=
          mul_nonneg (sub_nonneg.mpr hbeta) hCt
        -- k·G t ≤ k·γ̄·D t
        have hkle : k * G t ≤ k * (gbar * D t) :=
          mul_le_mul_of_nonneg_left hGup hk
        have hgoal : rho * D t + beta * C t - k * (C t + G t) ≥ 0 := by
          have := hnn1
          have := hnn2
          have hkey' : rho * D t + beta * C t
              - k * (C t + gbar * D t) ≥ 0 := by
            rw [hkey]; positivity
          linarith
        rw [hstep t htlt]
        linarith
  intro t ht
  exact hmain t (by rw [Finset.mem_range] at ht; omega)

/-- **Takeoff from per-step two-sided certificates**: the
full audit-§41 arc, chain side. If at every step the four
conversion factors clear the floor β (lower certificate),
the realized increment is pinned above by γ̄ (upper
certificate), the step law is exact and the cone dynamics
hold, capability grows exponentially with γ = β⁴κ:

  C₀(1 + β⁴κ·k)^T ≤ C_T.

The runtime measures the α's and the increment band; Lean
concludes takeoff. -/
theorem takeoff_from_certificate
    (C D G : ℕ → ℝ) (stages : ℕ → DisagreementStages)
    (T : ℕ) (beta kappa gbar rho cbeta k : ℝ)
    (hβ : 0 ≤ beta) (hκ : 0 ≤ kappa) (hk : 0 ≤ k)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hcert : ∀ t ∈ Finset.range T, beta ≤ (stages t).α_align
      ∧ beta ≤ (stages t).α_trunc
      ∧ beta ≤ (stages t).α_safe ∧ beta ≤ (stages t).α_cap)
    (hdiv : ∀ t ∈ Finset.range T,
      kappa * D t ≤ (stages t).E_raw)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hG : ∀ t ∈ Finset.range T,
      (stages t).G_cap = G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ gbar * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + cbeta * C t ≤ D (t + 1))
    (hrhogk : gbar * k ≤ rho)
    (hbeta' : gbar * k ^ 2 + (1 - rho) * k ≤ cbeta)
    (hcone0 : k * C 0 ≤ D 0) :
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T := by
  -- lower certificate: gamma·D t ≤ G t via chain_feeds_cone
  have hlow : ∀ t ∈ Finset.range T,
      (beta^4 * kappa) * D t ≤ G t := by
    intro t ht
    have hg := chain_feeds_cone (stages t) hβ hκ
      (hD t (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp ht))))
      (hcert t ht) (hdiv t ht)
    rw [hG t ht] at hg
    exact hg
  -- the cone holds under the two-sided certificate
  have hcone := cone_two_sided_certificate C D G
    (beta^4 * kappa) gbar rho cbeta k T hk hD hC
    hstep hlow hup hdyn hrhogk hbeta' hcone0
  -- takeoff via the lower-bounded step law
  have hmain : ∀ t : ℕ, t ≤ T →
      C 0 * (1 + (beta^4 * kappa) * k) ^ t ≤ C t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have htlt : t ∈ Finset.range T := by
          rw [Finset.mem_range]; omega
        have hci := ih (by omega)
        have hlo := hlow t htlt
        have hs := hstep t htlt
        have hgammak : 0 ≤ (beta^4 * kappa) * k :=
          mul_nonneg (mul_nonneg (by positivity) hκ) hk
        have hmul : (1:ℝ) ≤ 1 + (beta^4 * kappa) * k := by linarith
        have hcone' := hcone t (Finset.mem_range.mpr
          (Nat.lt_succ_of_lt (Finset.mem_range.mp htlt)))
        -- C0·X^(t+1) ≤ C t·X = C t + γk·C t ≤ C t + γ·D t
        have h1 : C 0 * (1 + (beta^4 * kappa) * k) ^ (t + 1)
            ≤ C t * (1 + (beta^4 * kappa) * k) := by
          have hexp : (1 + (beta^4 * kappa) * k) ^ (t + 1)
              = (1 + (beta^4 * kappa) * k) ^ t
                * (1 + (beta^4 * kappa) * k) := pow_succ _ _
          have hmono := mul_le_mul_of_nonneg_right hci
            (add_nonneg zero_le_one hgammak)
          rw [hexp]
          nlinarith [hmono]
        have h2 : C t * (1 + (beta^4 * kappa) * k)
            ≤ C t + (beta^4 * kappa) * D t := by
          have hkC : k * C t ≤ D t := hcone'
          have hgamma : 0 ≤ beta^4 * kappa :=
            mul_nonneg (by positivity) hκ
          have hmono : (beta^4 * kappa) * (k * C t)
              ≤ (beta^4 * kappa) * D t :=
            mul_le_mul_of_nonneg_left hkC hgamma
          have hrew : C t * (1 + (beta^4 * kappa) * k)
              = C t + (beta^4 * kappa) * (k * C t) := by ring
          rw [hrew]
          nlinarith [hmono]
        rw [hs]
        nlinarith [h1, h2]
  exact hmain T (le_refl T)

end Hagi.Growth
