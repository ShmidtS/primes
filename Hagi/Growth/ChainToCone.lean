/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.DisagreementChain

/-!
# ChainToCone — from the disagreement chain to the growth cone

* `chain_feeds_cone`: if each conversion factor of `s` is at least
  `β` and `κ * D ≤ s.E_raw` (all with `0 ≤ β`, `0 ≤ κ`, `0 ≤ D`),
  then `(β^4 * κ) * D ≤ s.G_cap`.
* `cone_two_sided_certificate`: if for all steps `gamma * D t ≤ G t ≤
  gbar * D t`, the step law `C (t+1) = C t + G t` holds, and the cone
  dynamics `rho * D t + beta * C t ≤ D (t+1)` hold with `gbar * k ≤ rho`
  and `gbar * k^2 + (1 - rho) * k ≤ beta`, then the cone invariant
  `k * C t ≤ D t` is preserved up to `T`.
  A one-sided lower certificate alone is not sufficient for this
  proof (the upper bound `G t ≤ gbar * D t` is a hypothesis).
* `takeoff_from_certificate`: combining per-step lower certificates
  via `chain_feeds_cone` with `cone_two_sided_certificate` yields
  `C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- If each conversion factor of `s` is at least `β`, `0 ≤ κ`,
`0 ≤ D`, and `κ * D ≤ s.E_raw`, then `(β^4 * κ) * D ≤ s.G_cap`. -/
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

/-- Cone invariant preservation under a two-sided certified
step: assuming `gamma * D t ≤ G t ≤ gbar * D t` for each step,
the exact step law `C (t + 1) = C t + G t`, nonnegativity of
`C` and `D`, the cone dynamics `rho * D t + beta * C t ≤ D (t+1)`,
and the parameter conditions `gbar * k ≤ rho`,
`gbar * k ^ 2 + (1 - rho) * k ≤ beta`, the invariant
`k * C t ≤ D t` (assumed at `t = 0`) is preserved for all
`t ≤ T`. -/
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

/-- Takeoff from per-step certificates: if at every step the
conversion factors of `stages t` are at least `beta`,
`kappa * D t ≤ (stages t).E_raw`, `(stages t).G_cap = G t`,
the increments satisfy `G t ≤ gbar * D t`, and the hypotheses
of `cone_two_sided_certificate` hold, then
`C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`. -/
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
