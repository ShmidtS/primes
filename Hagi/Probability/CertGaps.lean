/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.GibbsInfoCore
import Hagi.Probability.GibbsCooling
set_option linter.style.header false

open Finset Real

open Finset Real in
/-- **Safety of a lower-bound entropy proxy (R463)**:
if the entropy estimate Ĥ never exceeds the true h,
then the surrogate free energy E − Ĥ majorizes the
true E − h, and the surprise certificate s ≤ E − h is
preserved by construction. -/
theorem proxy_cert_preserved (E h hhat s : ℝ)
    (hlow : hhat ≤ h) (hcert : s ≤ E - h) :
    s ≤ E - hhat := by
  linarith

/-- **Loss of the certificate for an upper-bound
entropy proxy (R463)**: if the proxy strictly exceeds
the true entropy and the true free energy exactly
meets the certificate, the surrogate free energy
falls strictly below it — the AIF bound is not
guaranteed (arXiv 2607.13612, Prop 2(ii)). -/
theorem proxy_cert_lost (E h hhat s : ℝ)
    (hup : h < hhat) (hexact : E - h = s) :
    E - hhat < s := by
  linarith

/-- **Gibbs certificate bridge (R463)**: at the
Gibbs equilibrium the surprise certificate
s ≤ F = −T·ln Z (R462 identity) is preserved by any
lower-bound entropy proxy Ĥ ≤ T·S_γ. -/
theorem gibbs_cert_bridge {V : Type*} [Fintype V]
    [DecidableEq V] [Nonempty V] (E : V → ℝ) (T : ℝ)
    (hT : 0 < T) (hhat s : ℝ)
    (hlow : hhat ≤ T * (-(∑ v : V, (Real.exp (-(E v)/T)
      / ∑ v : V, Real.exp (-(E v)/T))
      * Real.log (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)))))
    (hcert : s ≤ -T * Real.log (∑ v : V,
      Real.exp (-(E v)/T))) :
    s ≤ (∑ v : V, (Real.exp (-(E v)/T)
        / ∑ v : V, Real.exp (-(E v)/T)) * E v) - hhat := by
  have hid := gibbs_free_energy_identity E T hT
  linarith

open Real in
/-- **Three-source gap decomposition (R464)**:
the surrogate-true free-energy gap decomposes
exactly into prior-miscalibration, estimator bias
and optimization slack (arXiv 2607.13612, Prop 1). -/
theorem gap_decomposition (F Fhat g1 g2 g3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3) :
    abs (Fhat - F) = abs (g1 + g2 + g3) := by
  rw [hgap]

/-- **Estimator bias is nonpositive for a lower-bound
entropy proxy (R464)**: Gap II = Ĥ − h ≤ 0 whenever
the proxy underestimates the entropy. -/
theorem gapII_nonpos (h hhat : ℝ) (hlow : hhat ≤ h) :
    hhat - h ≤ 0 := by
  linarith

/-- **Graceful degradation, linear slack (R464)**:
if the gap sources obey |g1| ≤ c1, |g2| ≤ c2,
|g3| ≤ c3 then the surrogate-true gap obeys the
triangle bound (arXiv 2607.13612, Cor 2(i)). -/
theorem gap_graceful (F Fhat g1 g2 g3 c1 c2 c3 : ℝ)
    (hgap : Fhat - F = g1 + g2 + g3)
    (h1 : abs g1 ≤ c1) (h2 : abs g2 ≤ c2)
    (h3 : abs g3 ≤ c3) :
    abs (Fhat - F) ≤ c1 + c2 + c3 := by
  rw [hgap, add_assoc]
  calc abs (g1 + (g2 + g3))
      ≤ abs g1 + abs (g2 + g3) :=
        abs_add_le g1 (g2 + g3)
    _ ≤ abs g1 + (abs g2 + abs g3) := by
        have := abs_add_le g2 g3
        linarith
    _ ≤ c1 + c2 + c3 := by
        linarith [h1, h2, h3]

open Real in
/-- **Autoregressive error compounding (R465)**:
if the predictor is L-Lipschitz so each step maps
e_t ↦ e_{t+1} ≤ L·e_t, the H-step executed error
compounds geometrically (arXiv 2607.13612, Thm 2(ii),
L^{2H}-structure in the squared metric). -/
theorem compounding_bound (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, e (t+1) ≤ L * e t)
    (n : ℕ) : e n ≤ L^n * e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := he n
      calc e (n+1) ≤ L * e n := h1
        _ ≤ L * (L^n * e 0) := by
            exact mul_le_mul_of_nonneg_left ih hL
        _ = L^(n+1) * e 0 := by
            rw [pow_succ]; ring

/-- **Squared-metric compounding is L^(2H) (R465)**:
in the squared metric the same step recursion gives
e_H^2 ≤ (L^2)^H·e_0^2 — the O(L^(2H)) term of
arXiv 2607.13612, Thm 2(ii). -/
theorem compounding_sq (L : ℝ) (hL : 0 ≤ L)
    (e : ℕ → ℝ) (he : ∀ t, 0 ≤ e t)
    (hsq : ∀ t, e (t+1)^2 ≤ (L^2) * e t^2)
    (n : ℕ) : e n^2 ≤ (L^2)^n * e 0^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := hsq n
      have hL2 : (0:ℝ) ≤ L^2 := by nlinarith [hL]
      calc e (n+1)^2 ≤ L^2 * e n^2 := h1
        _ ≤ L^2 * ((L^2)^n * e 0^2) := by
            exact mul_le_mul_of_nonneg_left ih hL2
        _ = (L^2)^(n+1) * e 0^2 := by
            rw [pow_succ]; ring

open Finset Real in
/-- **Mutual information is nonnegative (R466)**:
I(X;Y) = KL(ρ ‖ μ₁×μ₂) ≥ 0 — the information a
joint distribution carries about the dependence
of its marginals never decreases below zero
(direct R447 application; equivalent to R459). -/
theorem mutual_info_nonneg {V W : Type*} [Fintype V]
    [Fintype W] [Nonempty V] [Nonempty W]
    [DecidableEq V] [DecidableEq W]
    (ρ : V × W → ℝ)
    (hρ : ∀ p, 0 < ρ p) (hρ1 : ∑ p : V × W, ρ p = 1) :
    (0:ℝ) ≤ ∑ p : V × W, ρ p * Real.log
      (ρ p / ((∑ w : W, ρ (p.1, w))
        * (∑ v : V, ρ (v, p.2)))) := by
  set μ₁ : V → ℝ := fun v => ∑ w : W, ρ (v, w) with hμ₁
  set μ₂ : W → ℝ := fun w => ∑ v : V, ρ (v, w) with hμ₂
  have hμ₁pos : ∀ v, 0 < μ₁ v := by
    intro v
    have := Finset.sum_pos (fun w _ => hρ (v, w))
      ⟨Classical.arbitrary W, Finset.mem_univ _⟩
    rw [hμ₁]; exact this
  have hμ₂pos : ∀ w, 0 < μ₂ w := by
    intro w
    have := Finset.sum_pos (fun v _ => hρ (v, w))
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    rw [hμ₂]; exact this
  set γ : V × W → ℝ := fun p => μ₁ p.1 * μ₂ p.2 with hγ
  have hγpos : ∀ p, 0 < γ p := fun p => by
    rw [hγ]; exact mul_pos (hμ₁pos p.1) (hμ₂pos p.2)
  have hμ₁s : ∑ v : V, μ₁ v = 1 := by
    rw [hμ₁, ← Fintype.sum_prod_type]; exact hρ1
  have hμ₂s : ∑ w : W, μ₂ w = 1 := by
    rw [hμ₂, Finset.sum_comm, ← Fintype.sum_prod_type]; exact hρ1
  have hγ1 : ∑ p : V × W, γ p = 1 := by
    show ∑ p : V × W, μ₁ p.1 * μ₂ p.2 = 1
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v : V,
        ∑ w : W, μ₁ (v, w).1 * μ₂ (v, w).2 = μ₁ v := by
      intro v
      simp only []
      rw [← Finset.mul_sum, hμ₂s, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hrow v)]
    exact hμ₁s
  -- the KL expression is definitionally the one in R447
  have hKL := finite_kl_nonneg ρ γ hρ hρ1 hγpos hγ1
  exact hKL

/-- **EFE ceiling (R466)**: expected free energy
decomposes as G = P − I with pragmatic value P and
epistemic (information) part I ≥ 0; hence the EFE
never exceeds the pragmatic value — the
state-epistemic gap is exactly the mutual
information (arXiv 2607.13612, Prop 6 structure). -/
theorem efe_ceiling (G P I : ℝ)
    (hdecomp : G = P - I) (hI : 0 ≤ I) :
    G ≤ P := by
  linarith

open Real in
/-- **Amortised EFE policy guarantee (R467)**: if the
learned surrogate Ĝ uniformly approximates the true
expected free energy within slack c, the policy
minimising Ĝ executes within 2c of the optimum
(arXiv 2607.13612, Prop 7 structure). -/
theorem amortized_policy_bound {Pol : Type*}
    (Ghat G : Pol → ℝ) (pih pis : Pol) (c : ℝ)
    (happrox : ∀ pi, abs (Ghat pi - G pi) ≤ c)
    (hmin : ∀ pi, Ghat pih ≤ Ghat pi) :
    G pih ≤ G pis + 2 * c := by
  have hA : ∀ pi : Pol, Ghat pi - G pi ≤ c :=
    fun pi => (abs_le.mp (happrox pi)).2
  have hB : ∀ pi : Pol, G pi - Ghat pi ≤ c :=
    fun pi => by
      have h := abs_le.mp (happrox pi)
      linarith
  have h3 := hmin pis
  linarith [hA pih, hA pis, hB pih]

