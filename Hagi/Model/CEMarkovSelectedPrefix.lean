import Hagi.Model.CEMarkovMaximalConfidence

/-! Direct finite-prefix algebra for a bounded selected raw-CE gap. -/

set_option relaxedAutoImplicit false

namespace Hagi.Model.CEMarkovSelectedPrefix

open Hagi.Model.CEHeldout
open Hagi.Probability

/-- On the guarded prefix event, a strict observed raw gap gives a strict
conditional-mean gap for the explicitly selected bounded prefix. -/
theorem raw_bank_selected_prefix_conditional_ce_gap_pos_of_good
    {G m : ℕ} {Label : Type} [Fintype Label] [Nonempty Label]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix Label (Fin (5 * G)) ℝ)
    (K : ℕ → ((Fin m → JointCode G) × Label) →
      PMF ((Fin m → JointCode G) × Label))
    (T : ℕ) (b : Fin m)
    (σ : History ((Fin m → JointCode G) × Label) T → Fin m)
    (τ : History ((Fin m → JointCode G) × Label) T → ℕ)
    (r V : ℝ) (ω : History ((Fin m → JointCode G) × Label) T)
    (hGood : ∀ i : Fin m, ∀ j ≤ T,
      historyCounter (fun k a => pmfMean (K k a)
        (fun next => (Hagi.ceOneHot next.2
          (ceLogits X (decodeJoint e (a.1 i))) -
            pmfMean (K k a) (fun next => Hagi.ceOneHot next.2
              (ceLogits X (decodeJoint e (a.1 i))))) ^ 2))
          T j ω ≤ V →
        |historyAdditive (fun k a next =>
          Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i))) -
            pmfMean (K k a) (fun next => Hagi.ceOneHot next.2
              (ceLogits X (decodeJoint e (a.1 i))))) T j ω| < r)
    (hτ : ∀ ω, τ ω ≤ T)
    (hbv : historyCounter (fun k a => pmfMean (K k a)
      (fun next => (Hagi.ceOneHot next.2
        (ceLogits X (decodeJoint e (a.1 b))) -
          pmfMean (K k a) (fun next => Hagi.ceOneHot next.2
            (ceLogits X (decodeJoint e (a.1 b))))) ^ 2))
        T (τ ω) ω ≤ V)
    (hσv : historyCounter (fun k a => pmfMean (K k a)
      (fun next => (Hagi.ceOneHot next.2
        (ceLogits X (decodeJoint e (a.1 (σ ω)))) -
          pmfMean (K k a) (fun next => Hagi.ceOneHot next.2
            (ceLogits X (decodeJoint e (a.1 (σ ω)))))) ^ 2))
        T (τ ω) ω ≤ V)
    (hobs : 2 * r <
      historyAdditive (fun _k a next => Hagi.ceOneHot next.2
        (ceLogits X (decodeJoint e (a.1 b)))) T (τ ω) ω -
      historyAdditive (fun _k a next => Hagi.ceOneHot next.2
        (ceLogits X (decodeJoint e (a.1 (σ ω))))) T (τ ω) ω) :
    0 < historyAdditive (fun k a _ => pmfMean (K k a)
      (fun next => Hagi.ceOneHot next.2
        (ceLogits X (decodeJoint e (a.1 b))))) T (τ ω) ω -
      historyAdditive (fun k a _ => pmfMean (K k a)
        (fun next => Hagi.ceOneHot next.2
          (ceLogits X (decodeJoint e (a.1 (σ ω)))))) T (τ ω) ω := by
  classical
  let F : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i _ a next => Hagi.ceOneHot next.2 (ceLogits X (decodeJoint e (a.1 i)))
  let μ : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (F i k a)
  let g : Fin m → ℕ → ((Fin m → JointCode G) × Label) →
      ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a next => F i k a next - μ i k a
  let v : Fin m → ℕ → ((Fin m → JointCode G) × Label) → ℝ :=
    fun i k a => pmfMean (K k a) (fun next => (g i k a next) ^ 2)
  have hgood (i : Fin m) :
      historyCounter (v i) T (τ ω) ω ≤ V →
        |historyAdditive (g i) T (τ ω) ω| < r := by
    intro hi
    exact hGood i (τ ω) (hτ ω) (by simpa only [v, g, μ, F] using hi)
  have hbv' : historyCounter (v b) T (τ ω) ω ≤ V := by
    simpa only [v, g, μ, F] using hbv
  have hσv' : historyCounter (v (σ ω)) T (τ ω) ω ≤ V := by
    simpa only [v, g, μ, F] using hσv
  have hbc := abs_lt.mp (hgood b hbv')
  have hσc := abs_lt.mp (hgood (σ ω) hσv')
  have hsplit (i : Fin m) :
      historyAdditive (fun k a next => F i (k + 1) a next) T (τ ω) ω =
        historyAdditive (g i) T (τ ω) ω +
          historyAdditive (fun k a _ => μ i k a) T (τ ω) ω := by
    unfold historyAdditive
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [g, F]
    ring
  have hobs' : 2 * r <
      historyAdditive (fun k a next => F b (k + 1) a next) T (τ ω) ω -
        historyAdditive (fun k a next => F (σ ω) (k + 1) a next) T (τ ω) ω := by
    simpa only [F] using hobs
  change 0 < historyAdditive (fun k a _ => μ b k a) T (τ ω) ω -
    historyAdditive (fun k a _ => μ (σ ω) k a) T (τ ω) ω
  rw [hsplit b, hsplit (σ ω)] at hobs'
  linarith

end Hagi.Model.CEMarkovSelectedPrefix
