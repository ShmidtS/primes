import Hagi.Model.BatchCEDescent

/-!
# BatchCEDescentMgdaCode

Correspondence bridge from the HAGI_v2 `mgda_weights` Frank-Wolfe solver
(`hagi/selfmodel.py:35-60` at `1ae924e`, wave 254) to the minimum-norm
point `batchGradientMinimizer` of the raw residual-gradient convex hull.

The code normalizes the task gradients (`G = g / (‖g‖ + 1e-12)`), starts
from the uniform simplex point and runs at most 200 Frank-Wolfe steps
with step `γ = 2 / (2 + t)`.  It stops as soon as
`min_j ⟪G_j, d⟫ ≥ ‖d‖^2 - 1e-16` for the mixture `d = ∑ α_j • G_j`
(selfmodel.py:48-50); the weights are then clamped and renormalized
(selfmodel.py:55-60), which is the identity whenever the loop was
entered through the stop test.

* `MgdaStationary v α ε` is that stopping test at tolerance `ε`.
* `mgda_norm_sq_le_of_stationary`: an `ε`-stationary mixture is `2ε`
  suboptimal in squared norm against every hull point (Young's inequality).
* `mgda_eq_of_stationary`: at `ε = 0` the mixture IS the minimum-norm
  point (uniqueness via the existing `Hagi.Step.eq_of_mem_of_forall_norm_le`).
* `batchGradientMinimizer_eq_mgdaCodeDirection_of_stationary`: the canon
  instantiation on `batchResidualGradient`.

Honest limits (STATUS C639 card): the code solves the problem on
NORMALIZED gradients, so the canon statement applies verbatim only when
all task gradients have equal norm (e.g. the test pairs); for unequal
norms the code's `d` is the min-norm point of the normalized hull, not
of the raw hull.  A run that exhausts 200 iterations without the stop
test yields simplex weights only - no certificate follows from this
module; the `2ε` bound is the only approximate statement.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.BatchCEDescent

open Set InnerProductSpace

variable {d K : ℕ}

/-- The task-gradient mixture the code forms from its returned weights. -/
noncomputable def mgdaCodeDirection (v : Fin K → EuclideanSpace ℝ (Fin d))
    (α : Fin K → ℝ) : EuclideanSpace ℝ (Fin d) :=
  ∑ j, α j • v j

/-- Weights lie on the simplex: nonnegative and summing to one. -/
def SimplexWeights (α : Fin K → ℝ) : Prop :=
  (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1

/-- The code's Frank-Wolfe stopping test with tolerance `ε`: every vertex
has at least the mixture's squared norm as alignment. -/
def MgdaStationary (v : Fin K → EuclideanSpace ℝ (Fin d))
    (α : Fin K → ℝ) (ε : ℝ) : Prop :=
  ∀ j, ‖mgdaCodeDirection v α‖ ^ 2 - ε ≤ ⟪v j, mgdaCodeDirection v α⟫_ℝ

/-- Every point of the finite hull is a full convex combination of the
vertices, and its alignment with any vector is the weighted average. -/
theorem inner_le_of_mem_convexHull_range [Nonempty (Fin K)]
    (v : Fin K → EuclideanSpace ℝ (Fin d))
    {c : EuclideanSpace ℝ (Fin d)}
    (hc : c ∈ convexHull ℝ (Set.range v)) (D : EuclideanSpace ℝ (Fin d))
    {m : ℝ} (hm : ∀ j, m ≤ ⟪v j, D⟫_ℝ) : m ≤ ⟪c, D⟫_ℝ := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hc
  obtain ⟨s, w, hw₀, hw₁, hc⟩ := hc
  have hc' : c = mgdaCodeDirection v (fun j => if j ∈ s then w j else 0) := by
    classical
    rw [← hc, Finset.affineCombination_eq_linear_combination _ _ _ hw₁, mgdaCodeDirection]
    simp
  have hβ₀ : ∀ j, 0 ≤ (if j ∈ s then w j else 0) :=
    fun j => by
      split_ifs with h
      · exact hw₀ j h
      · exact le_rfl
  have hβ₁ : ∑ j, (if j ∈ s then w j else 0) = 1 := by
    classical
    simpa using hw₁
  subst hc'
  classical
  simp only [mgdaCodeDirection, sum_inner]
  calc
    m = ∑ j, (if j ∈ s then w j else 0) * m := by rw [← Finset.sum_mul, hβ₁, one_mul]
    _ ≤ ∑ j, (if j ∈ s then w j else 0) * ⟪v j, D⟫_ℝ :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hm j) (hβ₀ j)
    _ = ∑ j, ⟪(if j ∈ s then w j else 0) • v j, D⟫_ℝ := by
      exact Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_left]

/-- A simplex mixture lies in the convex hull of its vertices. -/
theorem mgdaCodeDirection_mem_convexHull [Nonempty (Fin K)]
    (v : Fin K → EuclideanSpace ℝ (Fin d)) (α : Fin K → ℝ)
    (hα : SimplexWeights α) :
    mgdaCodeDirection v α ∈ convexHull ℝ (Set.range v) := by
  rw [mgdaCodeDirection]
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => hα.1 j) (by simpa using hα.2)
    (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)

/-- A stationary mixture is a minimum-norm hull point: any hull point `c`
is at least as aligned with the mixture as the least-aligned vertex, and
Young's inequality turns alignment into squared norm. -/
theorem mgda_norm_sq_le_of_stationary [Nonempty (Fin K)]
    (v : Fin K → EuclideanSpace ℝ (Fin d)) (α : Fin K → ℝ)
    (hα : SimplexWeights α) {ε : ℝ} (hstat : MgdaStationary v α ε)
    {c : EuclideanSpace ℝ (Fin d)}
    (hc : c ∈ convexHull ℝ (Set.range v)) :
    ‖mgdaCodeDirection v α‖ ^ 2 - 2 * ε ≤ ‖c‖ ^ 2 := by
  have hmem := mgdaCodeDirection_mem_convexHull v α hα
  have hcD : ‖mgdaCodeDirection v α‖ ^ 2 - ε ≤ ⟪c, mgdaCodeDirection v α⟫_ℝ :=
    inner_le_of_mem_convexHull_range v hc _ hstat
  have hDc : ‖mgdaCodeDirection v α‖ ^ 2 - ε ≤
      ⟪mgdaCodeDirection v α, c⟫_ℝ := by
    rw [real_inner_comm]
    exact hcD
  have hyoung : ⟪mgdaCodeDirection v α, c⟫_ℝ ≤
      (‖mgdaCodeDirection v α‖ ^ 2 + ‖c‖ ^ 2) / 2 := by
    have h := real_inner_le_norm (mgdaCodeDirection v α) c
    have hsq := sq_nonneg (‖mgdaCodeDirection v α‖ - ‖c‖)
    have hs2 := sq_nonneg (‖mgdaCodeDirection v α‖ + ‖c‖)
    linarith [h, hsq, hs2]
  have hy := (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mp hyoung
  linarith [hDc, hy]

/-- The code's exact stopping test (zero tolerance) makes the mixture the
canon minimum-norm point. -/
theorem mgda_eq_of_stationary [Nonempty (Fin K)]
    (v : Fin K → EuclideanSpace ℝ (Fin d)) (α : Fin K → ℝ)
    (hα : SimplexWeights α)
    (hstat : MgdaStationary v α 0)
    {ω : EuclideanSpace ℝ (Fin d)}
    (hω : ω ∈ convexHull ℝ (Set.range v))
    (hmin : ∀ c ∈ convexHull ℝ (Set.range v), ‖ω‖ ≤ ‖c‖) :
    mgdaCodeDirection v α = ω := by
  have hle : ∀ c ∈ convexHull ℝ (Set.range v),
      ‖mgdaCodeDirection v α‖ ≤ ‖c‖ := by
    intro c hc
    have h := mgda_norm_sq_le_of_stationary v α hα hstat hc
    have hnn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    have hnn' : 0 ≤ ‖mgdaCodeDirection v α‖ ^ 2 := sq_nonneg _
    exact le_of_sq_le_sq (by nlinarith [h]) (norm_nonneg c)
  exact Hagi.Step.eq_of_mem_of_forall_norm_le (convex_convexHull ℝ _)
    (mgdaCodeDirection_mem_convexHull v α hα) hω hle hmin

/-- Instantiation at the canon: weights whose normalized-vertex mixture
passes the code's exact stop reproduce `batchGradientMinimizer`. -/
theorem batchGradientMinimizer_eq_mgdaCodeDirection_of_stationary
    {V : Type} [Fintype V] {B n : ℕ} [Nonempty (Fin B)]
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) (α : Fin B → ℝ) (hα : SimplexWeights α)
    (hstat : MgdaStationary (fun b => batchResidualGradient (X b) θ (y b)) α 0) :
    mgdaCodeDirection (fun b => batchResidualGradient (X b) θ (y b)) α =
      batchGradientMinimizer X θ y :=
  mgda_eq_of_stationary _ α hα hstat (batchGradientMinimizer_mem X θ y)
    (fun c hc => batchGradientMinimizer_norm_le X θ y hc)

end Hagi.Model.BatchCEDescent

