import Hagi.Prelude.Info

namespace Hagi.Numerics

open Hagi.Prelude Finset

/-!
Формализация точной математики arXiv 2610.31642v1
"A Fix for Softmax and Cross-Entropy":
(1) градиент кросс-энтропии g = q − p суммируется в ноль;
(2) маржа-форма: потери жёсткой CE = softplus(−m),
остаточная сумма Σ_{j≠t} e^{z_j−z_t} = e^{−m};
(3) равновесие маржи AdamW: g/(|g|+ε)+λθ=0 ⟹
|g| = λ|θ|ε/(1−λ|θ|) — маржа насыщается на m*≈log(1/ε);
(4) нулевой градиент дистилляции при z_S = z_T.
-/

/-- ГРАДИЕНТ CE СУММИРУЕТСЯ В НОЛЬ: точный градиент
кросс-энтропии g = q − p (softmax минус цель) суммируется
в ноль, т.к. оба распределения нормированы — базовое
свойство, нарушаемое Softmax Collapse в плавающей точке
(там обнуляется только целевой компонент, сумма > 0). -/
theorem ce_grad_sum_zero {V : Type*} [Fintype V] [Nonempty V]
    (z : V → ℝ) (p : V → ℝ) (hp1 : ∑ v, p v = 1) :
    (∑ v, (softDef z v - p v)) = 0 := by
  have hsplit : (∑ v, (softDef z v - p v))
      = (∑ v, softDef z v) - (∑ v, p v) :=
    Finset.sum_sub_distrib (fun v => softDef z v) (fun v => p v)
  rw [hsplit, softDef_sum_one, hp1, sub_self]

/-- МАРЖА (logit margin, eq.2): m = z_t − log Σ_{j≠t} e^{z_j}
— насколько целевой логит превышает log-sum-exp остальных. -/
noncomputable def logitMargin {V : Type*} [Fintype V] [DecidableEq V]
    (z : V → ℝ) (t : V) : ℝ :=
  z t - Real.log (∑ j ∈ Finset.univ.erase t, Real.exp (z j))

/-- ОСТАТОЧНАЯ СУММА РАВНА e^{−m}: Σ_{j≠t} e^{z_j−z_t} = e^{−m}
— нормировка фиксированного CE (знаменатель 1+e^{−m},
нетождественное обнуление целевого слота исключено). -/
theorem margin_rest_sum {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (z : V → ℝ) (t : V)
    (hrest : (Finset.univ.erase t).Nonempty) :
    (∑ j ∈ Finset.univ.erase t, Real.exp (z j - z t))
      = Real.exp (-(logitMargin z t)) := by
  have hrestpos : (0:ℝ)
      < ∑ j ∈ Finset.univ.erase t, Real.exp (z j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) hrest
  calc (∑ j ∈ Finset.univ.erase t, Real.exp (z j - z t))
      = ∑ j ∈ Finset.univ.erase t,
          Real.exp (z j) / Real.exp (z t) :=
        Finset.sum_congr rfl (fun j _ => Real.exp_sub _ _)
    _ = (∑ j ∈ Finset.univ.erase t, Real.exp (z j))
        / Real.exp (z t) := (Finset.sum_div _ _ _).symm
    _ = Real.exp (Real.log
        (∑ j ∈ Finset.univ.erase t, Real.exp (z j)))
        / Real.exp (z t) := by rw [Real.exp_log hrestpos]
    _ = Real.exp (Real.log
        (∑ j ∈ Finset.univ.erase t, Real.exp (z j)) - z t) :=
        (Real.exp_sub _ _).symm
    _ = Real.exp (-(logitMargin z t)) := by
        unfold logitMargin
        rw [neg_sub]

/-- ПОТЕРИ ЖЁСТКОЙ CE ПО МАРЖЕ: L = softplus(−m):
log Σ_v e^{z_v} − z_t = log(1 + e^{−m}) — потери зависят
только от маржи; фиксированный CE (eq.6) сохраняет
точность за пределами precision cliff. -/
theorem ce_loss_margin {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (z : V → ℝ) (t : V)
    (hrest : (Finset.univ.erase t).Nonempty) :
    Real.log (∑ v, Real.exp (z v))
      - Real.log (Real.exp (z t))
      = Real.log (1 + Real.exp (-(logitMargin z t))) := by
  -- остаток: Σ_{j≠t} e^{z_j} = e^{z_t}·e^{−m}
  have hsum : (∑ j ∈ Finset.univ.erase t, Real.exp (z j))
      = Real.exp (z t) * Real.exp (-(logitMargin z t)) := by
    rw [← margin_rest_sum z t hrest, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← Real.exp_add]
    congr 1
    ring
  -- разложение полной суммы: e^{z_t}(1 + e^{−m})
  have hsplit : (∑ v, Real.exp (z v))
      = Real.exp (z t) * (1
        + Real.exp (-(logitMargin z t))) := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset V)
      (fun v => Real.exp (z v)) (Finset.mem_univ t), add_comm,
      mul_add, mul_one, hsum]
  have h1m : (0:ℝ) < Real.exp (-(logitMargin z t)) :=
    Real.exp_pos _
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne'
    (ne_of_gt (add_pos one_pos h1m)), Real.log_exp]
  ring

/-- РАВНОВЕСИЕ МАРЖИ ADAMW: стационарная точка AdamW с
weight decay λ: g/(|g|+ε) + λθ = 0 ⟹ точная величина
градиента |g| = λ|θ|ε/(1−λ|θ|) при λ|θ| < 1 — нормированный
шаг уравновешивает decay; при экспоненциальном убывании
|g| ∝ e^{−m} маржа насыщается на m* ≈ log(1/ε)
(§5, eq.10–11). -/
theorem adamw_equilibrium_magnitude (g θ ε lam : ℝ)
    (hε : 0 < ε) (hlam : 0 < lam) (hθ : 0 < |θ|)
    (hlamθ : lam * |θ| < 1)
    (hstat : g / (|g| + ε) + lam * θ = 0) :
    |g| = lam * |θ| * ε / (1 - lam * |θ|) := by
  have h0 : g / (|g| + ε) = -(lam * θ) := by linarith
  have hden : (0:ℝ) < |g| + ε := by
    have hg := abs_nonneg g
    linarith
  have habs : |g| / (|g| + ε) = lam * |θ| := by
    have h1 : |g / (|g| + ε)| = |lam * θ| := by rw [h0, abs_neg]
    rw [abs_div, abs_of_pos hden, abs_mul,
      abs_of_pos hlam] at h1
    exact h1
  have hkey : |g| = lam * |θ| * (|g| + ε) := by
    rw [← habs, div_mul_cancel₀ _ hden.ne']
  have hgoal : |g| * (1 - lam * |θ|) = lam * |θ| * ε := by
    nlinarith [hkey, hlamθ]
  have hne : (1:ℝ) - lam * |θ| ≠ 0 := by
    intro hc
    have := hlamθ
    linarith
  rw [eq_div_iff hne]
  exact hgoal

/-- НУЛЕВОЙ ГРАДИЕНТ ДИСТИЛЛЯЦИИ ПРИ СОВПАДЕНИИ ЛОГИТОВ:
если студенческие логиты равны учительским, точный градиент
soft-target CE q − p равен нулю тождественно — Softmax
Cancellation в точной арифметике не возникает, студент не
дрейфует от учителя (§3, §7). -/
theorem distill_grad_self_zero {V : Type*} [Fintype V] [Nonempty V]
    (zS zT : V → ℝ) (heq : zS = zT) (v : V) :
    softDef zS v - softDef zT v = 0 := by
  rw [heq, sub_self]

end Hagi.Numerics
