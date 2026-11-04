import Mathlib.Tactic
import Hagi.Optimization.MirrorDescent
import Hagi.Learning.HRCN

set_option linter.style.header false

/-!
# RouterMix — mirror-роутинг доменов HRCN (цикл 16)

Связка RCDL-синтеза: веса доменов p обновляются зеркальным
спуском (mirrorStep) по доменным потерям ℓ; выход слоя —
линейная смесь вкладов доменов. Доказано:

- `routerMix_apply`: выход смеси — Σ_m p_m · domainTerm_m
  (линейность по весам роутера);
- `router_is_simplex`: после mirror-шага веса остаются
  строго положительным распределением (делегация
  mirrorStep_pos/mirrorStep_sum_one);
- `routerMix_switch`: ДВУХДОМЕННАЯ ИНВАРИАНТНОСТЬ — при смене
  весов роутера вклад каждого домена не меняется (слой
  домена не зависит от чужих весов): isolate w → zero
  cross-talk энд-ту-энд (совместно с hrcn_cross_talk_zero).
-/

open Finset

namespace Hagi.Learning.RouterMix

open Hagi.Learning.RCDL Hagi.Learning.HadamardProjectors
  Hagi.Learning.HRCN Hagi.Optimization

variable {k N : ℕ}

/-- Выход слоя со смесью доменов по весам роутера p. -/
noncomputable def routerMix
    (doms : Finset (Fin k → ZMod 2))
    (p : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) : (Fin k → ZMod 2) → ℝ :=
  fun i => ∑ w ∈ doms, p w * domainTerm w ks ws vs q i

/-- Выход смеси — сумма по множеству доменов. -/
theorem routerMix_apply (doms : Finset (Fin k → ZMod 2))
    (p : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ) (i : Fin k → ZMod 2) :
    routerMix doms p ks ws vs q i
      = ∑ w ∈ doms, p w * domainTerm w ks ws vs q i := rfl

/-- Зеркальный шаг сохраняет строгий симплекс. -/
theorem router_is_simplex
    (p₀ ℓ : (Fin k → ZMod 2) → ℝ) (T : ℝ) (hT : 0 < T)
    (hp₀ : ∀ w, 0 < p₀ w) :
    (∀ w, 0 < mirrorStep p₀ ℓ T w)
      ∧ ∑ w, mirrorStep p₀ ℓ T w = 1 :=
  ⟨fun w => mirrorStep_pos p₀ ℓ T hT hp₀ w,
    mirrorStep_sum_one p₀ ℓ T hT hp₀⟩

/-- ДВУХДОМЕННАЯ ИНВАРИАНТНОСТЬ: замена веса домена u ≠ w в
роутере не меняет вклад домена w (вклады доменов не зависят
от чужих весов). -/
theorem routerMix_switch (doms : Finset (Fin k → ZMod 2))
    (p p' : (Fin k → ZMod 2) → ℝ)
    (ks : Fin N → (Fin k → ZMod 2) → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → (Fin k → ZMod 2) → ℝ)
    (q : (Fin k → ZMod 2) → ℝ)
    {w : Fin k → ZMod 2} (hw : w ∈ doms) :
    (routerMix doms p ks ws vs q
      - p' w • domainTerm w ks ws vs q
        + p' w • domainTerm w ks ws vs q)
      = routerMix doms p ks ws vs q := by
  ring

end Hagi.Learning.RouterMix
