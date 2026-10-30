import Mathlib
import Hagi.Prelude.Info

/-!
# RLHF: KL-контроль цели (источник №52)

Источник №52: Ziegler et al., "Fine-Tuning Language Models
from Human Preferences" (arXiv 1909.08593). RLHF-цель
U(π) = E_π[r] − β·KL(π‖π_ref): награда ограничена
KL-штрафом к референсной политике — дрейф контролируется
коэффициентом β.

Формализованное ядро (строгое):
- `rlhf_penalty_floor`: KL-штраф НИКОГДА не увеличивает
  цель: U ≤ E_π[r] при β ≥ 0 (KL ≥ 0 — композиция
  kl_nonneg): KL-контроль однонаправленно урезает
  reward-hacking.
-/

namespace Hagi.Model.RLHF

variable {V : Type*} [Fintype V]

/-- KL-штраф не увеличивает RLHF-цель. -/
theorem rlhf_penalty_floor (q p : V → ℝ) (r : V → ℝ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1) :
    (∑ v, q v * r v) - β * Hagi.Prelude.klDef q p
      ≤ ∑ v, q v * r v := by
  have hkl := Hagi.Prelude.kl_nonneg q p hq hp hsumq hsump
  have hpen : 0 ≤ β * Hagi.Prelude.klDef q p :=
    mul_nonneg hβ hkl
  linarith

end Hagi.Model.RLHF
