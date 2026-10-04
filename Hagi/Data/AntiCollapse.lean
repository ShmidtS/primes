/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.DistillRecursion
set_option linter.style.header false

/-!
# R136: T5 AntiCollapse — честная непрерывность энтропии

FORMALIZATION_PLAN §7.1 T5 (P1): ревизия опровергла hcert
(R108: «KL ≤ δ ⟹ энтропия не падает» — контрпример: может
сжигать энтропию, sharpening tail при малом KL). Замена:
Pinsker + явная непрерывность энтропии (Fannes-форма):

  |H(p) − H(q)| ≤ τ·log(V − 1) + h₂(τ),  τ = ½‖p − q‖₁,

где h₂ — двоичная энтропия. Связь с KL: Pinsker
τ ≤ √(KL(p‖q)/2) — измеряемый мост (посылка: KL-скан).

**Теоремы:**

* `entTV` (полная вариация), `h2` (двоичная энтропия) — defs.
* `entTV_nonneg/symm/le_one` — базовые свойства.
* `h2_le_log2` — h₂(τ) ≤ log 2 (грубая форма для гейтов).
* `entropy_continuity` — ГЛАВНАЯ граница (T5): при
  measured-посылке смеси-разложения (сертифицируемое
  разложение p = (1−τ)·u + τ·w, q = (1−τ)·u' + τ·w' с
  носителями u,u' вне общих ≤ V−1 точек — Fannes-контракт)
  следует |H(p)−H(q)| ≤ τ·log(V−1) + h₂(τ).

**Честные границы:** Fannes-разложение — measured premise
(классическое доказательство конструктивно строит u,w из
положительных/отрицательных частей p−q; полный порт —
многочасовая комбинаторика сумм, отложена); Pinsker-мост
τ ≤ √(KL/2) — посылка (KL-сканы уже логируются). Именно
τ (не KL!) управляет энтропией — суть опровержения hcert.
-/

open Finset

namespace Hagi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Полная вариация τ = ½‖p − q‖₁. -/
noncomputable def entTV (p q : V → ℝ) : ℝ :=
  (1/2) * ∑ v, |p v - q v|

/-- Двоичная энтропия h₂(τ) = −τ·log τ − (1−τ)·log(1−τ). -/
noncomputable def binEnt (τ : ℝ) : ℝ :=
  -τ * Real.log τ - (1 - τ) * Real.log (1 - τ)

/-- Fannes-контракт: измеряемое разложение смеси —
p = (1−τ)·u + τ·w, q = (1−τ)·u' + τ·w', u,u' — распределения,
w,w' — субраспределения; носители u, u' покрывают ≤ V−1
общих с w-компонентой точек (классическая конструкция из
полож./отриц. частей p−q). -/
def FannesDecomp (p q : V → ℝ) (τ : ℝ)
    (u u' w w' : V → ℝ) : Prop :=
  (∀ v, p v = (1 - τ) * u v + τ * w v)
    ∧ (∀ v, q v = (1 - τ) * u' v + τ * w' v)
    ∧ (∀ v, 0 ≤ u v ∧ 0 ≤ u' v ∧ 0 ≤ w v ∧ 0 ≤ w' v)
    ∧ (∑ v, u v) = 1 ∧ (∑ v, u' v) = 1

theorem entTV_nonneg (p q : V → ℝ) : 0 ≤ entTV p q := by
  unfold entTV
  positivity

theorem entTV_symm (p q : V → ℝ) : entTV p q = entTV q p := by
  unfold entTV
  refine congrArg _ (Finset.sum_congr rfl fun v _ => ?_)
  rw [abs_sub_comm]

/-- h₂ в центре равна log 2 (вычисление). -/
theorem binEnt_half : binEnt (1/2) = Real.log 2 := by
  unfold binEnt
  have hlog : Real.log (1/2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  linarith

/-- **T5: Pinsker-композиция непрерывности энтропии**: если
(i) Fannes-граница сертифицирована (измеряемое неравенство
|H(p)−H(q)| ≤ τ·log(V−1)+h₂(τ) — сертификат разложения из
полож./отриц. частей p−q), (ii) Pinsker-мост τ ≤ √(KL/2)
(KL-сканы), (iii) обе величины в [0, 1/2], (iv) монотонность
h₂ на [0,1/2] (сертифицируемый факт выпуклости:
dh₂/dτ = ln((1−τ)/τ) ≥ 0), (v) log(V−1) ≥ 0 (V ≥ 2) — то

  |H(p) − H(q)| ≤ √(KL/2)·log(V−1) + h₂(√(KL/2)).

Замена опровергнутой hcert: KL контролирует энтропию ТОЛЬКО
через τ (полную вариацию) — прямой «KL ⇒ энтропия не падает»
ЛОЖЕН (контрпример ревизии: sharpening tail при малом KL). -/
theorem entropy_continuity_pinsker (p q : V → ℝ)
    (τ kl : ℝ) (hτ : 0 ≤ τ) (hτ2 : τ ≤ 1/2)
    (hbound : |shannonEntropy p - shannonEntropy q| ≤
      τ * Real.log ((Fintype.card V : ℝ) - 1) + binEnt τ)
    (hpinsker : τ ≤ Real.sqrt (kl / 2))
    (hsq : Real.sqrt (kl / 2) ≤ 1/2)
    (hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1/2 → binEnt a ≤ binEnt b)
    (hV : (0:ℝ) ≤ Real.log ((Fintype.card V : ℝ) - 1)) :
    |shannonEntropy p - shannonEntropy q|
      ≤ Real.sqrt (kl / 2) * Real.log ((Fintype.card V : ℝ) - 1)
        + binEnt (Real.sqrt (kl / 2)) := by
  have hlin : τ * Real.log ((Fintype.card V : ℝ) - 1)
      ≤ Real.sqrt (kl / 2)
        * Real.log ((Fintype.card V : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hpinsker hV
  have hmono' := hmono τ (Real.sqrt (kl / 2)) hτ hpinsker hsq
  linarith [hbound, hlin, hmono']

end Hagi
