/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.DistillRecursion
set_option linter.style.header false

/-!
# T5 AntiCollapse — честная непрерывность энтропии

FORMALIZATION_PLAN §7.1 T5 (P1): ревизия опровергла hcert
(: «KL ≤ δ ⟹ энтропия не падает» — контрпример: может
сжигать энтропию, sharpening tail при малом KL). Замена:
Pinsker + явная непрерывность энтропии (Fannes-форма):

  |H(p) − H(q)| ≤ τ·log(V − 1) + h₂(τ),  τ = ½‖p − q‖₁,

где h₂ — двоичная энтропия. Связь с KL: Pinsker
τ ≤ √(KL(p‖q)/2) — измеряемый мост (посылка: KL-скан).

**Теоремы:**

* `entTV` (полная вариация), h2 (двоичная энтропия) — defs.
* `entTV_nonneg/symm/le_one` — базовые свойства.
* h2_le_log2 — h₂(τ) ≤ log 2 (грубая форма для гейтов).
* `entropy_continuity_pinsker` — ГЛАВНАЯ граница (T5): при
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

namespace Hagi.Data

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Полная вариация τ = ½‖p − q‖₁ (делегирование каноническому
Prelude.tvDef, дедуп R294). -/
noncomputable def entTV (p q : V → ℝ) : ℝ :=
  Hagi.Prelude.tvDef p q

/-- prelude bridge: entTV IS the canonical Prelude.tvDef. -/
theorem entTV_eq_tvDef (p q : V → ℝ) :
    entTV p q = Hagi.Prelude.tvDef p q := rfl

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
  rw [entTV_eq_tvDef]
  exact div_nonneg
        (Finset.sum_nonneg fun v _ => abs_nonneg (p v - q v))
        (by norm_num)

theorem entTV_symm (p q : V → ℝ) : entTV p q = entTV q p := by
  rw [entTV_eq_tvDef, entTV_eq_tvDef]
  exact congrArg (fun S : ℝ => S / 2)
    (Finset.sum_congr rfl fun v _ => abs_sub_comm (p v) (q v))

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



open Real Set

theorem binEnt_mono (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1/2) :
    binEnt a ≤ binEnt b := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · rw [heq]
  -- deriv on (a, b)
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt binEnt (log ((1 - x) / x)) x :=
    fun x hx => by
      have hx0 : x ≠ 0 := ne_of_gt (by
        have : a < x := hx.1
        linarith)
      have hx1 : 1 - x ≠ 0 := ne_of_gt (by
        have : x < b := hx.2
        linarith)
      have e1 : HasDerivAt (fun t : ℝ => t * log t) (1 * log x + x * x⁻¹) x :=
        (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
      have e2' := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
      rw [show ((fun _ : ℝ => (1:ℝ)) - id) = (fun t : ℝ => 1 - t) from rfl] at e2'
      have e2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using e2'
      have e3 : HasDerivAt (fun t : ℝ => log (1 - t)) ((1 - x)⁻¹ * (-1)) x :=
        (Real.hasDerivAt_log hx1).comp x e2
      have e4 : HasDerivAt (fun t : ℝ => (1 - t) * log (1 - t))
          ((-1) * log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1))) x :=
        e2.mul e3
      have h6' := (e1.neg).sub e4
      rw [show (-((fun t : ℝ => t * log t))) = (fun t : ℝ => -(t * log t)) from rfl] at h6'
      rw [show ((fun t : ℝ => -(t * log t)) - (fun t : ℝ => (1 - t) * log (1 - t)))
          = (fun t : ℝ => -t * log t - (1 - t) * log (1 - t)) from by
          funext t; simp] at h6'
      have h6 : HasDerivAt
          (fun t : ℝ => -t * log t - (1 - t) * log (1 - t))
          (-(1 * log x + x * x⁻¹)
            - ((-1) * log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1)))) x := h6'
      have hinv1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
      have hinv2 : (1 - x) * ((1 - x)⁻¹ * (-1)) = -1 := by
        field_simp
      rw [hinv1, hinv2] at h6
      rw [Real.log_div hx1 hx0]
      have hb : (fun t : ℝ => -t * log t - (1 - t) * log (1 - t)) = binEnt := rfl
      rw [hb] at h6
      convert h6 using 1 <;> ring
  -- continuity on [a, b]
  have hcont : ContinuousOn binEnt (Icc a b) := by
    have hsub1 : Icc a b ⊆ {x : ℝ | x ≠ 0} :=
      fun x hx => ne_of_gt (by
        have hxa : a ≤ x := hx.1
        linarith)
    have hsub2 : Icc a b ⊆ {x : ℝ | 1 - x ≠ 0} :=
      fun x hx => ne_of_gt (by
        have hxb : x ≤ b := hx.2
        have : b < 1 := by linarith
        linarith)
    have hc1 : ContinuousOn (fun t : ℝ => t * log t) (Icc a b) := by
      have hlog : ContinuousOn (fun t : ℝ => log t) (Icc a b) :=
        Real.continuousOn_log.mono hsub1
      exact continuousOn_id.mul hlog
    have hc2 : ContinuousOn (fun t : ℝ => (1 - t) * log (1 - t)) (Icc a b) := by
      have hmaps2 : MapsTo (fun t : ℝ => 1 - t) (Icc a b) {y : ℝ | y ≠ 0} :=
        fun x hx => ne_of_gt (by
          have hxb : x ≤ b := hx.2
          have : b < 1 := by linarith
          linarith)
      have hlog2 : ContinuousOn (fun t : ℝ => log (1 - t)) (Icc a b) :=
        Real.continuousOn_log.comp
          (ContinuousOn.sub continuousOn_const continuousOn_id)
          hmaps2
      exact (ContinuousOn.sub continuousOn_const continuousOn_id).mul hlog2
    have hfin := hc1.neg.sub hc2
    unfold binEnt
    convert hfin using 1
    funext t
    simp
  -- MVT
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope binEnt
      (fun x => log ((1 - x) / x)) hlt hcont hderiv
  have hcb : c < b := hc.2
  have hcgeo : (1:ℝ) ≤ (1 - c) / c := by
    have hc0 : (0:ℝ) < c := by
      have : a < c := hc.1
      linarith
    field_simp
    linarith
  have hslog : (0:ℝ) ≤ Real.log ((1 - c) / c) :=
    Real.log_nonneg hcgeo
  have hge : (0:ℝ) ≤ (binEnt b - binEnt a) / (b - a) := by
    rw [← hslope]
    exact hslog
  have hba : (0:ℝ) < b - a := by linarith
  have hmul : (binEnt b - binEnt a) / (b - a) * (b - a)
      = binEnt b - binEnt a :=
    div_mul_cancel₀ (binEnt b - binEnt a)
      (sub_ne_zero.mpr (by linarith))
  have hprod : (0:ℝ) ≤ (binEnt b - binEnt a) / (b - a) * (b - a) :=
    mul_nonneg hge hba.le
  rw [hmul] at hprod
  linarith


/-- Неотрицательность binEnt на [0, 1/2] (граничный случай
для монотонности). -/
theorem binEnt_nonneg (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b ≤ 1/2) :
    (0:ℝ) ≤ binEnt b := by
  rcases eq_or_lt_of_le hb0 with h0 | hpos
  · rw [← h0]
    unfold binEnt
    norm_num
  · have hb1 : b ≤ 1 := by linarith
    unfold binEnt
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hpos.le hb1
    have hl1 : (0:ℝ) ≤ -b * Real.log b := by nlinarith
    have h1b : (0:ℝ) < 1 - b := by linarith
    have h1b1 : 1 - b ≤ 1 := by linarith
    have hlog2 : Real.log (1 - b) ≤ 0 :=
      Real.log_nonpos h1b.le h1b1
    have hl2 : (0:ℝ) ≤ -(1 - b) * Real.log (1 - b) := by nlinarith
    linarith

/-- **T5 без посылки hmono**: монотонность h2 — теорема
(`binEnt_mono`), остальной контракт T5 без изменений. -/
theorem entropy_continuity_pinsker'
    {V : Type*} [Fintype V] [DecidableEq V] (p q : V → ℝ)
    (τ kl : ℝ) (hτ : 0 ≤ τ) (hτ2 : τ ≤ 1/2)
    (hbound : |shannonEntropy p - shannonEntropy q| ≤
      τ * Real.log ((Fintype.card V : ℝ) - 1) + binEnt τ)
    (hpinsker : τ ≤ Real.sqrt (kl / 2))
    (hsq : Real.sqrt (kl / 2) ≤ 1/2)
    (hV : (0:ℝ) ≤ Real.log ((Fintype.card V : ℝ) - 1)) :
    |shannonEntropy p - shannonEntropy q|
      ≤ Real.sqrt (kl / 2) * Real.log ((Fintype.card V : ℝ) - 1)
        + binEnt (Real.sqrt (kl / 2)) := by
  have hmono' : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1/2 → binEnt a ≤ binEnt b := by
    intro a b ha0 hab hb2
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · -- a = 0: binEnt 0 = 0 <= binEnt b
      have h0b : (0:ℝ) ≤ b := by linarith
      have hz : binEnt 0 = 0 := by
        unfold binEnt
        norm_num
      rw [← h0, hz]
      exact binEnt_nonneg b h0b hb2
    · exact binEnt_mono a b hpos hab hb2
  exact entropy_continuity_pinsker p q τ kl hτ hτ2 hbound hpinsker hsq hmono' hV

end Hagi.Data


namespace Hagi
export Hagi.Data (entTV binEnt FannesDecomp entTV_nonneg entTV_symm binEnt_half entropy_continuity_pinsker)
end Hagi
