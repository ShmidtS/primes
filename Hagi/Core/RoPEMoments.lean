 /-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.RoPELimit

set_option linter.style.header false

/-!
# RoPEMoments — моменты высокочастотного счёта (Prop 1,
слайс)

Ядро Proposition 1 из «RoPE at the End of Its Rope?»
(arXiv:2609.39929): высокочастотный attention-счёт
S(m) = Σ_n z_n·cos(m·ω_n) при равномерном m ∈ {0..M−1}.

Доказано (ТОЧНЫЕ моментные тождества — редукция Prop 1 к
частотным контрактам окна):
* `rope_mean_sum`: Σ_m S(m) = Σ_n z_n·C(ω_n), где
  C(ω) := Σ_m cos(mω) — среднее = сумма геометрических
  косинус-сумм (обмен сумм);
* `rope_second_moment_sum`: 2·Σ_m S(m)² = Σ_{n,k} z_n z_k·
  [C(ω_n+ω_k) + C(ω_n−ω_k)] — косинусное
  произведение-тождество: ВТОРОЙ момент полностью
  определяется парными фазовыми суммами C.

Смысл: Prop 1-оценки |E[S]| ≤ εU, |Var − U²/2| ≤ εU²
сводятся к контрактам на C (малость геометрических сумм на
высоких частотах — lacunary-условия сертифицированного
окна); моментная структура — точная, без приближений.

Prop 1 — НИЖНЯЯ ОЦЕНКА ВАРИАЦИИ (_contractная форма_,
доказано):
* `rope_var_bound`: при |C(2ω_n)| ≤ κM и
  |C(ω_n±ω_k)| ≤ κM (n≠k), Σz²=1:
  |Σ_m S(m)²/M − 1/2| ≤ κ(1+2M)/2 — вариация счёта
  около неминуемого уровня 1/2: диагональ даёт κM,
  кросс-члены 2κM·M (Коши–Буняковский (Σ|z|)² ≤ M).
  С R284 (rope_limit_irreversible) замыкает Theorem 0:
  RoPE-модель не может удерживать точность выше порога.

Честная граница: сами оценки |C(ω)| — эмпирические
контракты окна; формализованы тождества.
-/

open Finset

namespace Hagi.RoPEMoments

variable (M : ℕ) (omega : Fin M → ℝ) (z : Fin M → ℝ)

/-- Высокочастотный счёт: S(m) = Σ_n z_n cos(m ω_n). -/
noncomputable def ropeScore (m : ℕ) : ℝ :=
  ∑ n, z n * Real.cos (m * omega n)

/-- Косинус-сумма окна: C(ω) := Σ_{m<M} cos(mω). -/
noncomputable def cosSum (w : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M, Real.cos (m * w)

/-- Среднее: Σ_m S(m) = Σ_n z_n·C(ω_n) — обмен сумм. -/
theorem rope_mean_sum :
    ∑ m ∈ Finset.range M, ropeScore M omega z m
      = ∑ n, z n * cosSum M (omega n) := by
  unfold ropeScore cosSum
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => (Finset.mul_sum _ _ _).symm

/-- Второй момент: 2·Σ_m S(m)² = Σ_{n,k} z_n z_k·
[C(ω_n+ω_k) + C(ω_n−ω_k)] — косинусное
произведение-тождество (Fintype.sum_mul_sum) + обмены
сумм. -/
theorem rope_second_moment_sum :
    2 * ∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2
      = ∑ n, ∑ k, z n * z k
          * (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) := by
  have hcos2 : ∀ (m : ℕ) (a b : ℝ),
      2 * (Real.cos (m * a) * Real.cos (m * b))
        = Real.cos (m * (a + b)) + Real.cos (m * (a - b)) := by
    intro m a b
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring
  have hpermMini : ∀ (m : ℕ),
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, 2 * (z n * Real.cos (m * omega n))
            * (z k * Real.cos (m * omega k)) := by
    intro m
    rw [sq, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    ring
  have hperm : ∀ m ∈ Finset.range M,
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, z n * z k
            * (Real.cos (m * (omega n + omega k))
              + Real.cos (m * (omega n - omega k))) := by
    intro m _
    rw [hpermMini m]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcos2 m (omega n) (omega k)]
    ring_nf
  unfold ropeScore
  unfold cosSum

  have hcos2 : ∀ (m : ℕ) (a b : ℝ),
      2 * (Real.cos (m * a) * Real.cos (m * b))
        = Real.cos (m * (a + b)) + Real.cos (m * (a - b)) := by
    intro m a b
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring_nf
  have hpermMini : ∀ (m : ℕ),
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, 2 * (z n * Real.cos (m * omega n))
            * (z k * Real.cos (m * omega k)) := by
    intro m
    rw [sq, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    ring_nf
  have hperm : ∀ m ∈ Finset.range M,
      2 * (∑ n, z n * Real.cos (m * omega n)) ^ 2
        = ∑ n, ∑ k, z n * z k
            * (Real.cos (m * (omega n + omega k))
              + Real.cos (m * (omega n - omega k))) := by
    intro m _
    rw [hpermMini m]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcos2 m (omega n) (omega k)]
    ring_nf
  conv_lhs => rw [Finset.mul_sum]
  have h1 := Finset.sum_congr rfl (fun m hm => hperm m hm)
  rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsplit : ∀ x ∈ Finset.range M,
      z n * z k * (Real.cos (x * (omega n + omega k))
        + Real.cos (x * (omega n - omega k)))
      = z n * z k * Real.cos (x * (omega n + omega k))
        + z n * z k * Real.cos (x * (omega n - omega k)) :=
    fun x _ => mul_add _ _ _
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem cosSum_zero' : cosSum M 0 = M := by
  unfold cosSum
  simp

theorem sum_diag_off' (f : Fin M → Fin M → ℝ) :
    ∑ n, ∑ k, f n k
      = (∑ n, f n n)
        + ∑ n, ∑ k ∈ Finset.univ.erase n, f n k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by
    rw [← Finset.sum_insert
      (Finset.notMem_erase n Finset.univ)]
    simp

theorem sum_singleton_rest (f : Fin M → ℝ) (n : Fin M) :
    ∑ k, f k = f n + ∑ k ∈ Finset.univ.erase n, f k := by
  rw [← Finset.sum_insert
    (Finset.notMem_erase n Finset.univ)]
  simp

theorem rope_var_bound (kappa : ℝ)
    (hdiag : ∀ n, |cosSum M (2 * omega n)| ≤ kappa * M)
    (hcross : ∀ n k, n ≠ k →
      |cosSum M (omega n + omega k)| ≤ kappa * M ∧
      |cosSum M (omega n - omega k)| ≤ kappa * M)
    (hsum : ∑ n, z n ^ 2 = 1) (hkappa : 0 ≤ kappa) :
    |(∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2) / M
      - 1 / 2|
      ≤ kappa * (1 + 2 * M) / 2 := by
  have hdiagval : ∀ n : Fin M,
      z n * z n * (cosSum M (omega n + omega n)
        + cosSum M (omega n - omega n))
      = z n ^ 2 * (cosSum M (2 * omega n) + M) := by
    intro n
    have h1 : omega n + omega n = 2 * omega n := by ring
    have h0 : omega n - omega n = 0 := by ring
    rw [h1, h0, cosSum_zero', ← sq (z n)]
  have e1 : 2 * ∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2
      = ∑ n, ∑ k, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) :=
    rope_second_moment_sum M omega z
  have e2 : ∑ n, ∑ k, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k))
      = (∑ n, z n * z n * (cosSum M (omega n + omega n)
          + cosSum M (omega n - omega n)))
        + ∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) :=
    sum_diag_off' M _
  have e3 : (∑ n, z n * z n * (cosSum M (omega n + omega n)
          + cosSum M (omega n - omega n)))
      = ∑ n, z n ^ 2 * (cosSum M (2 * omega n) + M) :=
    Finset.sum_congr rfl fun n _ => hdiagval n
  have h2c : 2 * ∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2
      = (∑ n, z n ^ 2 * (cosSum M (2 * omega n) + M))
        + ∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) :=
    e1.trans (e2.trans (congrArg (fun x => x +
      ∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
        (cosSum M (omega n + omega k)
          + cosSum M (omega n - omega k))) e3))
  have hM : ∑ n, z n ^ 2 * M = M := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hsplit2 : ∑ n, z n ^ 2 * (cosSum M (2 * omega n) + M)
      = ∑ n, z n ^ 2 * cosSum M (2 * omega n) + M := by
    have hd : ∀ n : Fin M, z n ^ 2 * (cosSum M (2 * omega n) + M)
        = z n ^ 2 * cosSum M (2 * omega n) + z n ^ 2 * M :=
      fun n => by rw [mul_add]
    rw [Finset.sum_congr rfl (fun n _ => hd n),
      Finset.sum_add_distrib, hM]
  rw [hsplit2] at h2c
  -- кросс-оценка построчно
  have hrow : ∀ n : Fin M,
      |∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k))|
        ≤ |z n| * (∑ k ∈ Finset.univ.erase n, |z k|) * (2 * kappa * M) := by
    intro n
    have habs : |∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k))|
        ≤ ∑ k ∈ Finset.univ.erase n,
            |z n| * |z k| * (2 * kappa * M) := by
      calc |∑ k ∈ Finset.univ.erase n, z n * z k *
              (cosSum M (omega n + omega k)
                + cosSum M (omega n - omega k))|
          ≤ ∑ k ∈ Finset.univ.erase n, |z n * z k *
              (cosSum M (omega n + omega k)
                + cosSum M (omega n - omega k))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.univ.erase n,
              |z n| * |z k| * |cosSum M (omega n + omega k)
                + cosSum M (omega n - omega k)| := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show z n * z k * (cosSum M (omega n + omega k)
                + cosSum M (omega n - omega k))
                = (z n * z k) * (cosSum M (omega n + omega k)
                  + cosSum M (omega n - omega k)) from rfl,
              abs_mul, abs_mul]
        _ ≤ ∑ k ∈ Finset.univ.erase n,
              |z n| * |z k| * (2 * kappa * M) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' := Finset.mem_erase.mp hk
            have hck := hcross n k (Ne.symm hk'.1)
            have h1 : |cosSum M (omega n + omega k)
                + cosSum M (omega n - omega k)|
                ≤ 2 * kappa * M := by
              calc |cosSum M (omega n + omega k)
                    + cosSum M (omega n - omega k)|
                  ≤ |cosSum M (omega n + omega k)|
                    + |cosSum M (omega n - omega k)| :=
                    abs_add_le
                      (cosSum M (omega n + omega k))
                      (cosSum M (omega n - omega k))
                _ ≤ kappa * M + kappa * M :=
                    add_le_add hck.1 hck.2
                _ = 2 * kappa * M := by ring
            exact mul_le_mul_of_nonneg_left h1
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc |∑ k ∈ Finset.univ.erase n, z n * z k *
            (cosSum M (omega n + omega k)
              + cosSum M (omega n - omega k))|
        ≤ ∑ k ∈ Finset.univ.erase n,
            |z n| * |z k| * (2 * kappa * M) := habs
      _ = |z n| * (2 * kappa * M)
            * ∑ k ∈ Finset.univ.erase n, |z k| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = |z n| * (∑ k ∈ Finset.univ.erase n, |z k|)
            * (2 * kappa * M) := by ring
  -- итоговая кросс-граница: |cross| ≤ 2κM·(Σ|z|)² ≤ 2κM·M
  have hcs : (∑ n, |z n|) ^ 2 ≤ (M : ℝ) := by
    have h1 := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin M)))
      (f := fun n : Fin M => |z n|)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have hsq : ∑ n, |z n| ^ 2 = 1 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun n _ => sq_abs (z n)
    rw [hsq] at h1
    linarith
  have hRle : ∀ n : Fin M,
      ∑ k ∈ Finset.univ.erase n, |z k| ≤ ∑ k, |z k| := by
    intro n
    have hins := sum_singleton_rest M (fun k => |z k|) n
    linarith [hins, abs_nonneg (z n)]
  have hkpos : (0:ℝ) ≤ 2 * kappa * M :=
    mul_nonneg (mul_nonneg (by norm_num) hkappa)
      (Nat.cast_nonneg M)
  have hcrossle : |∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
        (cosSum M (omega n + omega k)
          + cosSum M (omega n - omega k))|
      ≤ 2 * kappa * M * M := by
    have hrowsum : |∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k))|
        ≤ ∑ n, |z n| * (∑ k ∈ Finset.univ.erase n, |z k|)
            * (2 * kappa * M) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun n _ => hrow n)
    have hred : ∑ n, |z n| * (∑ k ∈ Finset.univ.erase n, |z k|)
          * (2 * kappa * M)
        ≤ (∑ n, |z n|) * (∑ k, |z k|) * (2 * kappa * M) := by
      calc ∑ n, |z n| * (∑ k ∈ Finset.univ.erase n, |z k|)
              * (2 * kappa * M)
          ≤ ∑ n, |z n| * (∑ k, |z k|) * (2 * kappa * M) := by
              exact Finset.sum_le_sum fun n _ =>
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hRle n)
                    (abs_nonneg (z n))) hkpos
        _ = (∑ n, |z n|) * (∑ k, |z k|)
              * (2 * kappa * M) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hfin : (∑ n, |z n|) * (∑ n, |z n|) * (2 * kappa * M)
        ≤ 2 * kappa * M * M := by
      nlinarith [hcs, hkpos]
    exact le_trans hrowsum (le_trans hred hfin)
  -- финальная сборка
  have hkey : 2 * (∑ m ∈ Finset.range M, (ropeScore M omega z m) ^ 2)
      - M = (∑ n, z n ^ 2 * cosSum M (2 * omega n))
        + ∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
          (cosSum M (omega n + omega k)
            + cosSum M (omega n - omega k)) := by
    linarith [h2c]
  -- диагональная оценка
  have hdiagle : |∑ n, z n ^ 2 * cosSum M (2 * omega n)|
      ≤ kappa * M := by
    have habs : |∑ n, z n ^ 2 * cosSum M (2 * omega n)|
        ≤ ∑ n, |z n ^ 2 * cosSum M (2 * omega n)| :=
      Finset.abs_sum_le_sum_abs _ _
    have heq : ∑ n, |z n ^ 2 * cosSum M (2 * omega n)|
        = ∑ n, z n ^ 2 * |cosSum M (2 * omega n)| := by
      exact Finset.sum_congr rfl fun n _ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (z n))]
    have hstep : ∑ n, z n ^ 2 * |cosSum M (2 * omega n)|
        ≤ ∑ n, z n ^ 2 * (kappa * M) :=
      Finset.sum_le_sum fun n _ =>
        mul_le_mul_of_nonneg_left (hdiag n) (sq_nonneg (z n))
    have hsimp2 : ∑ n, z n ^ 2 * (kappa * M) = kappa * M := by
      rw [← Finset.sum_mul, hsum, one_mul]
    exact habs.trans
      ((le_of_eq heq).trans
        (hstep.trans (le_of_eq hsimp2)))
  -- финал
  have hMpos : (0:ℝ) < M := by
    cases Nat.eq_zero_or_pos M with
    | inl h0 => subst h0; simp at hsum
    | inr h1 => exact_mod_cast h1
  have htri : |2 * (∑ m ∈ Finset.range M,
        (ropeScore M omega z m) ^ 2) - M|
      ≤ kappa * M + 2 * kappa * M * M := by
    have habs2 : |2 * (∑ m ∈ Finset.range M,
          (ropeScore M omega z m) ^ 2) - M|
        = |(∑ n, z n ^ 2 * cosSum M (2 * omega n))
          + ∑ n, ∑ k ∈ Finset.univ.erase n, z n * z k *
            (cosSum M (omega n + omega k)
              + cosSum M (omega n - omega k))| := by
      rw [hkey]
    rw [habs2]
    exact le_trans (abs_add_le _ _)
      (add_le_add hdiagle hcrossle)
  have hfin2 : |(∑ m ∈ Finset.range M,
        (ropeScore M omega z m) ^ 2) / M - 1 / 2|
      ≤ kappa * (1 + 2 * M) / 2 := by
    have hconv : (∑ m ∈ Finset.range M,
        (ropeScore M omega z m) ^ 2) / M - 1 / 2
        = (2 * (∑ m ∈ Finset.range M,
            (ropeScore M omega z m) ^ 2) - M) / (2 * M) := by
      field_simp
    rw [hconv]
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * M)]
    have h2 : (kappa * M + 2 * kappa * M * M) / (2 * M)
        = kappa * (1 + 2 * M) / 2 := by
      field_simp
    have h1 : |2 * (∑ m ∈ Finset.range M,
          (ropeScore M omega z m) ^ 2) - M| / (2 * M)
        ≤ kappa * (1 + 2 * M) / 2 :=
      ((div_le_div_iff_of_pos_right
          (by linarith : (0:ℝ) < 2 * M)).mpr htri).trans
        (le_of_eq h2)
    exact h1
  exact hfin2

end Hagi.RoPEMoments
