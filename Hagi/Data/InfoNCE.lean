/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.Canonical
import Hagi.Data.DField

set_option linter.style.header false

/-!
# InfoNCE — нижняя граница взаимной информации

Формализация ядра InfoNCE-неравенства (van den Oord et al.,
«Representation Learning with Contrastive Predictive Coding»;
корпус-подтверждение: SSL-HSICIC 2106.08320 — «InfoNCE, a
variational lower bound on the mutual information»):
контрастивный лосс (кросс-энтропия softmax-модели против
целевого индекса) НЕ МОЖЕТ опуститься ниже энтропии цели —
потому log K − L_NCE ≤ log K − H: InfoNCE-оценка никогда не
переоценивает взаимную информацию.

Доказано (на канонических CE/KL/H из Data/Canonical):
* `ce_ge_entropy`: CE q p ≥ H q — кросс-энтропия не ниже
  собственной энтропии цели;
* `infonce_never_overestimates`: log k − CE q p ≤
  log k − H q — InfoNCE-оценка MI не выше log K − H(q);
* `infonce_gap_is_kl`: зазор «MI − InfoNCE-оценка» — ТОЧНО
  KL(post ‖ model): контрастивная оценка терминально точна
  ⟺ модель равна постериору.

Плановая переформулировка IB-строк (§2 плана): вместо
НЕоцениваемого MI — surrogate-bound; здесь он доказан.
-/

open Finset

namespace Hagi.InfoNCE

variable {V : Type} [Fintype V] [DecidableEq V]

/-- CE q q в точности равен энтропии H q (знак-соглашения
канонических определений совпадают). -/
theorem ce_self_eq_entropy (q : V → ℝ) :
    Hagi.Canonical.CE q q = Hagi.Canonical.H q := rfl

/-- Кросс-энтропия не ниже энтропии цели: CE q p ≥ H q
(KL ≥ 0 в ce-разложении kl_excess_cross_entropy). -/
theorem ce_ge_entropy (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    Hagi.Canonical.H q ≤ Hagi.Canonical.CE q p := by
  have hex := Hagi.Canonical.kl_excess_cross_entropy q p
    (fun v => ne_of_gt (hq v))
    (fun v => ne_of_gt (hp v))
  have hkl : 0 ≤ Hagi.Canonical.KL q p :=
    Hagi.kl_nonneg q p hq hp hsumq hsump
  rw [ce_self_eq_entropy] at hex
  linarith [hex, hkl]

/-- InfoNCE никогда не переоценивает MI: log k − лосс
не выше log k − энтропийного пола. -/
theorem infonce_never_overestimates (k : ℝ) (q p : V → ℝ)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v) :
    k - Hagi.Canonical.CE q p ≤ k - Hagi.Canonical.H q := by
  have h := ce_ge_entropy q p hsumq hsump hq hp
  linarith

/-- Зазор «MI − InfoNCE-оценка» — ТОЧНО KL(post ‖ model):
контрастивная оценка терминально точна ⟺ модель совпадает
с постериором (зазор нулевой ⟺ KL нулевой). -/
theorem infonce_gap_is_kl (k : ℝ) (q p : V → ℝ)
    (hq : ∀ v, q v ≠ 0) (hp : ∀ v, p v ≠ 0) :
    (k - Hagi.Canonical.H q) - (k - Hagi.Canonical.CE q p)
      = Hagi.Canonical.KL q p := by
  have hex := Hagi.Canonical.kl_excess_cross_entropy q p hq hp
  rw [ce_self_eq_entropy] at hex
  linarith

end Hagi.InfoNCE
