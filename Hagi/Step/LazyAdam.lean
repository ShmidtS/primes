/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# LazyAdam — точная эквивалентность ленивого и плотного Adam (β₁ = 0)

Модель: AdamW с β₁ = 0, decoupled weight decay; вторая
момента на строке таблицы обновляется только на затронутых
шагах: `v_t = β₂·v_{t−1} + (1−β₂)·g_t²`.

* `lazyDecay_exact`: за d пропущенных шагов плотная
  рекуррентность даёт `v_{τ+d} = β₂^d·v_τ` — точно
  геометрический декей (итерация `x ↦ β₂·x`);
* `lazyReplay_exact`: тождество композиции —
  `β₂^d·(v + (1−β₂)g²) = β₂^d·v + β₂^d·(1−β₂)·g²`;
  вместе с точной геометрией декея — алгебраическая основа
  эквивалентности ленивого повтора плотной траектории;
* `supportSet_bound`: `|(S_in ∪ S_tgt) ∪ S_neg|.card
  ≤ |S_in| + |S_tgt| + |S_neg|`.

Граница: эквивалентность — между ленивым β₁=0 и плотным
β₁=0; сравнение с AdamW β₁=0.9 — эмпирическое (A/B),
не теорема.
-/

open Finset

namespace Hagi

section LazyAdam

/- Состояние второй момента на строку (β₁ = 0): скаляр
на строку. -/

/-- Геометрический декей за пропущенную серию: итерация
`x ↦ β₂·x` d раз даёт `(β₂^d)·v0` — точно, одним
скалярным умножением. -/
theorem lazyDecay_exact (beta2 v0 : ℝ) (d : ℕ) :
    (fun x => beta2 * x)^[d] v0 = (beta2^d) * v0 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    ring

/-- Тождество композиции повтора:
`(β₂^d)·(vstale + (1−β₂)·g²)
= (β₂^d)·vstale + (β₂^d)·(1−β₂)·g²` — алгебраическая
основа эквивалентности ленивого повтора (с
`lazyDecay_exact` — по индукции по паттерну касаний). -/
theorem lazyReplay_exact (beta2 vstale g : ℝ) (d : ℕ) :
    (beta2^d) * (vstale + (1 - beta2) * g^2)
      = (beta2^d) * vstale + (beta2^d) * (1 - beta2) * g^2 := by
  ring

-- НЕ ТЕОРЕМА: прежняя rfl-форма была носителем предписания.
-- Аккумулятор-произведение — реализация; эквивалентность —
-- в тождествах выше.

set_option linter.unusedDecidableInType false in
-- гипотеза сохранена: документированная посылка API
/-- `((S_in ∪ S_tgt) ∪ S_neg).card ≤ S_in.card + S_tgt.card
+ S_neg.card` (union bound для затронутых строк). -/
theorem supportSet_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S_in S_tgt S_neg : Finset ι) :
    ((S_in ∪ S_tgt) ∪ S_neg).card
      ≤ S_in.card + S_tgt.card + S_neg.card := by
  have h1 : ((S_in ∪ S_tgt) ∪ S_neg).card
      ≤ (S_in ∪ S_tgt).card + S_neg.card :=
    Finset.card_union_le _ _
  have h2 : (S_in ∪ S_tgt).card ≤ S_in.card + S_tgt.card :=
    Finset.card_union_le _ _
  omega

end LazyAdam

end Hagi
