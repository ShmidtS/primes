/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ShiftedTarget — сдвиг целевого байта ломает оценку гейта

Баг unified.py (`_windows` брал целью `idx[p+k]` вместо следующего байта):
все гейты адаптеров/роста/ремонта оценивали модель как случайную.

* `Exact x T k f` — предиктор `f` по контексту угадывает `x (t+k)` на `[0,T)`.
* `exact_period2_iff` — на потоке `0,1,0,1,…` точность предиктора «текущий байт»
  равносильна чётности сдвига `k`.
* `shifted_target_breaks` — при нечётном сдвиге точный предиктор становится
  неточным: гейт по сдвинутой цели видит случайную модель.

Сертификат конечный и безусловный; цифры CE кода не моделируются.
-/

namespace Hagi.Model.ShiftedTarget

/-- Предиктор `f` по контексту точен на потоке `x` в окне `[0,T)` при целевом
сдвиге `k`: `f x_{<t} = x (t+k)` для всех `t < T`. -/
def Exact (x : ℕ → ℕ) (T k : ℕ) (f : List ℕ → ℕ) : Prop :=
  ∀ t, t < T → f ((List.range t).map x) = x (t + k)
/-- Правильная цель (`k = 1`): предиктор «период 1» точен. -/
theorem exact_k1_period1 (c : ℕ) (T : ℕ) : Exact (fun _ => c) T 1 (fun _ => c) := fun _ _ => rfl
/-- Поток периода 2 `0,1,0,1,…`, предиктор «текущий байт» (чётность позиции).
Точность в окне `[0,2)` равносильна чётности сдвига `k`. -/
theorem exact_period2_iff (k : ℕ) :
    Exact (fun t => t % 2) 2 k (fun ctx => ctx.length % 2) ↔ k % 2 = 0 := by
  constructor
  · intro h
    have h1 := h 1 (by decide)
    simp only [List.length_map, List.length_range, Nat.cast_ofNat, Nat.mod_mul_mod,
      Nat.mod_eq_of_lt (by decide : (1:ℕ) < 2)] at h1
    have : (1 + k) % 2 = 1 := by omega
    omega
  · intro hk t ht
    have ht2 : t < 2 := by omega
    have hte : t % 2 = t := by omega
    simp only [List.length_map, List.length_range, hte, Nat.cast_ofNat]
    rw [Nat.add_comm, Nat.add_mod]
    omega
/-- Сдвиг цели на нечётное число позиций превращает точный предиктор в
неточный: гейт по сдвинутой цели видит случайную модель. -/
theorem shifted_target_breaks (k : ℕ) (hk : k % 2 = 1) :
    Exact (fun t => t % 2) 2 0 (fun ctx => ctx.length % 2) ∧
    ¬ Exact (fun t => t % 2) 2 k (fun ctx => ctx.length % 2) := by
  exact ⟨(exact_period2_iff 0).2 (by decide), fun h => by rw [exact_period2_iff k] at h; omega⟩

end Hagi.Model.ShiftedTarget
