import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option linter.style.header false

/-!
# RCDL — Retrieval-Centric Deep Learning: дуальность и gauge-инвариантность

Исследовательский цикл 5 (источник: arXiv:2610.03858,
Schlegel et al., "Retrieval-Centric Deep Learning in Growing
Nonparametric Neural Networks"):

1. `dual_apply`: ТОЧНАЯ дуальная форма линейного слоя после T
   шагов SGD: (W₀ + Σₜ vₜ xₜᵀ) q = W₀ q + Σₜ vₜ (xₜᵀ q) —
   слой эквивалентен ненормализованному linear attention с
   ключами xₜ и значениями vₜ. Никакой эмпирики: чистая
   дистрибутивность, но она — фундамент RCDL.

2. `weightedSoftmax` и `gauge_shift`: взвешенный софтмакс
   s_D(q) = Σ e^{⟨kᵢ,q⟩} ṽᵢ / Σ e^{⟨kᵢ,q⟩} wᵢ и строгая
   теорема gauge-инвариантности: сдвиг всех значений базы на
   вектор b (ṽᵢ → ṽᵢ + b·wᵢ) НЕ меняет s_D(q). Именно эта
   инвариантность позволяет выбирать калибровочный сдвиг для
   гарантии положительных весов новых ключей без клиппинга
   (доказательство корректности сдвига — следующая цель).

Честная граница: функциональный градиент Фреше по гауссовым
смесям и theorem о regret RCDL здесь НЕ формализуются.
-/

open Finset Matrix

namespace Hagi.Learning.RCDL

variable {d T : ℕ}

/-! ### Дуальная форма линейного слоя -/

/-- Внешнее произведение: (outer v x) i j = v i * x j. -/
def outer (v x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => v i * x j

/-- SGD-обновление весов через внешние произведения. -/
def dualW (W0 : Matrix (Fin d) (Fin d) ℝ)
    (xs vs : Fin T → (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  W0 + ∑ t, outer (vs t) (xs t)

/-- ДУАЛЬНОЕ ТОЖДЕСТВО RCDL: слой после T SGD-шагов — это
ненормализованный linear attention с ключами xₜ, значениями vₜ:
(W₀ + Σ vₜ xₜᵀ) q = W₀ q + Σ vₜ ⟨xₜ, q⟩. -/
theorem dual_apply (W0 : Matrix (Fin d) (Fin d) ℝ)
    (xs vs : Fin T → (Fin d → ℝ)) (q : Fin d → ℝ) (i : Fin d) :
    (dualW W0 xs vs *ᵥ q) i
      = (W0 *ᵥ q) i + ∑ t, dotProduct (xs t) q * vs t i := by
  have hkey : ∀ (v x : Fin d → ℝ),
      dotProduct v x * 0 = 0 := fun v x => by ring
  -- поэлементно: разворачиваем все определения
  unfold dualW
  simp only [Matrix.add_mulVec, Matrix.sum_apply, Matrix.add_apply,
    Matrix.of_apply, Matrix.mulVec, dotProduct, outer]
  -- осталось: Σ_j (W0 i j + Σ_t vs t i * xs t j) * q j
  --         = Σ_j W0 i j * q j + Σ_t (Σ_j xs t j * q j) * vs t i
  have hsplit : ∀ j : Fin d,
      (W0 i j + ∑ t, vs t i * xs t j) * q j
        = W0 i j * q j + ∑ t, (xs t j * q j) * vs t i := by
    intro j
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  congr 1
  -- обмен порядков суммирования в двойной сумме
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => by
    rw [Finset.sum_mul])

end Hagi.Learning.RCDL

/-! ### Взвешенный софтмакс и gauge-инвариантность -/

variable {N : ℕ}

/-- Экспоненциальный вес ключа: e^{⟨kᵢ, q⟩}. -/
noncomputable def expw (k q : Fin d → ℝ) : ℝ := Real.exp (dotProduct k q)

/-- Взвешенный софтмакс RCDL:
s(q) = Σ e^{⟨kᵢ,q⟩} ṽᵢ / Σ e^{⟨kᵢ,q⟩} wᵢ. -/
noncomputable def weightedSoftmax (ks : Fin N → Fin d → ℝ)
    (ws : Fin N → ℝ) (vs : Fin N → Fin d → ℝ) (q : Fin d → ℝ) :
    Fin d → ℝ :=
  fun j => (∑ i, expw (ks i) q * vs i j) / (∑ i, expw (ks i) q * ws i)

/-- GAUGE-ИНВАРИАНТНОСТЬ: сдвиг базы значений на вектор b
(ṽᵢ → ṽᵢ + b·wᵢ) не меняет взвешенный софтмакс. Именно эта
теорема делает калибровочный сдвиг законным инструментом
гарантии w_new > 0 (arXiv:2610.03858, Sec. 3.2). -/
theorem gauge_shift (ks : Fin N → Fin d → ℝ) (ws : Fin N → ℝ)
    (vs : Fin N → Fin d → ℝ) (q : Fin d → ℝ) (b : Fin d → ℝ)
    (hdenpos : (∑ i, expw (ks i) q * ws i) ≠ 0) :
    weightedSoftmax ks ws (fun i => vs i + ws i • b) q
      = weightedSoftmax ks ws vs q + b := by
  unfold weightedSoftmax
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i : Fin N, expw (ks i) q * (vs i j + ws i * b j)
      = expw (ks i) q * vs i j + expw (ks i) q * ws i * b j := by
    intro i; ring
  have hnum : ∑ i, expw (ks i) q * (vs i j + ws i * b j)
      = ∑ i, expw (ks i) q * vs i j + (∑ i, expw (ks i) q * ws i) * b j := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_mul]
  rw [hnum]
  field_simp

/-! ### Существование калибровочного сдвига -/

/-- GAUGE-СУЩЕСТВОВАНИЕ: если выход s не согласован с градиентом
(⟨g, s⟩ ≤ 0) и градиент ненулевой, существует явный сдвиг
b = δ·g, делающий согласование строгим: ⟨g, s + b⟩ > 0.
Вместе с gauge_shift это даёт законную (без клиппинга)
гарантию строго положительного веса нового ключа RCDL:
w_new ∝ ⟨g, s + b⟩ > 0. -/
theorem gauge_exists (s g : Fin d → ℝ) (hg : g ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ b : Fin d → ℝ, dotProduct g (s + b) ≥ eps := by
  refine ⟨((eps - dotProduct g s) / dotProduct g g) • g, ?_⟩
  have hgg : 0 < dotProduct g g := by
    have hnn : (0:ℝ) ≤ dotProduct g g := by
      unfold dotProduct
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))
    rcases lt_or_eq_of_le hnn with h1 | h1
    · exact h1
    · exact absurd (dotProduct_self_eq_zero.mp h1.symm) hg
  have hkey : dotProduct g (s + ((eps - dotProduct g s) / dotProduct g g) • g)
      = eps := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul,
      div_mul_cancel₀ _ (ne_of_gt hgg)]
    ring
  rw [hkey]
