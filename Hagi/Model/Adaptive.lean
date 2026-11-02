/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Foundations.SumIdentities
import Hagi.Prelude.Info
import Hagi.Model.NormAct

/-!
# Адаптивный рост архитектуры (объединённый)

LoRA, Upcycling, Matryoshka, MoeExpansion, ReZero,
SwitchMoE. Имена сохранены.
-/

/-!
# Switch MoE: балансировка нагрузки (источник №34)

Источник №34: Fedus, Zoph, Shazeer, "Switch Transformers:
Scaling to Trillion Parameter Models" (arXiv 2101.03961).
Auxiliary load-balance loss L = α·n·∑ f_i·P_i штрафует
перегрузку экспертов: f_i — доля токенов у эксперта i,
P_i — вероятность роутера. При роутинге f ∝ P нагрузочный
член ∝ ∑ P_i², и его МИНИМУМ — равномерное распределение.

Формализованное ядро (строгое, |E| = n > 0, ∑ P = 1):
- `switch_floor`: ∑ P_i² ≥ 1/n — нижняя граница
  нагрузочного члена;
- `switch_floor_eq_iff`: равенство ⟺ P равномерно
  (∀ i, P i = 1/n) — единственный минимум баланса
  достигается только равномерным роутингом.
-/

namespace Hagi.Model.SwitchMoE

open Finset

variable {n : ℕ}

/-- Нижняя граница нагрузочного члена: ∑ P² ≥ 1/n. -/
theorem switch_floor (P : Fin n → ℝ) (hsum : ∑ i, P i = 1)
    (hn : 0 < n) :
    1 / n ≤ ∑ i, (P i) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hd := Hagi.Foundations.SumIdentities.sq_decomp P hn 0
  simp only [sub_zero] at hd
  rw [hsum] at hd
  have hnn : 0 ≤ ∑ i, (P i - 1 / n) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hval : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by
    field_simp
  rw [hval] at hd
  linarith

/-- Равенство в границе ⟺ равномерное распределение. -/
theorem switch_floor_eq_iff (P : Fin n → ℝ)
    (hsum : ∑ i, P i = 1) (hn : 0 < n) :
    ∑ i, (P i) ^ 2 = 1 / n ↔ ∀ i, P i = 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · intro heq
    have hd := Hagi.Foundations.SumIdentities.sq_decomp P hn 0
    simp only [sub_zero] at hd
    rw [hsum] at hd
    have hval : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by
      field_simp
    rw [hval] at hd
    -- из heq и hd: ∑ (P i − 1/n)² = 0
    have hzero : ∑ i, (P i - 1 / n) ^ 2 = 0 := by linarith
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (P i - 1 / n) ^ 2 :=
      fun i _ => sq_nonneg _
    have hper : ∀ i ∈ Finset.univ, (P i - 1 / n) ^ 2 = 0 :=
      fun i _ =>
        Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp hzero i
          (Finset.mem_univ i)
    intro i
    have hz := hper i (Finset.mem_univ i)
    have hsub : P i - 1 / n = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hz
    exact sub_eq_zero.mp hsub
  · intro hunif
    have : ∀ i ∈ Finset.univ, (P i) ^ 2 = (1 / n) ^ 2 := by
      intro i _
      rw [hunif i]
    rw [Finset.sum_congr rfl this, Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin]
    field_simp

end Hagi.Model.SwitchMoE

/-!
# Адаптивный рост архитектуры (объединённый)

LoRA, Upcycling, Matryoshka, MoeExpansion, ReZero —
адаптеры и рост архитектуры. Слит из пяти модулей; имена
деклараций сохранены.
-/

/-!
# LoRA: низкоранговая адаптация (источник №35)

Источник №35: Hu et al., "LoRA: Low-Rank Adaptation of
Large Language Models" (arXiv 2106.09685). Адаптация
ΔW = B·A с рангом r ≪ min(m,n): обучается m·r + n·r
параметров вместо m·n — переиспользование замороженного
базового W.

Формализованное ядро (строгое):
- `lora_out`: выход адаптированной модели
  (W + B·A)·x = W·x + B·(A·x) — адаптация идёт через
  НИЗКОРАНГОВЫЙ канал B(A(·));
- `lora_kernel_preserved`: если A·x = 0 (адаптер не видит
  x), поведение модели НЕ МЕНЯЕТСЯ:
  (W + B·A)·x = W·x — LoRA сохраняет базу на всём, что
  вне охвата адаптера (аналог GPM zero-forgetting);
- `lora_param_saving`: при r ≤ mn/(m+n) число обучаемых
  параметров (m+n)·r не превосходит m·n — экономия против
  полного fine-tuning.
-/

namespace Hagi.Model.LoRA

open Matrix

variable {m n k : ℕ}

/-- Выход адаптированной модели. -/
theorem lora_out (W : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ) :
    (W + B * A) *ᵥ x = W *ᵥ x + B *ᵥ (A *ᵥ x) := by
  rw [add_mulVec]
  congr 1
  exact (mulVec_mulVec x B A).symm

/-- ЯДРО №35: адаптер не видит x ⟹ поведение неизменно. -/
theorem lora_kernel_preserved (W : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (A : Matrix (Fin k) (Fin n) ℝ) (x : Fin n → ℝ)
    (hAx : A *ᵥ x = 0) :
    (W + B * A) *ᵥ x = W *ᵥ x := by
  rw [lora_out W B A x, hAx]
  simp

/-- Экономия параметров: (m+n)·r ≤ m·n при малом ранге. -/
theorem lora_param_saving (m n r : ℕ)
    (hr : (m + n : ℕ) * r ≤ m * n) :
    (m * r + n * r : ℕ) ≤ m * n := by
  have hsplit : m * r + n * r = (m + n) * r := by ring
  omega

end Hagi.Model.LoRA

/-!
# Sparse Upcycling (источник №50)

Источник №50: Komatsuzaki et al., "Sparse Upcycling:
Training Mixture-of-Experts from Dense Checkpoints"
(arXiv 2210.06264). MoE инициализируется из dense-модели:
эксперты — копии FFN, роутер стартует равномерно: начальная
ФУНКЦИЯ модели сохраняется (переиспользование обучения).

Формализованное ядро (строгое):
- `upcycle_preserves`: если все эксперты — копии dense-FFN
  (f i = f) и роутер равномерен (P i = 1/n), то MoE-выход
  ∑ P i * f i = f — upcycling НЕ МЕНЯЕТ функцию модели в
  стартовой точке (вся предобученная функция наследуется).
-/

namespace Hagi.Model.Upcycling

open Finset

variable {n : ℕ}

/-- Равномерный роутер + идентичные эксперты сохраняют
dense-функцию. -/
theorem upcycle_preserves (fd : ℝ) (f : Fin n → ℝ)
    (hf : ∀ i, f i = fd) (_hn : 0 < n) :
    ∑ i, (1 / (n : ℝ)) * f i = fd := by
  have hconv : ∀ i ∈ Finset.univ,
      (1 / (n : ℝ)) * f i = (1 / (n : ℝ)) * fd :=
    fun i _ => by rw [hf i]
  rw [Finset.sum_congr rfl hconv, ← Finset.mul_sum,
    Finset.sum_const]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [Finset.card_univ, Fintype.card_fin]
  field_simp

end Hagi.Model.Upcycling

/-!
# Matryoshka Representation Learning (источник №44)

Источник №44: Kusupati et al., "Matryoshka Representation
Learning" (arXiv 2205.13147). Вложенные представления: первые
m координат эмбеддинга — сами по себе полноценное
представление (масштабируемая гранулярность: одно кодирование
обслуживает любой бюджет размерности).

Формализованное ядро (строгое):
- `matryoshka_norm_le`: норма (сумма квадратов) усечения
  m ≤ n НЕ превосходит полной нормы — иерархическая
  вложенность: усечение теряет не более чем «хвост»;
- `matryoshka_dist_le`: расстояние усечений ≤ расстояния
  полных векторов (усечение никогда не усиливает
  расстояние).
-/

namespace Hagi.Model.Matryoshka

open Finset

/-- Норма усечения не превосходит полной. -/
theorem matryoshka_norm_le (x : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, (x i) ^ 2
      ≤ ∑ i ∈ Finset.range n, (x i) ^ 2 := by
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hmn
    rw [hm0]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hmn with h | h
    · have h2 : m ≤ n := Nat.le_of_lt_succ h
      have hstep := ih h2
      rw [Finset.sum_range_succ]
      have hnn : 0 ≤ (x n) ^ 2 := sq_nonneg _
      linarith
    · rw [h]

/-- Расстояние усечений не превосходит расстояния полных
векторов. -/
theorem matryoshka_dist_le (x y : ℕ → ℝ) (m n : ℕ)
    (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, ((x i - y i)) ^ 2
      ≤ ∑ i ∈ Finset.range n, ((x i - y i)) ^ 2 :=
  matryoshka_norm_le (fun i => x i - y i) m n hmn

end Hagi.Model.Matryoshka

-- Cortex (arXiv 2610.20399v1) Appx A: MoE shared expansion.
open Finset

namespace Hagi.Model

/-!
Cortex (arXiv 2610.20399v1), Appx A.4/A.5: shared expansion в MoE.
Тождество (18): при Σ a_e(x) = 1 общая ветка S сворачивается в
каждого эксперта без изменения выхода: F + S = Σ a_e·(E_e + S).
-/

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- Тождество сворачивания shared-ветки (Prop A.5, eq. 18). -/
theorem moe_shared_expansion_identity
    {ι : Type*} [Fintype ι] (E : ι → V) (S : V) (a : ι → ℝ)
    (ha : ∑ e, a e = 1) :
    (∑ e, a e • E e) + S = ∑ e, a e • (E e + S) := by
  calc (∑ e, a e • E e) + S
      = (∑ e, a e • E e) + (∑ e, a e) • S := by rw [ha, one_smul]
    _ = (∑ e, a e • E e) + ∑ e, a e • S := by rw [Finset.sum_smul]
    _ = ∑ e, (a e • E e + a e • S) := Finset.sum_add_distrib.symm
    _ = ∑ e, a e • (E e + S) :=
          Finset.sum_congr rfl fun e _ => (smul_add (a e) (E e) S).symm


/-- Prop A.4 (Cortex, источник в заголовке модуля): shared down-projection
реализует цели Δ матрицей L (L * H = Δ) ⟺ каждая строка Δ —
линейная комбинация строк H (row(Δ) ⊆ row(H)). -/
theorem shared_down_projection_iff
    {m n p : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (Δ : Matrix (Fin p) (Fin n) ℝ) :
    (∃ L : Matrix (Fin p) (Fin m) ℝ, L * H = Δ)
      ↔ ∀ i : Fin p, ∃ c : Fin m → ℝ,
          ∀ j : Fin n, Δ i j = ∑ k : Fin m, c k * H k j := by
  constructor
  · rintro ⟨L, hL⟩ i
    refine ⟨fun k => L i k, fun j => ?_⟩
    have h1 : (L * H) i j = ∑ k : Fin m, L i k * H k j :=
      Matrix.mul_apply
    rw [← h1, ← hL]
  · intro h
    refine ⟨Matrix.of fun i k => (h i).choose k, ?_⟩
    funext i j
    have := (h i).choose_spec j
    simpa [Matrix.mul_apply] using this.symm


end Hagi.Model

/-!
# ReZero — обучаемая residual-масштабировка (источник №67:
# Bachlechner et al., "ReZero is All You Need: Fast
# Convergence at Large Depth", arXiv 2003.04887)

Идея: residual-блок x + α·f(x) с ОБУЧАЕМЫМ α,
инициализированным НУЛЁМ: в начале обучения каждый блок —
ТОЖДЕСТВО (глубокая сеть вырождается в residual-путь),
градиент течёт свободно; α вырастает по мере надобности.
Формализуем: init-тождество (α=0) и линейное по α
возмущение нормы.
-/

namespace Hagi.Model.ReZero

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- ReZero-блок: x + α·f x. -/
def rezeroStep (x fx : X) (alpha : ℝ) : X := x + alpha • fx

/-- ИСТОЧНИК №67, УРОВЕНЬ 1: INIT-ТОЖДЕСТВО — при α = 0
блок РАВЕН входу (глубокая сеть в инициализации — чистый
residual-путь; градиент беспрепятственно течёт по глубине). -/
theorem rezero_identity (x fx : X) :
    rezeroStep x fx 0 = x := by
  unfold rezeroStep
  simp

/-- УРОВЕНЬ 1b: ЛИНЕЙНОСТЬ ВОЗМУЩЕНИЯ ПО α — норма отклонения
блока от входа растёт ЛИНЕЙНО по |α| (малые α — малое
возмущение; управление глубиной через один скаляр). -/
theorem rezero_perturb_bound (x fx : X) (alpha : ℝ) :
    ‖rezeroStep x fx alpha - x‖ ≤ |alpha| * ‖fx‖ := by
  unfold rezeroStep
  rw [add_sub_cancel_left]
  exact le_of_eq (norm_smul alpha fx)

end Hagi.Model.ReZero
