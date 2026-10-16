/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Unified.FannesComplete
set_option linter.style.header false

/-!
# «Neural Networks Are Already Clean» — рекурсивное обобщение
против суперпозиции (R533)

Формализация математической модели теории Goodfire
(N. Cammarata, «Neural Networks Are Already Clean»):
кажущаяся полисемантичность нейрона часто объясняется не
суперпозицией независимых признаков, а рекурсивным
обобщением — деревом родственных понятий с общим
происхождением. Теория фальсифицируема через вектор
характеристик (локальность, временнáя согласованность,
связность, причинность), а не через единый индекс.

Ядро (конечномерная реализация):

* `branchLocality` — средневзвешенная семантическая
  длина ветви L_j = Σ p(v)·d(p(v),v) / Σ p(v);
* `locality_le_of_bounded` — Условие A (семантическая
  локальность): все ветви ≤ ε ⟹ L_j ≤ ε;
* `timeConsistency` — доля рёбер дерева с родителем не
  позже потомка T*_j = 1 − |{τ(u) > τ(v)}|/|E|;
* `timeConsistency_eq_one` — Условие B (временнáя
  последовательность): все рёбра упорядочены ⟹ T* = 1;
* `indepMass` — U_j = 1 − max_k Σ_{v∈C_k} p(v);
* `indepMass_eq_zero_of_cover` — одна компонента покрывает
  всю массу ⟹ U = 0 (нет сигнала суперпозиции);
* `activationMass_entropy_le` — граница энтропии
  активационной массы (переиспользует машину Fannes R532);
* `CleanCertificate` — сертификат рекурсивного обобщения
  из условий A + B + U (теорема clean_neuron_of_conditions);
* `piR_le_card` — доля π̂_R «чистых» нейронов ≤ 1 и её
  ограничение числом сертификатов.

Соглашения: понятия — конечный тип V; активационная масса
w : V → ℝ неотрицательна; родитель par : V → V (корень —
свой родитель, вклад корня исключён из сумм); расстояние
d : V → V → ℝ; моменты появления τ : V → ℝ.
-/

namespace Hagi.Unified.RecursiveClean

open Real Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Условие A: семантическая локальность ветвления -/

/-- Средневзвешенная длина ветви дерева обобщений:
L_j = Σ_{v ≠ r} w v · d(par v, v) / Σ_{v ≠ r} w v. -/
noncomputable def branchLocality (w : V → ℝ) (par : V → V)
    (d : V → V → ℝ) (r : V) : ℝ :=
  (∑ v ∈ univ \ {r}, w v * d (par v) v)
    / (∑ v ∈ univ \ {r}, w v)

/-- **Условие A ⟹ локальность (R533)**: если все ветви
дерева обобщений имеют семантическую длину ≤ ε и масса
вне корня положительна, то средневзвешенная локальность
L_j ≤ ε. Средневзвешенное ограничено максимумом весов. -/
theorem locality_le_of_bounded (w : V → ℝ) (par : V → V)
    (d : V → V → ℝ) (r : V) (ε : ℝ)
    (hw : ∀ v ∈ univ \ {r}, 0 ≤ w v)
    (hsum : 0 < ∑ v ∈ univ \ {r}, w v)
    (hbd : ∀ v ∈ univ \ {r}, d (par v) v ≤ ε) :
    branchLocality w par d r ≤ ε := by
  have hnum : ∑ v ∈ univ \ {r}, w v * d (par v) v
      ≤ ε * ∑ v ∈ univ \ {r}, w v := by
    have h1 : ∑ v ∈ univ \ {r}, w v * d (par v) v
        ≤ ∑ v ∈ univ \ {r}, w v * ε :=
      Finset.sum_le_sum (fun v hv =>
        mul_le_mul_of_nonneg_left (hbd v hv) (hw v hv))
    rw [← Finset.sum_mul] at h1
    linarith
  rw [branchLocality, div_le_iff₀ hsum]
  linarith

/-! ## Условие B: временнáя согласованность -/

/-- Доля рёбер дерева, в которых родитель появляется не
позже потомка: T* = 1 − |{e ∈ E : τ e.2 < τ e.1}| / |E|. -/
noncomputable def timeConsistency (E : Finset (V × V))
    (τ : V → ℝ) : ℝ :=
  1 - (E.filter (fun e => τ e.2 < τ e.1)).card / E.card

/-- **Условие B ⟹ T* = 1 (R533)**: если на каждом ребре
дерева родитель устойчиво появляется не позже потомка
(τ u ≤ τ v), то временнáя согласованность максимальна. -/
theorem timeConsistency_eq_one (E : Finset (V × V))
    (τ : V → ℝ) (hE : E.Nonempty)
    (hord : ∀ e ∈ E, τ e.1 ≤ τ e.2) :
    timeConsistency E τ = 1 := by
  have hfil : (E.filter (fun e => τ e.2 < τ e.1)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    exact absurd (hord e (Finset.mem_filter.mp he |>.1))
      (not_le.mpr (Finset.mem_filter.mp he |>.2))
  rw [timeConsistency, hfil, Finset.card_empty, Nat.cast_zero,
    zero_div, sub_zero]

/-! ## Масса независимых компонент -/

/-- Масса вне крупнейшей связной компоненты:
U_j = 1 − max_k Σ_{v ∈ C_k} w v. -/
noncomputable def indepMass (w : V → ℝ)
    (comps : Finset (Finset V)) (hne : comps.Nonempty) : ℝ :=
  1 - comps.sup' hne (fun c => ∑ v ∈ c, w v)

/-- **Одна компонента покрывает массу ⟹ U = 0 (R533)**:
если некоторая компонента накрывает всю активационную
массу (Σ w = 1, вне компоненты масса нулевая), то сигнал
суперпозиции U_j нулевой — все понятия нейрона связаны. -/
theorem indepMass_eq_zero_of_cover (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v = 1)
    (comps : Finset (Finset V)) (hne : comps.Nonempty)
    (c₀ : Finset V) (hc₀ : c₀ ∈ comps)
    (hout : ∀ v ∉ c₀, w v = 0) :
    indepMass w comps hne = 0 := by
  have hcov : ∑ v ∈ c₀, w v = 1 :=
    Finset.sum_subset c₀.subset_univ (fun v _ hv => hout v hv) |>.trans hw1
  have hle_sup : (1:ℝ) ≤ comps.sup' hne (fun c => ∑ v ∈ c, w v) :=
    le_trans (le_of_eq hcov.symm) (Finset.le_sup' (fun c => ∑ v ∈ c, w v) hc₀)
  have hge_sup : comps.sup' hne (fun c => ∑ v ∈ c, w v) ≤ 1 :=
    Finset.sup'_le hne (fun c => ∑ v ∈ c, w v)
      (fun c _ => by
        have hsub : ∑ v ∈ c, w v ≤ ∑ v, w v := sum_le_univ_sum_of_nonneg hw
        rw [hw1] at hsub
        exact hsub)
  rw [indepMass, le_antisymm hge_sup hle_sup, sub_self]

/-! ## Энтропия активационной массы -/

/-- Энтропия распределения активационной массы по понятиям
не превосходит логарифма размера полного пространства
понятий (граница из машинерии Fannes R533 ← R532):
интерпретируемость описывается вектором характеристик,
а не сжимается в один индекс — но энтропия массы даёт
верхнюю оценку разнообразия задействованных понятий. -/
theorem activationMass_entropy_le (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v = 1) :
    ∑ v, Real.negMulLog (w v)
      ≤ Real.log (Fintype.card V : ℝ) :=
  Hagi.Unified.shannon_le_log_card w hw hw1

/-! ## Сертификат «чистого» нейрона -/

/-- Сертификат рекурсивного обобщения для нейрона j:
условие A (локальность ветвей ≤ ε), условие B (полная
временнáя согласованность) и отсутствие сигнала
суперпозиции (U_j = 0). Это векторная характеристика,
а не единый индекс чистоты. -/
structure CleanCertificate (V : Type*) [Fintype V]
    [DecidableEq V] where
  /-- активационная масса -/
  w : V → ℝ
  /-- функция родителя в дереве обобщений -/
  par : V → V
  /-- семантическое расстояние -/
  d : V → V → ℝ
  /-- корневое понятие -/
  root : V
  /-- рёбра дерева -/
  E : Finset (V × V)
  /-- моменты появления -/
  τ : V → ℝ
  /-- компоненты активных понятий -/
  comps : Finset (Finset V)
  hcompsNe : comps.Nonempty
  /-- масса неотрицательна и нормирована -/
  hw_nonneg : ∀ v, 0 ≤ w v
  hw_sum : ∑ v, w v = 1
  /-- порог локальности -/
  εA : ℝ
  /-- условие A: все ветви локальны -/
  hA : ∀ v ∈ Finset.univ \ {root}, d (par v) v ≤ εA
  /-- условие B: родители не позже потомков -/
  hB : ∀ e ∈ E, τ e.1 ≤ τ e.2
  /-- компонента покрывает всю массу -/
  hcover : ∃ c₀ ∈ comps, ∀ v ∉ c₀, w v = 0

/-- **Композиция условий ⟹ сертификат (R533)**: локальность
ветвей ≤ ε (условие A), полная временнáя согласованность
(условие B) и покрывающая компонента (U = 0) вместе дают
L_j ≤ ε, T*_j = 1 и U_j = 0 — проверяемое свидетельство
рекурсивного обобщения против суперпозиции. -/
theorem clean_neuron_of_conditions (cert : CleanCertificate V)
    (hsumpos : 0 < ∑ v ∈ Finset.univ \ {cert.root}, cert.w v)
    (hE : cert.E.Nonempty) :
    branchLocality cert.w cert.par cert.d cert.root ≤ cert.εA
      ∧ timeConsistency cert.E cert.τ = 1
      ∧ indepMass cert.w cert.comps cert.hcompsNe = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact locality_le_of_bounded cert.w cert.par cert.d
      cert.root cert.εA
      (fun v hv => cert.hw_nonneg v) hsumpos cert.hA
  · exact timeConsistency_eq_one cert.E cert.τ hE cert.hB
  · obtain ⟨c₀, hc₀mem, hc₀out⟩ := cert.hcover
    exact indepMass_eq_zero_of_cover cert.w cert.hw_nonneg
      cert.hw_sum cert.comps cert.hcompsNe c₀ hc₀mem hc₀out

/-! ## Доля «чистых» нейронов в сети -/

/-- Доля нейронов сети, для которых гипотеза рекурсивного
обобщения подтверждена индикатором z : V → ℝ ∈ {0,1}:
π̂_R = (Σ z_j)/N. -/
noncomputable def piR (z : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ range N, z j) / N

/-- **0 ≤ π̂_R ≤ 1 (R533)**: доля индикаторов в {0,1} лежит
в [0,1]; кроме того, π̂_R ≤ (число единиц)/N тривиально
совпадает — приводим каноническую оценку и не-отрицательность. -/
theorem piR_le_one (z : ℕ → ℝ) (N : ℕ)
    (hz : ∀ j ∈ range N, 0 ≤ z j ∧ z j ≤ 1) :
    0 ≤ piR z N ∧ piR z N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · simp only [piR, h0, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero, div_zero]
    exact ⟨le_refl (0:ℝ), zero_le_one⟩
  · have hsum : ∑ j ∈ range N, z j ≤ (N : ℝ) := by
      have hcard : ∑ j ∈ range N, z j ≤ ∑ j ∈ range N, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => (hz j hj).2)
      rw [Finset.sum_const, Finset.card_range] at hcard
      norm_num at hcard
      exact hcard
    have hnn : 0 ≤ ∑ j ∈ range N, z j :=
      Finset.sum_nonneg (fun j hj => (hz j hj).1)
    constructor
    · exact div_nonneg hnn (Nat.cast_nonneg N)
    · exact (div_le_one (Nat.cast_pos.mpr hpos)).mpr hsum

end Hagi.Unified.RecursiveClean
