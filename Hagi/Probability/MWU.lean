import Hagi.Probability.GibbsConcentration
import Hagi.Probability.FreedmanTwoSided

namespace Hagi.Probability


/-!
# MWU — мост к multiplicative weights (R433–)

Одношаговый потенциал-анализ экспоненциальных весов
(hedge-ядро без рядов, RAG-опора: arXiv 2608.09389,
EW-regret ≤ M√(2 ln A·T)). База: R432
(gibbs_energy_gap_crude). Здесь: логарифм
нормировочной константы после одного обновления
весов контролируется потерями:
ln Z' ≥ −2η·⟨ℓ⟩_w при η·ℓ ≤ 1/2.
Ключ: (1+2x)(1−x) ≥ 1 при x ≤ 1/2 ⟹
e^{−2x} ≤ 1−x (без calculus).
-/

open Finset Real

theorem mwu_potential_step {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≥ -2 * η * (∑ v, w v * ℓ v) := by
  set L : ℝ := ∑ v, w v * ℓ v with hL
  -- per-v: 1 - ηℓ v <= exp(-(η ℓ v))
  have hper : ∀ v : V, 1 - η * ℓ v ≤ Real.exp (-(η * ℓ v)) :=
    fun v => Real.one_sub_le_exp_neg (η * ℓ v)
  -- weighted: sum w (1 - ηℓ) <= Z'
  have hsum1 : ∑ v, w v * (1 - η * ℓ v)
      ≤ ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- sum w (1 - ηℓ) = 1 - η L
  have hterm : ∀ v : V, w v * (1 - η * ℓ v)
      = w v - w v * (η * ℓ v) := fun v => by ring
  have hsplit : ∑ v, w v * (1 - η * ℓ v)
      = ∑ v, w v - ∑ v, w v * (η * ℓ v) := by
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_sub_distrib]
  have hmul : ∑ v, w v * (η * ℓ v) = η * L := by
    rw [hL, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hw1] at hsplit
  rw [hsplit, hmul] at hsum1
  -- x := η L in [0, 1/2]
  have hLnn : (0:ℝ) ≤ L :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (le_of_lt (hw v)) (hℓ v))
  have hx : (0:ℝ) ≤ η * L := mul_nonneg (le_of_lt hη) hLnn
  have hxle : η * L ≤ 1/2 := by
    -- η L = Σ w (η ℓ) <= Σ w (1/2) = 1/2
    have hterm2 : ∀ v : V, w v * (η * ℓ v) ≤ w v * (1/2) :=
      fun v => mul_le_mul_of_nonneg_left (hsmall v) (le_of_lt (hw v))
    calc η * L = ∑ v, w v * (η * ℓ v) := hmul.symm
      _ ≤ ∑ v, w v * (1/2) := Finset.sum_le_sum (fun v _ => hterm2 v)
      _ = 1/2 := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) ((1:ℝ)/2)),
            ← Finset.mul_sum, hw1, mul_one]
  -- exp(-2x) <= 1 - x for x in [0, 1/2]
  have he2 : Real.exp (-(2*(η*L))) ≤ 1 - η*L := by
    have h1 := Real.add_one_le_exp (2*(η*L))
    have hmul2 : (1 + 2*(η*L)) * (1 - η*L) ≥ 1 := by
      have hxs : (η*L)^2 ≤ (η*L)/2 := by nlinarith [hxle, hx]
      nlinarith [hxs, hx]
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ (exp_pos (2*(η*L)))).mpr
      (by nlinarith [h1, hmul2,
        mul_nonneg (exp_pos (2*(η*L))).le (show (0:ℝ) ≤ 1 - η*L by linarith)])
  -- log chain
  have hlog := Real.log_le_log (exp_pos (-(2*(η*L)))) (le_trans he2 hsum1)
  rw [Real.log_exp] at hlog
  linarith

/-- **Нижняя грань потенциала (R434)**:
ln Z' ≤ −η·ℓ_min — вклад минимизатора
потерь доминирует:
e^{−ηℓ_v} ≤ e^{−ηℓ_min} почленно ⟹
Z' ≤ e^{−ηℓ_min}. Вместе с R433
(верхняя грань): −η·ℓ_min
≤ −ln Z' ≤ 2η·⟨ℓ⟩_w — потенциал
зажат с обеих сторон. -/
theorem mwu_potential_lower {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hη : 0 < η) :
    ∃ vmin : V, Real.log (∑ v, w v * Real.exp (-(η * ℓ v)))
      ≤ -(η * ℓ vmin) := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  -- per-v: exp(-(η ℓ v)) <= exp(-(η ℓ vmin))
  have hper : ∀ v : V, Real.exp (-(η * ℓ v)) ≤ Real.exp (-(η * ℓ vmin)) := by
    intro v
    apply Real.exp_le_exp.mpr
    have h1 : ℓ vmin ≤ ℓ v := hvmin v
    have h2 : -(η * ℓ v) ≤ -(η * ℓ vmin) := by
      have : η * ℓ vmin ≤ η * ℓ v :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hη)
      linarith
    exact h2
  -- weighted sum bound
  have hsum : ∑ v, w v * Real.exp (-(η * ℓ v))
      ≤ ∑ v, w v * Real.exp (-(η * ℓ vmin)) :=
    Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hper v) (le_of_lt (hw v)))
  -- = exp(...) * sum w = exp(...)
  have hsplit : ∑ v, w v * Real.exp (-(η * ℓ vmin))
      = Real.exp (-(η * ℓ vmin)) * ∑ v, w v := by
    rw [Finset.sum_congr rfl (fun v _ => mul_comm (w v) (Real.exp (-(η * ℓ vmin)))),
      Finset.mul_sum]
  rw [hw1, mul_one] at hsplit
  rw [hsplit] at hsum
  -- log mono
  have hZpos : (0:ℝ) < ∑ v, w v * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (hw v) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hlog := Real.log_le_log hZpos hsum
  rwa [Real.log_exp] at hlog

/-- **Сертификат зажатия потенциала
(R435)**: η·ℓ_min ≤ −ln Z' ≤ 2η·⟨ℓ⟩_w —
одна теорема для потребителя
(композиция R434 + R433).
Следствие: ℓ_min ≤ 2⟨ℓ⟩_w —
одношаговая гарантия
без-регретности; многошаговый
телескоп построится на
ней индукцией. -/
theorem mwu_potential_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (w : V → ℝ) (ℓ : V → ℝ) (η : ℝ)
    (hw : ∀ v, 0 < w v) (hw1 : ∑ v, w v = 1)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v, w v * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v, w v * ℓ v) := by
  obtain ⟨vmin, hlow⟩ := mwu_potential_lower w ℓ η hw hw1 hη
  have hhigh := mwu_potential_step w ℓ η hw hw1 hℓ hη hsmall
  refine ⟨vmin, ?_, ?_⟩
  · linarith
  · linarith

/-- **MWU с uniform-стартом (R436)**:
специализация R435 на веса
1/n — классический hedge с
равномерным начальным
распределением над
экспертами V. Кумулятивные
потери ℓ := L (сумма по шагам)
дают телескопический
потенциал: η·L_min ≤ −ln W ≤
2η·⟨L⟩_{unif}. -/
theorem mwu_uniform_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V, η * ℓ vmin
      ≤ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
      ∧ -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v) := by
  have hw : ∀ v : V, (0:ℝ) < 1/(Fintype.card V : ℝ) := by
    intro v
    apply div_pos (by norm_num)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hw1 : ∑ v : V, (1/(Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
    rw [nsmul_eq_mul, one_div, mul_inv_cancel₀ (ne_of_gt hn)]
  exact mwu_potential_squeeze (fun _ => 1/(Fintype.card V : ℝ)) ℓ η hw hw1 hℓ hη hsmall

/-- **Классический ln n-член (R437)**:
−ln W ≤ ln n + η·L_min для uniform-hedge
(W ≥ (1/n)·e^{−ηL_min} через
один член суммы).
Вместе с R436 (верхняя
2η-грань): полная regret-пара
для экспоненциальных
весов: ln n + ηL_min ≥ −ln W ≥ ηL_min —
запас на инициализацию ровно
ln n. -/
theorem mwu_potential_upper_uniform {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ vmin : V, -(Real.log (∑ v : V, (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v))))
      ≤ Real.log (Fintype.card V : ℝ) + η * ℓ vmin := by
  obtain ⟨vmin, hvmin⟩ : ∃ vmin : V, ∀ v : V, ℓ vmin ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset V) ℓ
      Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  refine ⟨vmin, ?_⟩
  have hn : (0:ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
  have hZpos : (0:ℝ) < ∑ v : V, (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)) :=
    Finset.sum_pos (fun v _ => mul_pos (by positivity) (exp_pos _))
      ⟨vmin, Finset.mem_univ _⟩
  have hsingle : (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ vmin))
      ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ v)) :=
    single_le_sum (f := fun v => (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ v)))
      (fun v _ => mul_nonneg (by positivity) (exp_pos _).le)
      (Finset.mem_univ vmin)
  have hpos2 : (0:ℝ) < (1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)) :=
    mul_pos (by positivity) (exp_pos _)
  have hlog := Real.log_le_log hpos2 hsingle
  have hsplit : Real.log ((1/(Fintype.card V : ℝ))
      * Real.exp (-(η * ℓ vmin)))
      = -(Real.log (Fintype.card V : ℝ) + η * ℓ vmin) := by
    have hne1 : (1/(Fintype.card V : ℝ)) ≠ 0 := by positivity
    have hne2 : Real.exp (-(η * ℓ vmin)) ≠ 0 := by positivity
    rw [Real.log_mul hne1 hne2, Real.log_exp,
      Real.log_div (one_ne_zero) (ne_of_gt hn), Real.log_one,
      zero_sub, neg_add_eq_sub]
    ring
  rw [hsplit] at hlog
  linarith

/-- **Телескоп MWU-весов (R438)**:
∏_{t<T} e^{−η·ℓ_t(v)} = e^{−η·∑_{t<T} ℓ_t(v)}
(индукция, exp_add). Замкнутая
форма ненормированных
экспоненциальных весов:
u_T(v) = e^{−ηL_v}. Соединяется с
R436/R437 (W = (1/n)∑ e^{−ηL_v}) — полная
многошаговая механика. -/
theorem mwu_prod_exp {V : Type*} (ℓs : ℕ → V → ℝ) (η : ℝ)
    (T : ℕ) (v : V) :
    ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))
      = Real.exp (-(η * ∑ t ∈ Finset.range T, ℓs t v)) := by
  induction T with
  | zero => simp
  | succ t ih =>
    rw [Finset.prod_range_succ_comm, Finset.sum_range_succ, ih,
      ← Real.exp_add]
    congr 1
    ring

/-- **Замкнутая форма разбиения (R439)**:
∑_v ∏_t e^{−ηℓ_t(v)} = ∑_v e^{−ηL_v}
(почленная композиция R438).
Ненормированная статистика
алгоритма — чисто
Гиббс-статистика
кумулятивных потерь:
мост MWU ↔ Гиббс замыкается
на уровне разбиения. -/
theorem mwu_partition_sum {V : Type*} [Fintype V] (ℓs : ℕ → V → ℝ) (η : ℝ)
    (T : ℕ) :
    ∑ v : V, ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))
      = ∑ v : V, Real.exp (-(η * ∑ t ∈ Finset.range T, ℓs t v)) :=
  Finset.sum_congr rfl (fun v _ => mwu_prod_exp ℓs η T v)

/-- **Статический MWU-regret (R440)**:
потенциал в произведенческой
форме зажат:
ηL_min ≤ −ln((1/n)∑∏ e^{−ηℓ_t})
  ≤ 2η·⟨L⟩_unif
(R439-перепись + R436 на
кумулятивных потерях).
Полная многошаговая
механика MWU сведена к
одношаговому сертификату. -/
theorem mwu_regret_static {V : Type*} [Fintype V]
    [Nonempty V] (ℓs : ℕ → V → ℝ) (η : ℝ) (T : ℕ)
    (hℓ : ∀ t ∈ Finset.range T, ∀ v, 0 ≤ ℓs t v)
    (hη : 0 < η)
    (hsmall : ∀ v, η * (∑ t ∈ Finset.range T, ℓs t v) ≤ 1/2) :
    ∃ vmin : V,
      η * (∑ t ∈ Finset.range T, ℓs t vmin)
        ≤ -(Real.log ((1/(Fintype.card V : ℝ))
            * ∑ v : V, ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))))
      ∧ -(Real.log ((1/(Fintype.card V : ℝ))
            * ∑ v : V, ∏ t ∈ Finset.range T, Real.exp (-(η * ℓs t v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ))
            * ∑ t ∈ Finset.range T, ℓs t v) := by
  -- rewrite product form to Gibbs form via R439
  rw [mwu_partition_sum ℓs η T, Finset.mul_sum]
  have hLnn : ∀ v : V, 0 ≤ ∑ t ∈ Finset.range T, ℓs t v :=
    fun v => Finset.sum_nonneg (fun t ht => hℓ t ht v)
  exact mwu_uniform_squeeze (fun v => ∑ t ∈ Finset.range T, ℓs t v) η
    hLnn hη hsmall

/-- **Гиббс = hedge при η = 1/T (R441)** —
мост вертикалей:
hedge-сертификат Гиббс-статистики:
(1/T)E_min ≤ −ln((1/n)∑e^{−E/T}) ≤
2(1/T)⟨E⟩_unif. Температура —
обратный learning rate: охлаждение
термостата = ускорение
обучения. Вся MWU-механика
(R432-R440) автоматически
переносится на термодинамику. -/
theorem gibbs_hedge_squeeze {V : Type*} [Fintype V]
    [Nonempty V] (E : V → ℝ) (T : ℝ) (hT : 0 < T)
    (hE : ∀ v, 0 ≤ E v)
    (hsmall : ∀ v, (1/T) * E v ≤ 1/2) :
    ∃ vmin : V, (1/T) * E vmin
      ≤ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(E v)/T)))
      ∧ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(E v)/T)))
        ≤ 2 * (1/T) * (∑ v : V, (1/(Fintype.card V : ℝ)) * E v) := by
  have hkey : ∀ v : V, Real.exp (-(E v)/T)
      = Real.exp (-((1/T) * E v)) := by
    intro v
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun v _ => hkey v), Finset.mul_sum]
  have hη : (0:ℝ) < 1/T := by positivity
  exact mwu_uniform_squeeze E (1/T) hE hη hsmall
/-- **Двойная верхняя грань (R443)**:
−ln W ≤ min(2η·⟨ℓ⟩_unif,
ln n + η·ℓ_min) — две
конкурирующие оценки
в одной теореме:
база для η-оптимизации
(уравнивание двух членов даёт
классический оптимальный
learning rate). -/
theorem mwu_double_upper {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2) :
    ∃ vmin : V,
      -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v))))
        ≤ 2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
      ∧ -(Real.log ((1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v))))
        ≤ Real.log (Fintype.card V : ℝ) + η * ℓ vmin := by
  obtain ⟨_, _, h2⟩ := mwu_uniform_squeeze ℓ η hℓ hη hsmall
  rw [← Finset.mul_sum] at h2
  obtain ⟨vmin, h3⟩ := mwu_potential_upper_uniform ℓ η hη
  rw [← Finset.mul_sum] at h3
  exact ⟨vmin, h2, h3⟩

/-- **η-сбалансированная граница (R444)**:
−ln W ≤ 2√(η·⟨ℓ⟩·ln n) при
η·⟨ℓ⟩ ≤ ln n (равновесие
двух оценок R443 через
среднее геометрическое:
f ≤ X, f ≤ Y, f ≥ 0 ⟹ f² ≤ XY;
Y ≤ 2 ln n при балансе).
Классическая структура
regret-границ MWU. -/
theorem mwu_sqrt_bound {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2)
    (hn : (0:ℝ) < Real.log (Fintype.card V : ℝ))
    (hbal : η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
      ≤ Real.log (Fintype.card V : ℝ)) :
    -(Real.log ((1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v))))
      ≤ 2 * Real.sqrt (η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
        * Real.log (Fintype.card V : ℝ)) := by
  obtain ⟨_, h2, _⟩ := mwu_double_upper ℓ η hℓ hη hsmall
  set Lbar : ℝ := ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v with hL
  -- explicit minimizer
  obtain ⟨v0, hv0⟩ : ∃ v0 : V, ∀ v : V, ℓ v0 ≤ ℓ v := by
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image
      (Finset.univ : Finset V) ℓ Finset.univ_nonempty
    exact ⟨a, fun v => ha v (Finset.mem_univ v)⟩
  have hLnn : (0:ℝ) ≤ Lbar :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (by positivity) (hℓ v))
  -- direct bound: -log W <= log n + eta * Lbar
  have hminle : ℓ v0 ≤ Lbar := by
    have hsumle : (Fintype.card V : ℝ)
        * ((1/(Fintype.card V : ℝ)) * ℓ v0)
        ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v := by
      calc (Fintype.card V : ℝ)
          * ((1/(Fintype.card V : ℝ)) * ℓ v0)
          = ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v0 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v :=
            Finset.sum_le_sum (fun v _ =>
              mul_le_mul_of_nonneg_left (hv0 v) (by positivity))
    have hrewrite : (Fintype.card V : ℝ)
        * ((1/(Fintype.card V : ℝ)) * ℓ v0) = ℓ v0 := by
      field_simp
    rw [hrewrite] at hsumle
    rw [hL]
    exact hsumle
  set f : ℝ := -(Real.log ((1/(Fintype.card V : ℝ))
      * ∑ v : V, Real.exp (-(η * ℓ v)))) with hfdef
  have hη0 : (0:ℝ) ≤ η := le_of_lt hη
  have hf : (0:ℝ) ≤ f := by
    have hW : (1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v)) ≤ 1 := by
      have hle : ∑ v : V, Real.exp (-(η * ℓ v))
          ≤ (Fintype.card V : ℝ) := by
        calc ∑ v : V, Real.exp (-(η * ℓ v))
            ≤ ∑ v : V, (1:ℝ) :=
              Finset.sum_le_sum (fun v _ =>
                Real.exp_le_one_iff.mpr
                  (neg_nonpos.mpr (mul_nonneg hη0 (hℓ v))))
          _ = (Fintype.card V : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                mul_one]
      have hnn : (0:ℝ) < (Fintype.card V : ℝ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
      have hone : (1/(Fintype.card V : ℝ))
          * (Fintype.card V : ℝ) = 1 := by field_simp
      have hstep := mul_le_mul_of_nonneg_left hle
        (by positivity : (0:ℝ) ≤ 1/(Fintype.card V : ℝ))
      have := hstep.trans_eq hone
      exact this
    have hWpos : (0:ℝ) < (1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v)) :=
      mul_pos (by positivity)
        (Finset.sum_pos (fun v _ => exp_pos _) ⟨v0, Finset.mem_univ _⟩)
    have hlog := Real.log_le_log hWpos hW
    rw [Real.log_one] at hlog
    simp only [hfdef]
    linarith
  have hupper2 : f
      ≤ Real.log (Fintype.card V : ℝ) + η * Lbar := by
    have hstep : η * ℓ v0 ≤ η * Lbar :=
      mul_le_mul_of_nonneg_left hminle hη0
    have hsingle : (1/(Fintype.card V : ℝ)) * Real.exp (-(η * ℓ v0))
        ≤ (1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v)) := by
      rw [Finset.mul_sum]
      exact single_le_sum
        (f := fun v => (1/(Fintype.card V : ℝ))
          * Real.exp (-(η * ℓ v)))
        (fun v _ => mul_nonneg (by positivity) (exp_pos _).le)
        (Finset.mem_univ v0)
    have hpos2 : (0:ℝ) < (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v0)) :=
      mul_pos (by positivity) (exp_pos _)
    have hlog := Real.log_le_log hpos2 hsingle
    have hsplit : Real.log ((1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v0)))
        = -(Real.log (Fintype.card V : ℝ) + η * ℓ v0) := by
      have hne1 : (1/(Fintype.card V : ℝ)) ≠ 0 := by positivity
      have hne2 : Real.exp (-(η * ℓ v0)) ≠ 0 := by positivity
      have hnn : (0:ℝ) < (Fintype.card V : ℝ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Classical.arbitrary V⟩)
      rw [Real.log_mul hne1 hne2, Real.log_exp,
        Real.log_div (one_ne_zero) (ne_of_gt hnn), Real.log_one,
        zero_sub, neg_add_eq_sub]
      ring
    rw [hsplit] at hlog
    simp only [hfdef] at hlog ⊢
    linarith
  -- geometric combination: f^2 <= X * Y with X = 2 eta Lbar, Y = log n + eta Lbar
  have hXY : f * f ≤ (2 * η * Lbar) * (Real.log (Fintype.card V : ℝ)
      + η * Lbar) :=
    mul_le_mul h2 hupper2 hf
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη0) hLnn)
  -- Y <= 2 log n
  have hY : Real.log (Fintype.card V : ℝ) + η * Lbar
      ≤ 2 * Real.log (Fintype.card V : ℝ) := by linarith
  have hprod : (2 * η * Lbar) * (Real.log (Fintype.card V : ℝ) + η * Lbar)
      ≤ (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))) := by
    have hsq : (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        = 4 * (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
      have h1 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ η * Lbar
        * Real.log (Fintype.card V : ℝ))
      calc (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
          * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
          = 4 * (Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))
            * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ))) := by
            ring
        _ = 4 * (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
            rw [← sq, h1]
    rw [hsq]
    nlinarith [hbal, hLnn, hn, le_of_lt hη, hY]
  -- f = sqrt(f^2) <= sqrt(prod) = 2 sqrt(...)
  have hfsq : Real.sqrt (f * f) = f := by
    rw [← sq f, Real.sqrt_sq hf]
  rw [← hfsq]
  calc Real.sqrt (f * f)
      ≤ Real.sqrt ((2 * η * Lbar) * (Real.log (Fintype.card V : ℝ)
        + η * Lbar)) := Real.sqrt_le_sqrt hXY
    _ ≤ Real.sqrt ((2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))
        * (2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)))) :=
        Real.sqrt_le_sqrt hprod
    _ = 2 * Real.sqrt (η * Lbar * Real.log (Fintype.card V : ℝ)) := by
        have h2 := Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.sqrt
          (η * Lbar * Real.log (Fintype.card V : ℝ)))
        rw [← sq, h2]

open Finset Real in
/-- **Двухрежимный regret-капстоун
MWU (R468)**: безусловная
объединённая граница:
−ln((1/n)∑e^{−ηℓ}) ≤
max(2√(η〈ℓ〉·ln n),
2η〈ℓ〉).
Малый режим (η〈ℓ〉 ≤ ln n):
√-балансировка R444;
большой — линейная
одношаговая R436.
Выбор η = √(ln n/〈ℓ〉)
даёт классический
2√(〈ℓ〉·ln n) regret. -/
theorem mwu_regret_regimes {V : Type*} [Fintype V]
    [Nonempty V] (ℓ : V → ℝ) (η : ℝ)
    (hℓ : ∀ v, 0 ≤ ℓ v) (hη : 0 < η)
    (hsmall : ∀ v, η * ℓ v ≤ 1/2)
    (hn : (0:ℝ) < Real.log (Fintype.card V : ℝ)) :
    -(Real.log ((1/(Fintype.card V : ℝ))
        * ∑ v : V, Real.exp (-(η * ℓ v))))
    ≤ max (2 * Real.sqrt (η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
        * Real.log (Fintype.card V : ℝ)))
      (2 * η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)) := by
  by_cases hbal : η * (∑ v : V, (1/(Fintype.card V : ℝ)) * ℓ v)
      ≤ Real.log (Fintype.card V : ℝ)
  · have h := mwu_sqrt_bound ℓ η hℓ hη hsmall hn hbal
    exact le_max_of_le_left h
  · obtain ⟨_, _, h2⟩ := mwu_uniform_squeeze ℓ η hℓ hη hsmall
    have hb : (∑ v : V, (1/(Fintype.card V : ℝ))
        * Real.exp (-(η * ℓ v)))
        = (1/(Fintype.card V : ℝ))
          * ∑ v : V, Real.exp (-(η * ℓ v)) :=
      (Finset.mul_sum Finset.univ
        (fun v => Real.exp (-(η * ℓ v)))
        (1/(Fintype.card V : ℝ))).symm
    refine le_max_of_le_right ?_
    rw [← hb]
    exact h2


open Classical in
/-- The selected inverse-weighted loss collapses to the fixed target loss by
finite-sum cancellation. This finite-sum identity uses no normalization,
nonnegativity or nonempty hypothesis. -/
theorem selectedLoss_sum_real {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  simp_rw [mul_ite, mul_zero]
  rw [Fintype.sum_ite_eq' b]
  exact mul_div_cancel₀ (ℓ b) hb

open Classical in
/-- Under a PMF, observing only a selected action's loss with inverse
propensity yields exactly its expectation for each fixed arm with positive
selection probability.  This is not a variance or learning-regret claim. -/
theorem pmfMean_selectedLoss {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  have hbReal : (p b).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
  exact selectedLoss_sum_real (fun a => (p a).toReal) ℓ b hbReal


open scoped Classical in
/-- If a target loss is zero, its selected inverse-weighted estimator is zero
even when that target has zero propensity. Otherwise nonzero propensity
suffices: zero-loss arms need not be observed. -/
theorem selectedLoss_sum_real_support {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  rcases hb with hb | hzero
  · exact selectedLoss_sum_real p ℓ b hb
  · simp_rw [mul_ite, mul_zero]
    rw [Fintype.sum_ite_eq' b]
    simp [hzero]

open scoped Classical in
/-- Finite-PMF unbiasedness only needs the propensity required to recover
that fixed target. A zero target can have zero selection probability. -/
theorem pmfMean_selectedLoss_support {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  exact selectedLoss_sum_real_support (fun a => (p a).toReal) ℓ b
    (hb.imp (fun hb => ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩)
      (fun hzero => hzero))

open scoped Classical in
/-- Exact finite variance of one selected inverse-propensity observation.
At zero target loss, both sides are zero even at zero propensity. This is
not a variance upper bound or a claim of reduced computational cost. -/
theorem pmfMean_selectedLoss_variance {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
      - (pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0)) ^ 2
      = (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
  have hmean :
      pmfMean p (fun a =>
        if a = b then ℓ a / (p a).toReal else 0) = ℓ b :=
    pmfMean_selectedLoss_support p ℓ b hb
  rw [hmean]
  by_cases hpb : p b = 0
  · have hzeroLoss : ℓ b = 0 :=
      hb.elim (fun hne => (hne hpb).elim) (fun hzero => hzero)
    have hzero : ∀ a,
        (if a = b then ℓ a / (p a).toReal else 0) = 0 := by
      intro a
      split_ifs with ha
      · subst a
        simp [hzeroLoss]
      · rfl
    simp [pmfMean, hzero, hzeroLoss]
  · have hpbReal : (p b).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hpb, p.apply_ne_top b⟩
    have hmoment :
        pmfMean p (fun a =>
          (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
          = (ℓ b) ^ 2 / (p b).toReal := by
      calc
        pmfMean p (fun a =>
            (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
            = ∑ a, if a = b then
                (p a).toReal * (ℓ a / (p a).toReal) ^ 2 else 0 := by
          simp only [pmfMean]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp [div_pow]
        _ = (p b).toReal * (ℓ b / (p b).toReal) ^ 2 := by
          rw [Fintype.sum_ite_eq' b]
        _ = (ℓ b) ^ 2 / (p b).toReal := by
          rw [div_pow]
          field_simp [hpbReal]
    rw [hmoment]
    ring


open scoped Classical

/-- One selected observation's expected sum of coordinate-wise squared
errors for a fixed finite loss vector. PmfMean is linear, so this also
expresses its expected Euclidean squared error; no independence claim. -/
noncomputable def selectedLossMSE {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : ℝ :=
  ∑ b, pmfMean p (fun a =>
    ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)

/-- Loss-magnitude-proportional propensity. The positive normalizer
ensures a genuine PMF, including zero propensity for zero losses.
This normalized construction is for one fixed finite loss vector. -/
noncomputable def selectedLoss_optimalPropensity {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) : PMF V := by
  let q : V → ℝ := fun i => |ℓ i| / ∑ a, |ℓ a|
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (abs_nonneg (ℓ i)) hL.le
  have hq_sum : ∑ i, q i = 1 := by
    dsimp [q]
    calc
      (∑ i, |ℓ i| / ∑ a, |ℓ a|) = (∑ i, |ℓ i|) / ∑ a, |ℓ a| :=
        (Finset.sum_div _ _ _).symm
      _ = 1 := div_self hL.ne'
  refine PMF.ofFintype (fun i => ENNReal.ofReal (q i)) ?_
  calc
    ∑ i, ENNReal.ofReal (q i) = ENNReal.ofReal (∑ i, q i) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => hq_nonneg i)).symm
    _ = 1 := by rw [hq_sum, ENNReal.ofReal_one]

@[simp] theorem selectedLoss_optimalPropensity_apply {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) (b : V) :
    (selectedLoss_optimalPropensity ℓ hL b).toReal =
      |ℓ b| / ∑ i, |ℓ i| := by
  change (ENNReal.ofReal (|ℓ b| / ∑ i, |ℓ i|)).toReal =
    |ℓ b| / ∑ i, |ℓ i|
  exact ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (ℓ b)) hL.le)

/-- Exact objective under target-wise support. The formula identifies
sum-of-coordinate-error MSE with the trace of marginal variances;
there is no covariance-independence or scalar-total-variance claim. -/
theorem selectedLossMSE_eq_sum {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ)
    (h_support : ∀ b, p b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE p ℓ =
      (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
  unfold selectedLossMSE
  calc
    ∑ b, pmfMean p (fun a =>
        ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)
        = ∑ b, (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
      apply Finset.sum_congr rfl
      intro b _
      have hmean := pmfMean_selectedLoss_support p ℓ b (h_support b)
      have hvar := pmfMean_selectedLoss_variance p ℓ b (h_support b)
      rw [pmfMean_sq_sub, hmean]
      rw [hmean] at hvar
      linarith
    _ = (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Exact MSE attained by loss-magnitude-proportional propensity.
Zero losses may have zero mass without losing unbiasedness. -/
theorem selectedLoss_optimalPropensity_mse {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      (∑ i, |ℓ i|) ^ 2 - ∑ i, (ℓ i) ^ 2 := by
  have h_support : ∀ b,
      selectedLoss_optimalPropensity ℓ hL b ≠ 0 ∨ ℓ b = 0 := by
    intro b
    by_cases hzero : ℓ b = 0
    · exact Or.inr hzero
    · apply Or.inl
      have hne : (selectedLoss_optimalPropensity ℓ hL b).toReal ≠ 0 := by
        rw [selectedLoss_optimalPropensity_apply]
        exact div_ne_zero (abs_ne_zero.mpr hzero) hL.ne'
      exact (ENNReal.toReal_ne_zero.mp hne).1
  rw [selectedLossMSE_eq_sum _ _ h_support]
  have hsecond : ∑ b,
      (ℓ b) ^ 2 / (selectedLoss_optimalPropensity ℓ hL b).toReal =
        ∑ b, |ℓ b| * ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro b _
    rw [selectedLoss_optimalPropensity_apply]
    by_cases hzero : ℓ b = 0
    · simp [hzero]
    · rw [← sq_abs]
      field_simp [abs_ne_zero.mpr hzero, hL.ne']
  rw [hsecond, ← Finset.sum_mul]
  ring

/-- Global finite MSE optimum among supported PMFs, proved using
zero-safe finite Cauchy-Schwarz, not stationary-point optimality. -/
theorem selectedLoss_optimalPropensity_mse_le {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ ≤
      selectedLossMSE q ℓ := by
  have hCS : (∑ i, |ℓ i|) ^ 2 ≤
      (∑ i, (ℓ i) ^ 2 / (q i).toReal) * ∑ i, (q i).toReal := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact div_nonneg (sq_nonneg (ℓ i)) ENNReal.toReal_nonneg
    · intro i _
      exact ENNReal.toReal_nonneg
    · intro i _
      by_cases hzero : (q i).toReal = 0
      · have hqi : q i = 0 := by
          have hz : q i = 0 ∨ q i = ⊤ :=
            (ENNReal.toReal_eq_zero_iff (q i)).mp hzero
          exact hz.resolve_right (q.apply_ne_top i)
        have hloss : ℓ i = 0 := (h_support i).elim
          (fun hne => (hne hqi).elim) (fun hzero => hzero)
        simp [hzero, hloss]
      · rw [sq_abs]
        exact le_of_eq (div_mul_cancel₀ ((ℓ i) ^ 2) hzero).symm
  have hbound : (∑ i, |ℓ i|) ^ 2 ≤
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    simpa only [pmf_weight_sum q, mul_one] using hCS
  rw [selectedLoss_optimalPropensity_mse,
    selectedLossMSE_eq_sum q ℓ h_support]
  linarith


open scoped Classical

/-- Selected-coordinate MSE is a sum of expectations of nonnegative
squared errors, so it is nonnegative for every finite PMF and loss. -/
theorem selectedLossMSE_nonneg {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : 0 ≤ selectedLossMSE p ℓ := by
  unfold selectedLossMSE
  apply Finset.sum_nonneg
  intro b _
  apply pmfMean_nonneg
  intro a _
  exact sq_nonneg _

/-- Zero total absolute loss means every fixed loss is zero. There is
no normalization need and no nonzero selected coordinate can occur. -/
theorem selectedLossMSE_eq_zero_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ = 0 := by
  have hzero (b : V) : ℓ b = 0 := by
    have habs : |ℓ b| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => abs_nonneg (ℓ i))).mp hL b (Finset.mem_univ b)
    exact abs_eq_zero.mp habs
  simp [selectedLossMSE, hzero]

/-- In the zero-normalizer branch, every supplied PMF has zero MSE and
is therefore a minimizer. This explicitly avoids a uniqueness claim. -/
theorem selectedLossMSE_le_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p q : PMF V) (ℓ : V → ℝ)
    (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ ≤ selectedLossMSE q ℓ := by
  rw [selectedLossMSE_eq_zero_of_abs_sum_eq_zero p ℓ hL]
  exact selectedLossMSE_nonneg q ℓ

/-- With positive total loss magnitude, the loss-proportional PMF is the
unique supported least-MSE proposal. The proof recovers the constant
nonzero-weight ratios using strict Jensen, with zero-weight losses
handled by the given support rather than an all-positive-assumption. -/
theorem selectedLoss_optimalPropensity_eq_of_mse_eq {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0)
    (h_mse : selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      selectedLossMSE q ℓ) :
    selectedLoss_optimalPropensity ℓ hL = q := by
  have hmul (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) = |ℓ i| := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) =
            |ℓ i| / (q i).toReal * (q i).toReal := mul_comm _ _
        _ = |ℓ i| := div_mul_cancel₀ _ hzero
  have hsq (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
        (ℓ i) ^ 2 / (q i).toReal := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
            ((q i).toReal * (|ℓ i| / (q i).toReal)) *
              (|ℓ i| / (q i).toReal) := by ring
        _ = |ℓ i| * (|ℓ i| / (q i).toReal) := by rw [hmul i]
        _ = |ℓ i| ^ 2 / (q i).toReal := by ring
        _ = (ℓ i) ^ 2 / (q i).toReal := by rw [sq_abs]
  have hmean : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) =
      ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact hmul i
  have hsecond : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsq i
  rw [selectedLoss_optimalPropensity_mse] at h_mse
  have hobjective := selectedLossMSE_eq_sum q ℓ h_support
  have hvalue : (∑ i, (ℓ i) ^ 2 / (q i).toReal) =
      (∑ i, |ℓ i|) ^ 2 := by
    linarith
  have hjensen := (strictConvexOn_pow (n := 2) (by norm_num)).map_sum_eq_iff'
    (t := Finset.univ)
    (w := fun i => (q i).toReal)
    (p := fun i => |ℓ i| / (q i).toReal)
    (fun i _ => ENNReal.toReal_nonneg)
    (pmf_weight_sum q)
    (fun i _ => div_nonneg (abs_nonneg (ℓ i)) ENNReal.toReal_nonneg)
  have hw_eq : ∀ b, (q b).toReal ≠ 0 →
      |ℓ b| / (q b).toReal = ∑ i, |ℓ i| := by
    have hsquare : (∑ i, (q i).toReal * (|ℓ i| / (q i).toReal)) ^ 2 =
        ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 := by
      rw [hmean, hsecond, hvalue]
    have hj := hjensen.mp hsquare
    intro b hb
    have hb_eq := hj b (Finset.mem_univ b) hb
    simpa only [smul_eq_mul, hmean] using hb_eq
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff'
    ((selectedLoss_optimalPropensity ℓ hL).apply_ne_top b)
    (q.apply_ne_top b)).mp
  rw [selectedLoss_optimalPropensity_apply]
  by_cases hzero : (q b).toReal = 0
  · have hqi : q b = 0 :=
      ((ENNReal.toReal_eq_zero_iff (q b)).mp hzero).resolve_right
        (q.apply_ne_top b)
    have hloss : ℓ b = 0 := (h_support b).elim
      (fun hne => (hne hqi).elim) (fun hz => hz)
    simp [hzero, hloss]
  · apply (div_eq_iff hL.ne').mpr
    calc
      |ℓ b| = (∑ i, |ℓ i|) * (q b).toReal :=
        (div_eq_iff hzero).mp (hw_eq b hzero)
      _ = (q b).toReal * ∑ i, |ℓ i| := mul_comm _ _

end Hagi.Probability

export Hagi.Probability (mwu_potential_step)
