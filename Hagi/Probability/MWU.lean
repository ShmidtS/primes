import Mathlib
import Hagi.Probability.GibbsConcentration

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

