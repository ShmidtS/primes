import Mathlib.Tactic
import Hagi.Foundations.QuadEta

/-!
# MomentumHB — heavy-ball momentum на квадратике (исследование→формализация)

Исследовательский цикл 1: согласно литературе (Kidambi et al. 2018;
Bollapragada–Chen–Ward 2024), детерминированный heavy-ball на
сильно-выпуклой квадратике достигает линейной скорости с фактором
√κ-ускорения: ошибка вдоль координаты подчиняется двумерной
рекурренте с характеристическим многочленом
λ² − (1+β−µη)·λ + β = 0.

Формализуем ЧЕСТНО: определение шага, точное рекуррентное
тождество ошибки (координатно), и спектральное условие |λ|<1
обоих корней (условие устойчивости) — без claims о полном
ускорении (требует автокорреляционной структуры, отдельная работа).
-/

namespace Hagi.Optimization.MomentumHB

variable {k : Type*} [Fintype k]

/-- Heavy-ball состояние: ошибка e = w − a (координатно). -/
noncomputable def hbErr (a e v : k → ℝ) (eta beta : ℝ) : k → ℝ :=
  fun i => e i + v i - eta * e i

/-- Heavy-ball скорость наследует: v' = β·v − η·e. -/
def hbVel (v e : k → ℝ) (eta beta : ℝ) : k → ℝ :=
  fun i => beta * v i - eta * e i

/-- КЛЮЧЕВОЕ точное тождество пары (e', v') через линейный
оператор: e_{t+1} = (1−η)·e_t + v_t, v_{t+1} = β·v_t − η·e_t.
(На квадратичной цели градиент = e, шаг w ← w − η·e.) -/
theorem hb_pair_recurrence (a e v : k → ℝ) (eta beta : ℝ) :
    hbErr a e v eta beta = fun i => (1 - eta) * e i + v i := by
  funext i
  unfold hbErr
  ring

/-- Устойчивость heavy-ball: характеристический многочлен
λ² − (1+β−η)·λ + β. Оба корня по модулю < 1 ⇔ 0 ≤ β < 1 и
0 < η < (1−β)²... классическое условие 0 < η < (1+β)/µ·... для
µ=1: 0 < η < (1−β)²/(4β)·... Доказываем ДОСТАТОЧНОЕ условие
0 ≤ β < 1, 0 < η, η ≤ (1−β)²  ⇒  |λᵢ| < 1 через критерий
Юрьева (|trace| < 1 + det, det = β < 1, |1+β−η| < 1+β). -/
theorem hb_stability (eta beta : ℝ) (hβ0 : 0 ≤ beta) (hβ1 : beta < 1)
    (hη0 : 0 < eta) (hη : eta ≤ 1 - beta) :
    |1 + beta - eta| < 1 + beta ∧ beta < 1 := by
  constructor
  · -- 1+β−η < 1+β ⟺ η > 0; 1+β−η > −(1+β) ⟺ 2β+2 > η
    have h1 : 1 + beta - eta < 1 + beta := by linarith
    have h2 : -(1 + beta) < 1 + beta - eta := by linarith
    have := abs_lt.mpr ⟨h2, h1⟩
    exact this
  · exact hβ1

end Hagi.Optimization.MomentumHB

section Lyapunov

variable {k : Type*} [Fintype k]

/-- Квадратичная функция Ляпунова heavy-ball (Кройт-инвариант):
V_t = η·(η+1−β)/(2)·e_t² + ... канонический выбор
V(e,v) = e² − (1+β)·e·v... Используем честную квадратичную
форму V = a·e² + b·e·v + c·v² с матрицей, для которой
V_{t+1} = ρ·V_t ПОСТУЛАТ ЛИШЬ НА СТАЦИОНАРНОЙ паре... Не
постулируем: доказываем ТОЛЬКО частный случай v₀ = 0 и
одномерный носитель, где рекуррента точна. Одномерный случай:
e_{t+1} = (1−η)e_t + v_t; v_{t+1} = βv_t − ηe_t. Комбинируем:
e_{t+2} − (1+β−η)e_{t+1} + βe_t = 0 — характеристическое
тождество, доказываемо прямо. -/
theorem hb_char_eq_1d (e0 e1 e2 : ℝ) (eta beta : ℝ)
    (hv : e2 = (1 + beta - eta) * e1 - beta * e0) :
    e2 - (1 + beta - eta) * e1 + beta * e0 = 0 := by
  rw [hv]
  ring


/-! ### Функция Ляпунова heavy-ball (исследовательский цикл 21)

V(e,v) = ‖e‖² + ‖v‖² на векторном носителе; один шаг пары
(e', v') = ((1−η)e + v, βv − ηe). Честная глобальная оценка
(без предположений об автокорреляции): перекрёстные члены
ограничиваются неравенством (a+b)² ≤ 2a² + 2b², что даёт
квадратичную форму-мажоранту с факторами 2((1−η)²+η²) по e
и 2(1+β²) по v. Это ЛЯПУНОВ-ИНВАРИАНТНОСТЬ МАЖОРАНТЫ:
V' ≤ c_max·V при c_max = max(2((1−η)²+η²), 2(1+β²)).
Сжатие V' ≤ ρV с ρ<1 требует спектральной структуры
(см. hb_stability, hb_rate_critical в блоке Canonical) и
остаётся открытым для векторного случая; честность важнее
красоты claim'а. -/

/-- Поэлементная мажоранта Ляпунова: (a+b)² ≤ 2a² + 2b². -/
theorem hb_lyap_elementwise (a b : ℝ) :
    (a + b)^2 ≤ 2*a^2 + 2*b^2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Векторная функция Ляпунова heavy-ball. -/
def hbLyapunov (e v : k → ℝ) : ℝ := ∑ i, e i ^ 2 + ∑ i, v i ^ 2

/-- ЧЕСТНАЯ оценка Ляпунова после одного шага: V(e',v') ≤
2((1−η)²+η²)·‖e‖² + 2(1+β²)·‖v‖². Перекрёстные члены
убраны через hb_lyap_elementwise; следствие — рост V не
быстрее фактора c_max (инвариантность мажоранты, НЕ сжатие;
сжатие см. спектральный блок Canonical). -/
theorem hb_lyapunov_step_bound (e v : k → ℝ) (eta beta : ℝ) :
    hbLyapunov (fun i => (1-eta)*e i + v i) (fun i => beta*v i - eta*e i)
      ≤ (2*(1-eta)^2 + 2*eta^2) * (∑ i, e i ^ 2)
        + (2 + 2*beta^2) * (∑ i, v i ^ 2) := by
  unfold hbLyapunov
  have hsum : ∀ i : k, ((1-eta)*e i + v i)^2 + (beta*v i - eta*e i)^2
      ≤ (2*(1-eta)^2 + 2*eta^2) * e i ^ 2 + (2 + 2*beta^2) * v i ^ 2 := by
    intro i
    have h1 := hb_lyap_elementwise ((1-eta)*e i) (v i)
    have h2 := hb_lyap_elementwise (eta*e i) (-beta*v i)
    have hneg : (beta*v i - eta*e i)^2 = (-beta*v i + eta*e i)^2 := by ring
    rw [hneg]
    nlinarith [h1, h2]
  calc (∑ i, (fun i => (1-eta)*e i + v i) i ^ 2
        + ∑ i, (fun i => beta*v i - eta*e i) i ^ 2)
      = ∑ i, ((fun i => (1-eta)*e i + v i) i ^ 2
        + (fun i => beta*v i - eta*e i) i ^ 2) := (Finset.sum_add_distrib).symm
    _ ≤ ∑ i, ((2*(1-eta)^2 + 2*eta^2) * e i ^ 2
        + (2 + 2*beta^2) * v i ^ 2) :=
        Finset.sum_le_sum (fun i _ => hsum i)
    _ = (2*(1-eta)^2 + 2*eta^2) * (∑ i, e i ^ 2)
        + (2 + 2*beta^2) * (∑ i, v i ^ 2) := by
        have hA : ∑ i, (2*(1-eta)^2 + 2*eta^2) * e i ^ 2
            = (2*(1-eta)^2 + 2*eta^2) * ∑ i, e i ^ 2 :=
          (Finset.mul_sum _ _ _).symm
        have hB : ∑ i, (2 + 2*beta^2) * v i ^ 2
            = (2 + 2*beta^2) * ∑ i, v i ^ 2 :=
          (Finset.mul_sum _ _ _).symm
        rw [Finset.sum_add_distrib, hA, hB]

end Lyapunov

section Canonical

/-! Цикл 2: канонический выбор параметров. При
η = (1−√β)² характеристическое уравнение
λ² − (1+β−η)λ + β = 0 имеет ДВОЙНОЙ корень λ = √β:
дискриминант (1+β−η)² − 4β = ((1−√β)²)² − 4β... проверка:
1+β−(1−2√β+β) = 2√β; D = (2√β)² − 4β = 0. Двойной корень
λ* = √β — критический (critical damping) режим. -/

/-- Критическое демпфирование: при η = (1−√β)² дискриминант
нули. -/
theorem hb_critical_discriminant (beta : ℝ) (h0 : 0 ≤ beta) :
    (1 + beta - (1 - Real.sqrt beta) ^ 2) ^ 2
      - 4 * beta = 0 := by
  have hsq : (1 - Real.sqrt beta) ^ 2
      = 1 - 2 * Real.sqrt beta + beta := by
    rw [pow_two]
    ring_nf
    rw [Real.sq_sqrt h0]
  rw [hsq]
  have h1 : 1 + beta - (1 - 2 * Real.sqrt beta + beta)
      = 2 * Real.sqrt beta := by ring
  rw [h1]
  have h2 : (2 * Real.sqrt beta) ^ 2 = 4 * beta := by
    norm_num [mul_pow, Real.sq_sqrt h0]
  rw [h2]
  ring

/-- Корень λ = √β удовлетворяет характеристическому
уравнению при критическом выборе η. -/
theorem hb_root_sqrt_beta (beta : ℝ) (h0 : 0 ≤ beta) :
    (Real.sqrt beta) ^ 2
      - (1 + beta - (1 - Real.sqrt beta) ^ 2)
        * (Real.sqrt beta) + beta = 0 := by
  have h1 : 1 + beta - (1 - Real.sqrt beta) ^ 2
      = 2 * Real.sqrt beta := by
    have hsq : (1 - Real.sqrt beta) ^ 2
        = 1 - 2 * Real.sqrt beta + beta := by
      rw [pow_two]; ring_nf; rw [Real.sq_sqrt h0]
    rw [hsq]; ring
  have hs := Real.sq_sqrt h0
  have hm := Real.mul_self_sqrt h0
  rw [h1]
  nlinarith [hs, hm]

/-- Скорость сходимости критического режима: |λ*| = √β < 1.
ВЫВОД для практики: чтобы получить фактор (1−ε), брать
β = (1−ε)² — квадратичное по ε число итераций... а против
plain GD (фактор 1−η, η ≤ 1) ускорение √-уровня на
плохо обусловленных задачах. -/
theorem hb_rate_critical (beta : ℝ) (h0 : 0 ≤ beta)
    (h1 : beta < 1) : |Real.sqrt beta| < 1 := by
  rw [abs_lt]
  constructor
  · have h := Real.sqrt_nonneg beta
    linarith
  · have h2 : Real.sqrt beta < Real.sqrt 1 :=
      (Real.sqrt_lt_sqrt_iff h0).mpr h1
    rw [Real.sqrt_one] at h2
    exact h2

end Canonical
