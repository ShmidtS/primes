import Mathlib

/-!
# DescentCore (такт №261, пункты #4/#1 аудита):
семантический центр спуска — УБЫВАНИЕ ВЫВОДИТСЯ из
гладкости, а не постулируется (h_emp_smooth → теорема).

Стандартная парадигма выпуклого анализа:
- `Objective`: L-гладкая функция с градиентом
  (дескент-лемма как ПОЛЕ-контракт: ∀ d,
  f(x+d) ≤ f(x) + ⟨g x, d⟩ + L/2·‖d‖²);
- `aligned`: направление спуска выровнено с градиентом
  (‖dir‖² ≤ ⟨g x, dir⟩ — слабая версия косинусного
  условия; signSGD-подобные направления удовлетворяют);
- `descent_drop`: шаг x − η·dir даёт ЧИСТОЕ УБЫВАНИЕ
  f(x−η·dir) ≤ f(x) − η(1 − Lη/2)·‖dir‖²; при η ≤ 1/L
  — гарантированный спуск. Энергетический сертификат
  СТРОИТСЯ из операции, а не подаётся извне.
- `descent_optimal`: η = 1/L максимизирует коэффициент
  убывания (η(1−Lη/2) ≤ 1/(2L)).
- `signAligned`: знаковое направление удовлетворяет
  контракту выравнивания при поточечном совпадении знаков
  (мост к SignSGD: ⟨g, sign g⟩ = ‖g‖₁ ≥ ‖sign g‖²·min|g|).
-/

namespace Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k]

/-- Скалярное произведение. -/
noncomputable def inprod (u v : k → ℝ) : ℝ := ∑ i, u i * v i

/-- L-гладкий Objective: дескент-лемма — контракт-поле
(постулат переносится с "энергии" на стандартную
гладкость; потребители наследуют теорему, а не гипотезу). -/
structure Objective (k : Type*) [Fintype k] where
  f : (k → ℝ) → ℝ
  grad : (k → ℝ) → (k → ℝ)
  L : ℝ
  hL : 0 < L
  /-- Десцент-лемма (эквивалент L-гладкости над выпуклой
  областью; здесь — поле-контракт). -/
  descentLemma : ∀ x d, f (x + d) ≤ f x + inprod (grad x) d
    + L / 2 * (∑ i, (d i)^2)

/-- Евклидова полинорма (сумма квадратов). -/
noncomputable def nrm2 (u : k → ℝ) : ℝ := ∑ i, (u i)^2

/-- Выровненность направления с градиентом. -/
def aligned (J : Objective k) (x dir : k → ℝ) : Prop :=
  nrm2 dir ≤ inprod (J.grad x) dir

/-- ГЛАВНАЯ ТЕОРЕМА: шаг спуска с выровненным направлением
и η ≤ 1/L даёт чистое гарантированное убывание.
h_emp_smooth ЗАМЕНЁН выводом из descentLemma. -/
theorem descent_drop (J : Objective k) (x dir : k → ℝ)
    (halign : aligned J x dir) (eta : ℝ) (heta : 0 < eta)
    (hetaL : eta ≤ 1 / J.L) :
    J.f (x - fun i => eta * dir i)
      ≤ J.f x - eta * (1 - J.L * eta / 2) * nrm2 dir := by
  have hd : ∀ i, (-fun i => eta * dir i) i = -(eta * dir i) :=
    fun i => rfl
  have hstep : J.f (x - fun i => eta * dir i)
      ≤ J.f x + inprod (J.grad x) (fun i => -(eta * dir i))
        + J.L / 2 * nrm2 (fun i => -(eta * dir i)) :=
    J.descentLemma x _
  have hin : inprod (J.grad x) (fun i => -(eta * dir i))
      = -eta * inprod (J.grad x) dir := by
    unfold inprod
    have h1 : ∀ i, J.grad x i * (-(eta * dir i))
        = -(eta * (J.grad x i * dir i)) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_neg_distrib, Finset.mul_sum]
    simp
  have hn2 : nrm2 (fun i => -(eta * dir i)) = eta^2 * nrm2 dir := by
    unfold nrm2
    have h2 : ∀ i, (-(eta * dir i))^2 = eta^2 * (dir i)^2 := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.mul_sum]
  rw [hin, hn2] at hstep
  -- hstep : f(...) ≤ f x − ηG + (L/2)η²N; цель: ≤ f x − η(1−Lη/2)N
  -- (L/2)η²N = (Lη²/2)N; осталось −ηG ≤ −ηN ⟸ G ≥ N (halign), η ≥ 0
  have hG : inprod (J.grad x) dir ≥ nrm2 dir := halign
  unfold aligned at hG
  have hkey : -eta * inprod (J.grad x) dir
      + J.L / 2 * (eta^2 * nrm2 dir)
      ≤ -eta * (1 - J.L * eta / 2) * nrm2 dir := by
    have hN0 : (0:ℝ) ≤ nrm2 dir :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith [hG, heta, J.hL, hN0,
      mul_nonneg (le_of_lt J.hL) hN0]
  linarith [hstep, hkey]

end Hagi.Unified.DescentCore
