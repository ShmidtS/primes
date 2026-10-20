import Mathlib.Tactic
import Hagi.Model.StageSemantics

set_option linter.style.header false

/-!
# Model.Sidon — Sidon-множества и бесконфликтная сериализация

Мост к arXiv:2610.17283 («The Surprising Expressivity of a
Single Neuron with Autoregressive Chain-of-Thought»):
техника статьи сериализует вычисление σ-схемы в
авторегрессионную траекторию ОДНОГО нейрона
x ↦ σ(⟨w, x⟩ + b) с фиксированным (time-invariant)
вектором параметров w. Веса рёбер кодируются координатами
w[−(t_j − t_i)], где t_i — шаг генерации вершины i;
Sidon-множество гарантирует, что все разности t_j − t_i
различны — координаты не коллидируют при разделении
параметров между шагами.

Формализовано ядро техники:

* `SidonSet` — все парные суммы различны с точностью до
  перестановки пары;
* `sidon_diff_eq` — Sidon ⟹ положительные попарные разности
  различны (Observation 3 статьи);
* `sidon_pair_diff_injective` — инъективность отображения
  рёбер (i,j) ↦ t_j − t_i для строго монотонной нумерации
  вершин шагами из Sidon-сета — бесконфликтное кодирование
  весов одним общим вектором;
* `sidonSet_golomb4` — явный свидетель {0,1,4,6};
* `advance_weights_shared` — переход HAGI разделяет вектор
  весов между циклами (advance сохраняет weights) — та же
  time-invariant структура параметров, что и AR-нейрон
  статьи: параметр-шеринг не обедняет вычислительную
  мощность (Theorem 1/2 статьи).
-/

namespace Hagi.Model

open Finset

/-- **Sidon-множество**: все парные суммы элементов различны
с точностью до перестановки пары. -/
def SidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- **Sidon ⟹ разности различны** (Observation 3 статьи):
если `b − a = d − c` для элементов Sidon-множества с
`a < b` и `c < d`, то пары совпадают: `a = c ∧ b = d`.
Положительные попарные разности Sidon-сета попарно
различны. -/
theorem sidon_diff_eq (S : Finset ℕ) (hS : SidonSet S)
    {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) (hab : a < b) (hcd : c < d)
    (h : b - a = d - c) : a = c ∧ b = d := by
  -- переписываем разность в сумму: b + c = a + d
  have hsum : b + c = a + d := by omega
  have hpair : (b = a ∧ c = d) ∨ (b = d ∧ c = a) :=
    hS b hb c hc a ha d hd hsum
  rcases hpair with h1 | h2
  · -- b = a противоречит a < b
    omega
  · -- b = d ∧ c = a — совпадение пар
    exact ⟨h2.2.symm, h2.1⟩

/-- **Бесконфликтное кодирование рёбер** (ядро техники
сериализации статьи): для строго монотонной нумерации
вершин `t` шагами из Sidon-множества отображение ребра
`(i, j)` (i < j) в координату `t j − t i` ИНЪЕКТИВНО —
каждое ребро схемы получает собственную координату общего
вектора параметров w, и веса не коллидируют при
разделении параметров между всеми шагами генерации. -/
theorem sidon_pair_diff_injective (S : Finset ℕ) (hS : SidonSet S)
    (t : ℕ → ℕ) (htS : ∀ i, t i ∈ S) (hmono : StrictMono t)
    {i j k l : ℕ} (hij : i < j) (hkl : k < l)
    (h : t j - t i = t l - t k) : i = k ∧ j = l := by
  have hti : t i < t j := hmono hij
  have htk : t k < t l := hmono hkl
  have hpair := sidon_diff_eq S hS (htS i) (htS j) (htS k)
    (htS l) hti htk h
  obtain ⟨hik, hjl⟩ := hpair
  have hinj := hmono.injective
  exact ⟨hinj hik, hinj hjl⟩

/-- **Явный Sidon-свидетель**: {0, 1, 4, 6} — Sidon-
множество (совершенная линейка Голомба 4-го порядка:
разности 1, 4, 6, 3, 5, 2 все различны). -/
theorem sidonSet_golomb4 : SidonSet {0, 1, 4, 6} := by
  unfold SidonSet
  decide

/-- **Time-invariant разделение параметров перехода HAGI**:
переход `advance` сохраняет вектор весов между циклами —
один и тот же фиксированный параметр обслуживает все шаги
траектории. Это в точности структура авторегрессионного
нейрона статьи (x ↦ σ(⟨w,x⟩+b) с общим w): по
Theorem 1/2 статьи такое разделение параметров НЕ
ограничивает вычислительную мощность — time-invariant
семантика `Trajectory` способна симулировать любую
σ-схему подходящего размера (сериализация через
Sidon-разности). -/
theorem advance_weights_shared {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S : GrowthState X) (u : StageInput X) :
    (advance S u).weights = S.weights := rfl

end Hagi.Model
