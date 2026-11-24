/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.RangeWrap

set_option relaxedAutoImplicit false

/-!
# AdaptiveContext — Occam-выбор окна контекста

Мост к HAGI_v2 `lm.AdaptiveContextSelector` (hagi/lm.py, класс с
тем же именем): модель выбирает размер собственного контекста на
вход. Архитектура держит фиксированное окно k; адаптивность —
число агрегируемых скользящих окон W (mean-logits ансамбль). W
измеряется на хвосте промпта (self-CE кривая по списку кандидатов
w_choices); выбирается НАИМЕНЬШИЙ W, чей измеренный CE лежит в
множителе `(1 + tol)` от лучшего — «no wider ensemble without
measured benefit» (формализация Occam-выбора окна). Полная
история остаётся у вызывающего: unbounded SOURCE, bounded compute.

Модель: выбор = первый элемент отсортированного списка
кандидатов, прошедший порог. Аддитивный
эпсилон исходника опущен честно (strict-margin комментарий в
research); fallback-ветка (нет подходящего W) моделируется none.

- `selectW_spec` — выбранный W принадлежит списку кандидатов и его
  измеренный CE в пределах `(1 + tol)` от лучшего (elbow-приём);
- `selectW_occam_minimal` — на отсортированном списке никакой
  меньший кандидат порог не проходит (минимальное окно);
- `selectW_budget_bound` — выбранный W ограничен максимумом списка
  (bounded compute: не более maxW окон по k байт независимо от
  длины источника).
-/

namespace Hagi.Theory.AdaptiveContext

variable (tol : ℚ) (ce : ℕ → ℚ) (best : ℚ)

/-- Occam-селектор окна: первый кандидат w из списка, чей
измеренный CE не хуже best * (1 + tol); ни один не проходит —
none (соответствует fallback «no W fits» в исходнике). Чистая
функция измеренной кривой — выбор детерминирован. -/
def selectW : List ℕ → Option ℕ
  | [] => none
  | w :: rest =>
      if ce w ≤ best * (1 + tol) then some w else selectW rest

/-- **Elbow-спецификация**: если селектор вернул окно w, то w —
кандидат из списка и его измеренный CE в пределах множителя
(1 + tol) от лучшего (принятие по self-CE elbow). -/
theorem selectW_spec (w : ℕ) : ∀ ws, selectW tol ce best ws = some w →
    w ∈ ws ∧ ce w ≤ best * (1 + tol) := by
  intro ws
  induction ws with
  | nil => intro h; simp [selectW] at h
  | cons a rest ih =>
    intro h
    by_cases hac : ce a ≤ best * (1 + tol)
    · have hsel' : selectW tol ce best (a :: rest) = some a := by
        simp [selectW, hac]
      rw [hsel'] at h
      injection h with heq
      rw [← heq]
      exact ⟨List.mem_cons_self, hac⟩
    · simp [selectW, hac] at h
      obtain ⟨hm, hle⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hle⟩

/-- **Occam-минимальность окна**: на списке кандидатов,
отсортированном по возрастанию, селектор возвращает окно w, для
которого НИ один меньший кандидат порога elbow не проходит —
меньшее окно принимается только при измеренной пользе. -/
theorem selectW_occam_minimal (w : ℕ) : ∀ ws, List.Pairwise (· < ·) ws →
    selectW tol ce best ws = some w →
    ∀ w' ∈ ws, w' < w → best * (1 + tol) < ce w' := by
  intro ws
  induction ws with
  | nil => intro _ h; simp [selectW] at h
  | cons a rest ih =>
    intro hsorted hsel w' hw' hw'lt
    rw [List.pairwise_cons] at hsorted
    obtain ⟨hhead, hrest⟩ := hsorted
    by_cases hac : ce a ≤ best * (1 + tol)
    · have hsel' : selectW tol ce best (a :: rest) = some a := by
        simp [selectW, hac]
      rw [hsel'] at hsel
      injection hsel with heq
      rw [← heq] at hw'lt
      rcases List.mem_cons.1 hw' with rfl | hmem
      · exact absurd hw'lt (by omega)
      · exact absurd hw'lt (by have := hhead w' hmem; omega)
    · simp [selectW, hac] at hsel
      rcases List.mem_cons.1 hw' with rfl | hmem
      · exact not_le.1 hac
      · exact ih hrest hsel w' hmem hw'lt

/-- **Бюджет вычислений**: выбранное окно не превосходит максимума
списка кандидатов — инференс агрегирует не более maxW окон по k
байт независимо от длины источника (unbounded source, bounded
compute). -/
theorem selectW_budget_bound (w : ℕ) : ∀ ws, selectW tol ce best ws = some w →
    w ≤ ws.foldr max 0 := by
  intro ws hsel
  have hmem : w ∈ ws := (selectW_spec tol ce best w ws hsel).1
  have lem : ∀ (l : List ℕ), w ∈ l → w ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a rest ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)
  exact lem ws hmem

end Hagi.Theory.AdaptiveContext
