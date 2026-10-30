import Mathlib

/-!
# StreamingLLM — attention sinks (источник №61: Xiao et
# al., "Efficient Streaming Language Models with
# Attention Sinks", arXiv 2309.17453)

Идея: KV-кэш = несколько первых токенов-«якорей» (sink) +
скользящее окно последних позиций (ограничено w). Память
НЕ растёт с длиной обрабатываемой последовательности:
стриминг сколь угодно длинного входа при кэше ≤ n_s + w.
Формализуем: равномерная ограниченность кэша (для ЛЮБОГО
горизонта T), строгая экономия против полного кэша и
линейный рост сэкономленной памяти по длине.
-/

namespace Hagi.Model.StreamingLLM

/-- KV-кэш StreamingLLM на горизонте T: n_s якорей +
окно min(w, T). -/
def streamCache (T n_s w : ℕ) : ℕ := n_s + min w T

/-- Полный KV-кэш длины T. -/
def fullCache (T : ℕ) : ℕ := T

/-- ИСТОЧНИК №61, УРОВЕНЬ 1: кэш РАВНОМЕРНО ОГРАНИЧЕН —
при ЛЮБОМ горизонте T размер кэша не превосходит n_s + w:
память не растёт с длиной входа (стриминг неограниченного
входа при фиксированной памяти). -/
theorem stream_bounded (T n_s w : ℕ) :
    streamCache T n_s w ≤ n_s + w := by
  have hmin := Nat.min_le_right w T
  unfold streamCache
  omega

/-- УРОВЕНЬ 1b: при T > n_s + w StreamingLLM СТРОГО
экономит память против полного кэша. -/
theorem stream_mem_lt (T n_s w : ℕ) (h : n_s + w < T) :
    streamCache T n_s w < fullCache T := by
  have hmin : min w T = w := Nat.min_eq_left (by omega)
  unfold streamCache fullCache
  rw [hmin]
  omega

/-- УРОВЕНЬ 2: ЭКОНОМИЯ РАСТЁТ ЛИНЕЙНО по длине (при
T ≥ n_s + w): каждый новый токен увеличивает
сэкономленную память ровно на 1. -/
theorem stream_saving_step (T n_s w : ℕ)
    (hT : n_s + w ≤ T) :
    fullCache (T + 1) - streamCache (T + 1) n_s w
      = (fullCache T - streamCache T n_s w) + 1 := by
  have hmin1 : min w T = w := Nat.min_eq_left (by omega)
  have hmin2 : min w (T + 1) = w :=
    Nat.min_eq_left (by omega)
  unfold fullCache streamCache
  rw [hmin1, hmin2]
  omega

end Hagi.Model.StreamingLLM
