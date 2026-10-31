import Mathlib

/-!
# SignSGD (источник №79: 1-bit compressed SGD,
# Bernstein et al. "signSGD with majority vote",
# arXiv 1802.04434)

Компрессия градиента до знаков: g → sign(g) — 1 бит на
координату (минимальный объём коммуникации).

Формализуем честные свойства:
1. `sign_inner_nonneg`: ⟨sign(g), g⟩ = Σ|g_i| ≥ 0 —
   знаковая проекция НЕ переворачивает направление спуска
   (острый угол с истинным градиентом всегда);
2. `sign_inner_pos`: при g ≠ 0 — строго положительный
   косинус (спуск гарантированно «вправо»);
3. `sign_idempotent`: sign(sign g) = sign g — повторная
   компрессия бесплатна;
4. `sign_bits`: каждая координата после компрессии
   трёхзначна {−1,0,1} — тернарное ядро HAGI совместимо:
   знаковый градиент — уже тернарный вектор.
-/

namespace Hagi.Step.SignSGD

open Classical

variable {k : Type*} [Fintype k]

/-- Знак координаты (тернарный: −1/0/1). -/
noncomputable def sgn1 (x : ℝ) : ℝ := if x < 0 then -1 else if x = 0 then 0 else 1

/-- ЗНАКОВАЯ ПРОЕКЦИЯ СОХРАНЯЕТ НАПРАВЛЕНИЕ СПУСКА:
⟨sign(g), g⟩ = ‖g‖₁ ≥ 0 — скалярное произведение с
истинным градиентом неотрицательно (компрессия до 1 бита
не переворачивает шаг). -/
theorem sign_inner_nonneg (g : k → ℝ) :
    ∑ i, sgn1 (g i) * g i = ∑ i, |g i| ∧ 0 ≤ ∑ i, |g i| := by
  constructor
  · refine Finset.sum_congr rfl ?_
    intro i _
    unfold sgn1
    rcases lt_trichotomy (g i) 0 with h | h | h
    · rw [if_pos h, abs_of_neg h]
      ring
    · rw [if_neg (by linarith), if_pos h, h]
      norm_num
    · rw [if_neg (by linarith), if_neg (by linarith : ¬ g i = 0),
        abs_of_pos h]
      ring
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg (g i))

/-- СТРОГО ПОЛОЖИТЕЛЬНЫЙ КОСИНУС ПРИ НЕПУСТОМ ГРАДИЕНТЕ:
g ≠ 0 ⟹ ⟨sign(g), g⟩ > 0 — спуск строго «по градиенту». -/
theorem sign_inner_pos (g : k → ℝ) [Nonempty k]
    (hg : ∃ i, g i ≠ 0) :
    0 < ∑ i, sgn1 (g i) * g i := by
  obtain ⟨i₀, h₀⟩ := hg
  obtain ⟨heq, hnn⟩ := sign_inner_nonneg g
  have hpos : (0:ℝ) < |g i₀| := abs_pos.mpr h₀
  have hle : |g i₀| ≤ ∑ i, |g i| :=
    Finset.single_le_sum (f := fun i => |g i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i₀)
  rw [heq]
  linarith

/-- sgn1 — идентичность на тернарном множестве {−1,0,1}. -/
theorem sgn1_fix (y : ℝ) (h : y = -1 ∨ y = 0 ∨ y = 1) :
    sgn1 y = y := by
  rcases h with h | h | h
  · subst h; unfold sgn1; norm_num
  · subst h; unfold sgn1; norm_num
  · subst h; unfold sgn1; norm_num

/-- ТЕРНАРНОСТЬ: после компрессии каждая координата ∈
{−1, 0, 1} — совместимость с тритарным ядром HAGI. -/
theorem sgn1_ternary (x : ℝ) :
    sgn1 x = -1 ∨ sgn1 x = 0 ∨ sgn1 x = 1 := by
  unfold sgn1
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inl (if_pos h)
  · exact Or.inr (Or.inl (by
      rw [if_neg (by linarith), if_pos h]))
  · exact Or.inr (Or.inr (by
      rw [if_neg (by linarith), if_neg (by linarith : ¬ x = 0)]))

/-- ИДЕМПОТЕНТНОСТЬ: повторная знаковая компрессия ничего
не меняет (sign ∘ sign = sign; следует из тернарности и
идентичности на {−1,0,1}). -/
theorem sign_idempotent (x : ℝ) : sgn1 (sgn1 x) = sgn1 x :=
  sgn1_fix _ (sgn1_ternary x)

end Hagi.Step.SignSGD
