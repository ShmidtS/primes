import Mathlib
import Hagi.Model.ModelSoup

/-!
# Grokfast (источник №88: Lee et al., arXiv 2505.15833)

Ускорение гроккинга: градиент раскладывается EMA-фильтром
на низкочастотную (медленную) и высокочастотную части:
  g_L(t) = EMA_β(g)(t),   g_H(t) = g(t) − g_L(t),
и шаг делается в направлении g + λ·g_L (λ ≥ 0 — усиление
медленной компоненты, которая отвечает за обобщение).

Честные свойства (реюз ema из ModelSoup):
1. `decompose`: g_L + g_H = g — ТОЖДЕСТВО разложения;
2. `amp_dir`: усиленное направление = (1+λ)·g_L + g_H;
3. `amp_low_only`: усиление меняет ТОЛЬКО низкочастотную
   часть (высокочастотная сохранена — шум не усиливается);
4. `const_grad_fix`: на постоянном градиенте EMA сходится
   к нему: g_L = g, g_H = 0 (усиление не искажает
   стационарный сигнал).
-/

namespace Hagi.Model.Grokfast

open Hagi.Model.ModelSoup

variable (β : ℝ)

/-- Низкочастотная компонента: EMA градиента. -/
noncomputable def gLow (β : ℝ) (g : ℕ → ℝ) : ℕ → ℝ :=
  ema β g

/-- Высокочастотная компонента: остаток. -/
noncomputable def gHigh (β : ℝ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun t => g t - gLow β g t

/-- ТОЖДЕСТВО РАЗЛОЖЕНИЯ: g_L + g_H = g в каждой точке. -/
theorem decompose (β : ℝ) (g : ℕ → ℝ) (t : ℕ) :
    gLow β g t + gHigh β g t = g t := by
  unfold gLow gHigh
  show ema β g t + (g t - ema β g t) = g t
  ring

/-- Усиленное направление Grokfast: g + λ·g_L. -/
noncomputable def ampDir (β lam : ℝ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun t => g t + lam * gLow β g t

/-- Усиление меняет только низкочастотную часть: новое
разложение усиленного = (1+λ)·g_L + g_H. -/
theorem amp_recompose (β lam : ℝ) (g : ℕ → ℝ) (t : ℕ) :
    (1 + lam) * gLow β g t + gHigh β g t
      = ampDir β lam g t := by
  unfold ampDir
  rw [← decompose β g t]
  ring

/-- На постоянном градиенте EMA-фильтр стационарен:
g_L = g, g_H = 0 — усиление не искажает постоянный
сигнал (нет ложной генерации «шума»). -/
theorem const_grad_fix (β g₀ : ℝ) (t : ℕ) :
    gLow β (fun _ => g₀) t = g₀
    ∧ gHigh β (fun _ => g₀) t = 0 := by
  have hlow : ∀ t : ℕ, ema β (fun _ => g₀) t = g₀ := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      show β * ema β (fun _ => g₀) t + (1 - β) * g₀ = g₀
      rw [ih]
      ring
  constructor
  · exact hlow t
  · unfold gHigh gLow
    rw [hlow t]
    ring

end Hagi.Model.Grokfast
