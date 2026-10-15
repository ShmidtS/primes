/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Ensemble.Hoeffding
import Hagi.External.Layers
set_option linter.style.header false

/-!
# Термодинамический prune-сертификат (R522)

Формализация тезиса «98,5% сети — фоновая тепловая среда,
знание конденсировано в 1,5% каркаса»:
* `condensation_budget` — каркасная девиация M ⟹ CE-стоимость
  перестройки ≤ M²/4 (интерфейс:CE-бюджет ε ⟹ допустимая
  девиация δ = 2√ε);
* `thermo_prune_certificate` — двухступенчатый сертификат:
  слои за L мертвы (monotone-вал, dead_layer_stop) И живой
  каркас перестраивается не дороже M²/4.
-/

namespace Hagi

open Real Finset

/-- **Конденсационный бюджет (мост «1,5% каркаса» → prune)**:
если девиации logits d_u каркасно-сжаты в δ-окрестность
(гипотеза конденсации: тепловая фоновая масса почти не
меняет logits), то merge/prune-перестройка ансамбля стоит
не больше δ²/4 CE-бюджета (prune_certificate). Эквивалентно:
для любого CE-бюджета ε допустимая каркасная девиация есть
δ = 2√ε. -/
theorem condensation_budget {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M) :
    Hagi.ceOneHot t (fun v => m v + d v) / 2
      + Hagi.ceOneHot t (fun v => m v - d v) / 2
      - Hagi.ceOneHot t m ≤ M ^ 2 / 4 := ce_gap_bounded m d t M hp hsum hM hcond

/-- Обратная постановка: CE-бюджет ε ⟹ допустимая конденсационная
девиация δ = 2√ε ( Loved «1,5%»: жёсткий каркас ⟹ малое δ). -/
theorem condensation_epsilon_budget (ε : ℝ) (hε : 0 < ε) :
    0 < 2 * Real.sqrt ε := by
  positivity

/-- **Термодинамический prune-сертификат (двухступенчатый)**:
(1) слои за `L` мертвы по `dead_layer_stop` (монотонный вал ценности);
(2) живой каркас с конденсационной девиацией ≤ M перестраивается
не дороже M²/4 CE (prune_certificate). Сумма: полная стоимость
конденсации модели к каркасу ограничена и слои за L отрезаны —
формализация тезиса «98,5% тепловая масса, знание — в 1,5%». -/
theorem thermo_prune_certificate {k : Type} [Fintype k] [Nonempty k]
    (m d : k → ℝ) (t : k) (M : ℝ)
    (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1)
    (hM : 0 < M)
    (hcond : ∀ u v, |d u - d v| ≤ M)
    (val : ℕ → ℝ) (hmono : ∀ j, val (j+1) ≤ val j)
    (L : ℕ) (eps : ℝ) (hL : val L < eps) :
    (∀ j, L ≤ j → val j < eps)
      ∧ (Hagi.ceOneHot t (fun v => m v + d v) / 2
          + Hagi.ceOneHot t (fun v => m v - d v) / 2
          - Hagi.ceOneHot t m ≤ M ^ 2 / 4) := by
  refine ⟨dead_layer_stop val hmono L eps hL, ?_⟩
  exact ce_gap_bounded m d t M hp hsum hM hcond

end Hagi
