import Hagi.Unified.CertifiedLoop

/-!
# Линейная сходимость certified-цикла при PL-условии

Без условия Поляка–Лоясевича certified-цикл гарантирует
лишь остановку в точке «нет сертифицируемого улучшения».
При PL-условии и равномерной нижней грани спуска по
квадрату градиента цепочка шагов даёт ЛИНЕЙНУЮ скорость:
остаточная энергия сжимается геометрически с фактором
(1 − 2κμ).
-/

namespace Hagi.Unified.PLLoop

variable {S : Type*}

/-- ГЛАВНАЯ ТЕОРЕМА: PL-скорость сертифицированной цепочки.
Каждый шаг убивает долю κ квадрата градиента, целевой
функционал удовлетворяет PL-неравенству с параметром μ —
остаток убывает линейно. -/
theorem pl_linear
    (obj : S → ℝ) (Estar κ μ : ℝ)
    (f : ℕ → S) (drops gsqr : ℕ → ℝ) (n : ℕ)
    (hκ : 0 ≤ κ) (hμ : 0 < μ) (hκμ : 2 * κ * μ < 1)
    (hE : ∀ t ≤ n, Estar ≤ obj (f t))
    (hPL : ∀ t ≤ n, 2 * μ * (obj (f t) - Estar) ≤ gsqr t)
    (hdrop : ∀ t < n, κ * gsqr t ≤ drops t)
    (hcert : ∀ t < n,
      obj (f (t + 1)) ≤ obj (f t) - drops t) :
    obj (f n) - Estar
      ≤ (1 - 2 * κ * μ) ^ n * (obj (f 0) - Estar) := by
  have hfactor : (0:ℝ) ≤ 1 - 2 * κ * μ := by
    nlinarith
  revert hE hPL hdrop hcert
  induction n with
  | zero =>
    intro hE hPL hdrop hcert
    rw [pow_zero, one_mul]
  | succ n ih =>
    intro hE hPL hdrop hcert
    have ih' := ih
      (fun t ht => hE t (by omega))
      (fun t ht => hPL t (by omega))
      (fun t ht => hdrop t (by omega))
      (fun t ht => hcert t (by omega))
    have hstep := hcert n (by omega)
    have hPLn := hPL n (by omega)
    have hdropn := hdrop n (by omega)
    have key : obj (f (n + 1)) - Estar
        ≤ (1 - 2 * κ * μ) * (obj (f n) - Estar) := by
      have h2 : κ * (2 * μ * (obj (f n) - Estar))
          ≤ κ * gsqr n :=
        mul_le_mul_of_nonneg_left hPLn hκ
      have h5 : obj (f n) - Estar
          - κ * (2 * μ * (obj (f n) - Estar))
          = (1 - 2 * κ * μ) * (obj (f n) - Estar) := by
        ring
      linarith
    rw [pow_succ]
    nlinarith [ih', key, hfactor]

/-- СЛЕДСТВИЕ ЧЕРЕЗ СЕРТИФИКАТЫ: цепочка StepCert с
drop-гранью по квадрату градиента и PL-условием даёт
линейную скорость certified-цикла. -/
theorem certified_pl_horizon
    (obj : S → ℝ) (M : Hagi.Unified.LinkedQVec.MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (Estar κ μ : ℝ)
    (f : ℕ → S) (b drops gsqr : ℕ → ℝ) (n : ℕ)
    (hκ : 0 ≤ κ) (hμ : 0 < μ) (hκμ : 2 * κ * μ < 1)
    (hE : ∀ t ≤ n, Estar ≤ obj (f t))
    (hPL : ∀ t ≤ n, 2 * μ * (obj (f t) - Estar) ≤ gsqr t)
    (hdrop : ∀ t < n, κ * gsqr t ≤ drops t)
    (certs : ∀ t : Fin n,
      Hagi.Unified.CertifiedLoop.StepCert obj M floor riskLim
        (f t.val) (f (t.val + 1)) (b t.val) (b (t.val + 1)))
    (hdrops : ∀ t : Fin n,
      drops t.val = (certs t).trans.objectiveDrop) :
    obj (f n) - Estar
      ≤ (1 - 2 * κ * μ) ^ n * (obj (f 0) - Estar) :=
  pl_linear obj Estar κ μ f drops gsqr n hκ hμ hκμ hE hPL hdrop
    (fun t ht => by
      have hd := (certs ⟨t, ht⟩).trans.actualDescent
      have heq := hdrops ⟨t, ht⟩
      show obj (f ((⟨t, ht⟩ : Fin n).val + 1))
        ≤ obj (f (⟨t, ht⟩ : Fin n).val)
          - drops (⟨t, ht⟩ : Fin n).val
      linarith [hd, heq])

end Hagi.Unified.PLLoop
