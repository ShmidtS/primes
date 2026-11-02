import Hagi.Optimization.InexactContraction

/-!
# LinkedProjects — мосты к внешним Lean-проектам ML-теории

Обзор соответствий (полная карта — RELATED.md); здесь —
рабочие Statement-мосты, где теория HAGI ПОГЛОЩАЕТ
результат внешнего проекта как частный случай уже
доказанного ядра (без импорта чужих пакетов: их
toolchain-пины 4.27/4.32 несовместимы с нашим 4.35 —
связь theorem-level, не package-level).

## ArtificialTheorems (GasStationManager)

`RL/ValueIterationComplete`: сходимость value iteration для
дисконтированного MDP — Bellman-оператор сжатие с фактором γ.
Мост ниже: точная/приближённая value iteration — ЧАСТНЫЙ
СЛУЧАЙ `inexact_contraction_bound` (x = дистанция до
фиксированной точки, q = γ, ε = погрешность итерации):
‖V_k − V*‖ ≤ γ^k·‖V_0 − V*‖ + ε(1−γ^k)/(1−γ).
Их `ApproxValueIterationInt` — ε-ветка того же ядра;
их `Opt/SGD` (Robbins–Siegmund) соседствует с нашим
`Optimization/RobbinsMonro` и `Unified/RateTheory`
(PL-скорости: quad_gd_pl_rate — точный квадратичный
инстанс без вероятностных предположений).

## FormalSLT (Robby955)

Time-uniform PAC-Bayes / e-processes / empirical Bernstein:
наш слой — `Unified/AnytimeMartingale` (Ville),
`Unified/AnytimePACBayes` (Catoni), `Probability/Freedman`,
`Probability/FreedmanTwoSided`. Заимствование — stitching
и master e-process поверх нескольких стратегий (у нас
master один; их countable master — кандидат в расширение).

## TorchLean (lean-dojo)

Spec→exec→verify (тензоры, FloatLib, CROWN/IBP): наш
аналог исполнительного слоя — `Model/ReferenceMachine` +
`Model/MachineBridge` (energyE/jointStepE/compressQE,
machine_param_bridge, machine_actual_descent_n — n-мерный
end-to-end мост «машина↔состояние»). Их принцип «same
definition trains and proves» — целевой формат для
StageSemantics при переходе к исполняемым эффектам.

## lean4-mlir (brettkoonce)

Verified GPU codegen: backward = Jacobian-transpose по
точным вещественным, нуль проектных аксиом — будущий
нижайзер для эталонной машины HAGI (ReferenceMachine как
спецификация, их StableHLO-путь как исполнение с
доверенным ℝ→Float32 барьером; см. их TRUST.md —
структура доверия совпадает с нашей AssumptionScan-моделью).

## LeanAgent (lean-dojo)

Lifelong proving-агент: процессный инструмент (у HAGI
0 sorry — применять не к чему); идея curriculum-сложности
e^S совместима с нашим Challenge-гейтом.
-/

namespace Hagi.Unified.LinkedProjects

open Hagi.Optimization

/-! ### ArtificialTheorems `RL/ValueIterationComplete` как частный случай -/

/-- МОСТ VALUE ITERATION → INEXACT CONTRACTION: если
оператор T — γ-сжатие к V* с аддитивной погрешностью
исполнения ε на каждом шаге, то k-я итерация находится в
γ^k-шаре вокруг V*: геометрическая сходимость value
iteration (ArtificialTheorems, RL/ValueIterationComplete +
ApproxValueIterationInt) выводится из ЕДИНОГО ядра
`inexact_contraction_bound` HAGI. -/
theorem value_iteration_via_contraction
    (V Vstar : ℕ → ℝ) (gamma eps : ℝ)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1)
    (heps : 0 ≤ eps)
    (hcontract : ∀ k : ℕ,
      V (k + 1) - Vstar (k + 1)
        ≤ gamma * (V k - Vstar k) + eps) :
    ∀ k : ℕ, V k - Vstar k
      ≤ gamma ^ k * (V 0 - Vstar 0)
        + eps * (1 - gamma ^ k) / (1 - gamma) :=
  fun k => inexact_contraction_bound
    (fun k => V k - Vstar k) gamma eps
    hgamma0 hgamma1 heps hcontract k

end Hagi.Unified.LinkedProjects
