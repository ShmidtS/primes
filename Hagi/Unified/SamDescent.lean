import Hagi.Unified.DescentCore
import Hagi.Optimization.SAM

/-!
# Мост SAM → DescentCore

Спуск по worst-neighbor цели `samW` переносится на
истинный лосс с потерей на остроту: если локальная
острота (samW − L) в текущей точке ≤ sharp, а шаг
гарантированно убывает samW на delta, то истинный лосс
убывает минимум на delta − sharp. Плоские минимумы
(малая острота) делают спуск по SAM-цели честным спуском
по истинной цели.
-/

namespace Hagi.Unified.SamDescent

open Hagi.Unified.DescentCore Hagi.Optimization.SAM

variable {k : Type*} [Fintype k]

/-- ГЛАВНЫЙ МОСТ: спуск по SAM-цели + оценка остроты
⟹ спуск по истинной цели. -/
theorem sam_descent_bridge (J : Objective k) (rho : ℝ)
    (hr : 0 ≤ rho) (x x' : k → ℝ) (delta sharp : ℝ)
    (hbdd : BddAbove (J.f '' (fun e => x + e) '' ball rho))
    (hbdd' : BddAbove (J.f '' (fun e => x' + e) '' ball rho))
    (hsharp : samW J.f rho x - J.f x ≤ sharp)
    (hsam : samW J.f rho x' ≤ samW J.f rho x - delta) :
    J.f x' ≤ J.f x - (delta - sharp) := by
  have hge0 : J.f x ≤ samW J.f rho x := sam_ge J.f rho hr x hbdd
  have hge' : J.f x' ≤ samW J.f rho x' := sam_ge J.f rho hr x' hbdd'
  have hkey : J.f x' ≤ samW J.f rho x - delta := by
    linarith [hge', hsam]
  have hlx : samW J.f rho x ≤ J.f x + sharp := by
    linarith [hsharp]
  linarith

/-- СЛЕДСТВИЕ: сертифицированный спуск по SAM-цели при
нулевой остроте (плоский лосс на шаре) — чистый спуск по
истинной цели. -/
theorem sam_descent_flat (J : Objective k) (rho : ℝ)
    (hr : 0 ≤ rho) (x x' : k → ℝ) (delta : ℝ)
    (hbdd : BddAbove (J.f '' (fun e => x + e) '' ball rho))
    (hbdd' : BddAbove (J.f '' (fun e => x' + e) '' ball rho))
    (hflat : samW J.f rho x = J.f x)
    (hsam : samW J.f rho x' ≤ samW J.f rho x - delta) :
    J.f x' ≤ J.f x - delta := by
  have := sam_descent_bridge J rho hr x x' delta 0 hbdd hbdd' (by linarith) hsam
  simpa using this

end Hagi.Unified.SamDescent
