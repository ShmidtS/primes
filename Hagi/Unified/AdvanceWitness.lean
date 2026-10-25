import Hagi.Unified.MasterHAGI
-- Продуктивный T=2 свидетель итогового инварианта из advance-переходов.
import Hagi.Model.StageSemantics
open Hagi.Model

namespace Hagi.Unified

/-- ПРОДУКТИВНЫЙ СВИДЕТЕЛЬ ИТОГОВОГО ИНВАРИАНТА на T=2
из РЕАЛЬНЫХ advance-переходов (аудит v3, критика 1):
последовательности risk/phi/cap/budget — фактические поля
wTraj-состояний (энергия 30→27→23 убывает, capability
1→2→4 растёт как 2^t, риск 0, бюджет 100−2t), а не свободно
заданные формулы. CertifiedHAGIInvariant выполняется с
α=1: cap 0·(1+1)^2 = 4 ≤ cap 2. -/
theorem certified_invariant_advance_witness :
    Hagi.Unified.CertifiedHAGIInvariant 2
      (fun t => (wTraj.state t).protectedRisk)
      (fun t => (wTraj.state t).energy)
      (fun t => (wTraj.state t).capability)
      (fun t => (wTraj.state t).budget)
      (fun _ => 2)
      (fun _ => 0)
      (fun _ => 0)
      1 0 := by
  constructor
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]

end Hagi.Unified
