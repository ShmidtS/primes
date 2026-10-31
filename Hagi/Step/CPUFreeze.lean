import Mathlib

/-!
# CPUFreeze (приоритет 5 «HAGI Neural Computer», такт №248):
SafeQP-ограничение C1 — параметры встроенного процессора
АБСОЛЮТНО инвариантны к градиентам.

Обновление состоит из двух блоков: (ΔCPU, Δrest).
Контроллер отбрасывает CPU-часть:
  safeStep = (0, Δrest).

Доказуемые свойства:
1. `cpu_frozen`: ΔCPU' = 0 — веса процессора неизменны
   (равенство по построению, а не гипотеза);
2. `norm_le`: ‖safeStep‖ ≤ ‖proposal‖ — заморозка не
   увеличивает норму шага (trust region C3 наследуется);
3. `anchor_drift`: якорный дрейф безопасного шага не
   превосходит дрейфа rest-части (контроль C2 по
   остальным координатам сохраняется).
-/

namespace Hagi.Step.CPUFreeze

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Безопасный шаг: CPU-блок обнулён, остальное сохранено. -/
def safeStep (dCPU : ℝ) (drest : k → ℝ) : ℝ × (k → ℝ) :=
  (0, drest)

/-- C1: процессор заморожен — CPU-компонента шага нулевая
В ТОЧНОСТИ (rfl-контракт). -/
theorem cpu_frozen (dCPU : ℝ) (drest : k → ℝ) :
    (safeStep dCPU drest).1 = 0 := rfl

/-- C3-наследование: сумма квадратов безопасного шага не
превосходит предложения (отбрасывание блока сжимает). -/
theorem norm_le (dCPU : ℝ) (drest : k → ℝ) :
    (safeStep dCPU drest).1 ^ 2
      + ∑ i, (safeStep dCPU drest).2 i ^ 2
    ≤ dCPU ^ 2 + ∑ i, drest i ^ 2 := by
  have hnn : (0:ℝ) ≤ ∑ i : k, drest i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (drest i))
  have h : (0:ℝ) ≤ dCPU ^ 2 := sq_nonneg dCPU
  simp only [safeStep]
  linarith

/-- C2-канал: якорный дрейг безопасного шага — только
rest-часть (CPU-координаты не дрейфуют вовсе). -/
theorem anchor_drift (dCPU : ℝ) (drest : k → ℝ)
    (gCPU : ℝ) (grest : k → ℝ) :
    gCPU * (safeStep dCPU drest).1
      + ∑ i, grest i * (safeStep dCPU drest).2 i
    = ∑ i, grest i * drest i := by
  simp [safeStep]

end Hagi.Step.CPUFreeze
