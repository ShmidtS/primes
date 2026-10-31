import Mathlib

/-!
# FlashAttention — IO-awareness (источник №63: Dao et
# al., "FlashAttention: Fast and Memory-Efficient Exact
# Attention with IO-Awareness", arXiv 2205.14135)

Идея: точное внимание БЕЗ материализации N×N-матрицы —
tiling с headdim d и SRAM-размером M. HBM-IO падает с
Θ(N·d + N²) стандартного внимания к Θ(N²d²/M) у
FlashAttention. Формализуем честную арифметику IO-выигрыша
при M > d (SRAM вмещает тайл) и монотонность по M: больше
быстрой памяти — меньше IO.
-/

namespace Hagi.Model.FlashAttention

/-- IO стандартного внимания: N·d + N² (материализация). -/
noncomputable def stdIO (N d : ℝ) : ℝ := N * d + N * N

/-- IO FlashAttention: N²·d²/M. -/
noncomputable def flashIO (N d M : ℝ) : ℝ := N * N * (d * d) / M

/-- ИСТОЧНИК №63, УРОВЕНЬ 1 (честная гипотеза): при
M > d² ≥ 1, N ≥ 1: IO FlashAttention СТРОГО меньше IO
стандартного внимания. Оговорка честности: при M лишь
слегка больше d (M ∈ (d, d²)) и больших N tiling НЕ даёт
выигрыша против материализации — выгодность требует
SRAM-размера больше КВАДРАТА headdim (эмпирика источника:
M на порядки больше d²). -/
theorem flash_io_lt (N d M : ℝ) (hd : 1 ≤ d)
    (hM : d * d < M) (hN : 1 ≤ N) :
    flashIO N d M < stdIO N d := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := lt_of_le_of_lt (by
    have : 0 ≤ d * d := mul_nonneg (by linarith) (by linarith)
    linarith) hM
  have hkey : N * N * (d * d) < N * N * M := by
    have hnn : 0 < N * N := by nlinarith
    exact mul_lt_mul_of_pos_left hM hnn
  have h1 : flashIO N d M < N * N := by
    rw [flashIO, div_lt_iff₀ hM0]
    exact hkey
  unfold stdIO
  have hnd : 0 < N * d := by nlinarith
  linarith

/-- УРОВЕНЬ 2: МОНОТОННОСТЬ ПО M — IO FlashAttention НЕ
растёт с размером быстрой памяти (больше SRAM — не хуже). -/
theorem flash_io_antitone (N d M M' : ℝ) (hpos : 0 < N * N * (d * d))
    (hM : 0 < M) (hM' : M ≤ M') :
    flashIO N d M' ≤ flashIO N d M := by
  have hM'0 : 0 < M' := lt_of_lt_of_le hM hM'
  rw [flashIO, flashIO, div_le_div_iff₀ hM'0 hM]
  nlinarith [hpos]

end Hagi.Model.FlashAttention
