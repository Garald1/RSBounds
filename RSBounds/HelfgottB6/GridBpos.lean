import RSBounds.HelfgottB6.Grid

/-! # (B.6) with `31.521`: region B, s = 1, in 8 chunks (one declaration each, to bound the
kernel's memory) -/

namespace RSBounds.HelfgottB6

theorem gBpos_00 : chunkB (1) (-1) (1 / 4) (1 / 28) 0 = true := by decide +kernel

theorem gBpos_01 : chunkB (1) (-1) (1 / 4) (1 / 28) 1 = true := by decide +kernel

theorem gBpos_02 : chunkB (1) (-1) (1 / 4) (1 / 28) 2 = true := by decide +kernel

theorem gBpos_03 : chunkB (1) (-1) (1 / 4) (1 / 28) 3 = true := by decide +kernel

theorem gBpos_04 : chunkB (1) (-1) (1 / 4) (1 / 28) 4 = true := by decide +kernel

theorem gBpos_05 : chunkB (1) (-1) (1 / 4) (1 / 28) 5 = true := by decide +kernel

theorem gBpos_06 : chunkB (1) (-1) (1 / 4) (1 / 28) 6 = true := by decide +kernel

theorem gBpos_07 : chunkB (1) (-1) (1 / 4) (1 / 28) 7 = true := by decide +kernel

end RSBounds.HelfgottB6
