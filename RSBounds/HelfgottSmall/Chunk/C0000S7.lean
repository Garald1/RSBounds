import RSBounds.HelfgottSmall.Split

/-! Part 7 of walk chunk 0 (positions 14002 to 16001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_7 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (14002, 14011180446853937657, 98178884200208063625202, 1162, 13933, 9542015406953819, 14002, 57, 14641, 4)
      (16002, 16044368999939091203, 128738204341268739264446, 1189, 15928, 9675833846584273, 16007, 59, 16129, 2) = true := by
  decide +kernel
