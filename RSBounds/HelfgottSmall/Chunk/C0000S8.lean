import RSBounds.HelfgottSmall.Split

/-! Part 8 of walk chunk 0 (positions 16002 to 18001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_8 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (16002, 16044368999939091203, 128738204341268739264446, 1189, 15928, 9675833846584273, 16007, 59, 16129, 2)
      (18002, 18014830382743614344, 162282839565650913585258, 1213, 17941, 9794843876259637, 18030, 63, 18769, 2) = true := by
  decide +kernel
