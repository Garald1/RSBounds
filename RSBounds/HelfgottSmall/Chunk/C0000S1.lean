import RSBounds.HelfgottSmall.Split

/-! Part 1 of walk chunk 0 (positions 2002 to 4001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_1 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (2002, 1994452091221954778, 1992528470135839362159, 764, 1999, 7600402335340415, 2008, 30, 2048, 11)
      (4002, 3997974359365986756, 7999693004422234510824, 908, 3995, 8292798859040469, 4014, 39, 4096, 12) = true := by
  decide +kernel
