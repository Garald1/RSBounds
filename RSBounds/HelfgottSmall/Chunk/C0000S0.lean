import RSBounds.HelfgottSmall.Split

/-! Part 0 of walk chunk 0 (positions 2 to 2001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_0 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (2, 0, 0, 0, 2, 693147180800000, 3, 0, 4, 2)
      (2002, 1994452091221954778, 1992528470135839362159, 764, 1999, 7600402335340415, 2008, 30, 2048, 11) = true := by
  decide +kernel
