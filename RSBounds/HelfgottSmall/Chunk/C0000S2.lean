import RSBounds.HelfgottSmall.Split

/-! Part 2 of walk chunk 0 (positions 4002 to 6001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_2 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (4002, 3997974359365986756, 7999693004422234510824, 908, 3995, 8292798859040469, 4014, 39, 4096, 12)
      (6002, 5988117236350652520, 17941021031389120529672, 991, 5994, 8698514248716748, 6023, 44, 6241, 2) = true := by
  decide +kernel
