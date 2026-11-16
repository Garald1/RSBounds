import RSBounds.HelfgottSmall.Split

/-! Part 3 of walk chunk 0 (positions 6002 to 8001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_3 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (6002, 5988117236350652520, 17941021031389120529672, 991, 5994, 8698514248716748, 6023, 44, 6241, 2)
      (8002, 7987290971276064395, 31908549116767414845551, 1049, 7972, 8983690682172857, 8011, 49, 8192, 13) = true := by
  decide +kernel
