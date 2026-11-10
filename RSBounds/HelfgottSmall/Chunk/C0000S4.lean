import RSBounds.HelfgottSmall.Split

/-! Part 4 of walk chunk 0 (positions 8002 to 10001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_4 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (8002, 7987290971276064395, 31908549116767414845551, 1049, 7972, 8983690682172857, 8011, 49, 8192, 13)
      (10002, 10013400725301655241, 50151309946487757694342, 1094, 9953, 9205629293086258, 10002, 51, 10201, 2) = true := by
  decide +kernel
