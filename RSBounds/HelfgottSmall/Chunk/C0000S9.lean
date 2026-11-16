import RSBounds.HelfgottSmall.Split

/-! Part 9 of walk chunk 0 (positions 18002 to 20001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_9 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (18002, 18014830382743614344, 162282839565650913585258, 1213, 17941, 9794843876259637, 18030, 63, 18769, 2)
      (20002, 19976518807272000996, 199578084351016601655550, 1234, 19912, 9899077844887692, 20011, 66, 22201, 2) = true := by
  decide +kernel
