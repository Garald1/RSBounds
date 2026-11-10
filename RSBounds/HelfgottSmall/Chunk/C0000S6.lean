import RSBounds.HelfgottSmall.Split

/-! Part 6 of walk chunk 0 (positions 12002 to 14001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_6 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (12002, 11976509962677774683, 71743878218708590863694, 1131, 11952, 9388653908212811, 12011, 55, 12167, 3)
      (14002, 14011180446853937657, 98178884200208063625202, 1162, 13933, 9542015406953819, 14002, 57, 14641, 4) = true := by
  decide +kernel
