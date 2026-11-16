import RSBounds.HelfgottSmall.Split

/-! Part 5 of walk chunk 0 (positions 10002 to 12001). Chunk 0 is split because its many anchor switches need more memory. -/

theorem RSBounds.HelfgottSmall.chunk_0_part_5 :
    RSBounds.HelfgottSmall.chunkOK 2000
      (10002, 10013400725301655241, 50151309946487757694342, 1094, 9953, 9205629293086258, 10002, 51, 10201, 2)
      (12002, 11976509962677774683, 71743878218708590863694, 1131, 11952, 9388653908212811, 12011, 55, 12167, 3) = true := by
  decide +kernel
