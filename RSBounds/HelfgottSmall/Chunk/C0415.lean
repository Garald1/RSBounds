import RSBounds.HelfgottSmall.States

/-! Walk chunk 415, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_415 : RSBounds.HelfgottSmall.ChunkGood 415 := by
  decide +kernel
