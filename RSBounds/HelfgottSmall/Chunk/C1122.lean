import RSBounds.HelfgottSmall.States

/-! Walk chunk 1122, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1122 : RSBounds.HelfgottSmall.ChunkGood 1122 := by
  decide +kernel
