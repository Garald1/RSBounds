import RSBounds.HelfgottSmall.States

/-! Walk chunk 1011, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1011 : RSBounds.HelfgottSmall.ChunkGood 1011 := by
  decide +kernel
