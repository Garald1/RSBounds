import RSBounds.HelfgottSmall.States

/-! Walk chunk 375, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_375 : RSBounds.HelfgottSmall.ChunkGood 375 := by
  decide +kernel
