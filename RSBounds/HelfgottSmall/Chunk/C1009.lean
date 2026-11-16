import RSBounds.HelfgottSmall.States

/-! Walk chunk 1009, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1009 : RSBounds.HelfgottSmall.ChunkGood 1009 := by
  decide +kernel
