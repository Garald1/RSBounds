import RSBounds.HelfgottSmall.States

/-! Walk chunk 808, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_808 : RSBounds.HelfgottSmall.ChunkGood 808 := by
  decide +kernel
