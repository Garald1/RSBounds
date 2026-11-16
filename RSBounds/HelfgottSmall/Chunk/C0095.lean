import RSBounds.HelfgottSmall.States

/-! Walk chunk 95, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_95 : RSBounds.HelfgottSmall.ChunkGood 95 := by
  decide +kernel
