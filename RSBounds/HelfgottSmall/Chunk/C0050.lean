import RSBounds.HelfgottSmall.States

/-! Walk chunk 50, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_50 : RSBounds.HelfgottSmall.ChunkGood 50 := by
  decide +kernel
