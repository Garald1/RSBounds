import RSBounds.HelfgottSmall.States

/-! Walk chunk 1200, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1200 : RSBounds.HelfgottSmall.ChunkGood 1200 := by
  decide +kernel
