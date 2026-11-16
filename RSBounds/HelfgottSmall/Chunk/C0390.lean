import RSBounds.HelfgottSmall.States

/-! Walk chunk 390, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_390 : RSBounds.HelfgottSmall.ChunkGood 390 := by
  decide +kernel
