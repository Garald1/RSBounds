import RSBounds.HelfgottSmall.States

/-! Walk chunk 380, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_380 : RSBounds.HelfgottSmall.ChunkGood 380 := by
  decide +kernel
