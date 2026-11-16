import RSBounds.HelfgottSmall.States

/-! Walk chunk 311, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_311 : RSBounds.HelfgottSmall.ChunkGood 311 := by
  decide +kernel
