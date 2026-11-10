import RSBounds.HelfgottSmall.States

/-! Walk chunk 1000, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1000 : RSBounds.HelfgottSmall.ChunkGood 1000 := by
  decide +kernel
