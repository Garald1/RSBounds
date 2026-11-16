import RSBounds.HelfgottSmall.States

/-! Walk chunk 30, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_30 : RSBounds.HelfgottSmall.ChunkGood 30 := by
  decide +kernel
