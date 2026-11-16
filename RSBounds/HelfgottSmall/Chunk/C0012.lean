import RSBounds.HelfgottSmall.States

/-! Walk chunk 12, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_12 : RSBounds.HelfgottSmall.ChunkGood 12 := by
  decide +kernel
