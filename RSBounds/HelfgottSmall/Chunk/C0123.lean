import RSBounds.HelfgottSmall.States

/-! Walk chunk 123, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_123 : RSBounds.HelfgottSmall.ChunkGood 123 := by
  decide +kernel
