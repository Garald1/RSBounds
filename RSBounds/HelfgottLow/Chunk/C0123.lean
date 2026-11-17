import RSBounds.HelfgottLow.States

/-! Walk chunk 123, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_123 : RSBounds.HelfgottLow.ChunkGood 123 := by
  decide +kernel
