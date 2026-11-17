import RSBounds.HelfgottLow.States

/-! Walk chunk 32, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_32 : RSBounds.HelfgottLow.ChunkGood 32 := by
  decide +kernel
