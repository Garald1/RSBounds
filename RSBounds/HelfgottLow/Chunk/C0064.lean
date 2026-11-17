import RSBounds.HelfgottLow.States

/-! Walk chunk 64, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_64 : RSBounds.HelfgottLow.ChunkGood 64 := by
  decide +kernel
