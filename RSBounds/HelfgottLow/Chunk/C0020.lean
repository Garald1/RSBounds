import RSBounds.HelfgottLow.States

/-! Walk chunk 20, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_20 : RSBounds.HelfgottLow.ChunkGood 20 := by
  decide +kernel
