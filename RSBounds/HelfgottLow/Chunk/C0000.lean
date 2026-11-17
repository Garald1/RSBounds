import RSBounds.HelfgottLow.States

/-! Walk chunk 0, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_0 : RSBounds.HelfgottLow.ChunkGood 0 := by
  decide +kernel
