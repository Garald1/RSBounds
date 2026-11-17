import RSBounds.HelfgottLow.States

/-! Walk chunk 127, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_127 : RSBounds.HelfgottLow.ChunkGood 127 := by
  decide +kernel
