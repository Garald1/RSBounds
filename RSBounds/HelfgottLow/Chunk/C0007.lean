import RSBounds.HelfgottLow.States

/-! Walk chunk 7, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_7 : RSBounds.HelfgottLow.ChunkGood 7 := by
  decide +kernel
