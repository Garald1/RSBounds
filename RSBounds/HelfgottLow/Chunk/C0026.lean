import RSBounds.HelfgottLow.States

/-! Walk chunk 26, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_26 : RSBounds.HelfgottLow.ChunkGood 26 := by
  decide +kernel
