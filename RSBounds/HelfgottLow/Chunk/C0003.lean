import RSBounds.HelfgottLow.States

/-! Walk chunk 3, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_3 : RSBounds.HelfgottLow.ChunkGood 3 := by
  decide +kernel
