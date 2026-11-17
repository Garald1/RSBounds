import RSBounds.HelfgottLow.States

/-! Walk chunk 98, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_98 : RSBounds.HelfgottLow.ChunkGood 98 := by
  decide +kernel
