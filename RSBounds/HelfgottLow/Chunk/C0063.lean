import RSBounds.HelfgottLow.States

/-! Walk chunk 63, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_63 : RSBounds.HelfgottLow.ChunkGood 63 := by
  decide +kernel
