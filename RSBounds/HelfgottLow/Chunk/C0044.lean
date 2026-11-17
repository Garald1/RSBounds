import RSBounds.HelfgottLow.States

/-! Walk chunk 44, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_44 : RSBounds.HelfgottLow.ChunkGood 44 := by
  decide +kernel
