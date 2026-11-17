import RSBounds.HelfgottLow.States

/-! Walk chunk 51, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_51 : RSBounds.HelfgottLow.ChunkGood 51 := by
  decide +kernel
