import RSBounds.HelfgottLow.States

/-! Walk chunk 25, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_25 : RSBounds.HelfgottLow.ChunkGood 25 := by
  decide +kernel
