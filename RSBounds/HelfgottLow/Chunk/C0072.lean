import RSBounds.HelfgottLow.States

/-! Walk chunk 72, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_72 : RSBounds.HelfgottLow.ChunkGood 72 := by
  decide +kernel
