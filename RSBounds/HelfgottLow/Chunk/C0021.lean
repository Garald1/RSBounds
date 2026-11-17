import RSBounds.HelfgottLow.States

/-! Walk chunk 21, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_21 : RSBounds.HelfgottLow.ChunkGood 21 := by
  decide +kernel
