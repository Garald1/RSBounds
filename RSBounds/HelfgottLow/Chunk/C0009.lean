import RSBounds.HelfgottLow.States

/-! Walk chunk 9, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_9 : RSBounds.HelfgottLow.ChunkGood 9 := by
  decide +kernel
