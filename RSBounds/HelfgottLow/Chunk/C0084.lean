import RSBounds.HelfgottLow.States

/-! Walk chunk 84, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_84 : RSBounds.HelfgottLow.ChunkGood 84 := by
  decide +kernel
