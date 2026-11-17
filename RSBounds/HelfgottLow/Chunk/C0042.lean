import RSBounds.HelfgottLow.States

/-! Walk chunk 42, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_42 : RSBounds.HelfgottLow.ChunkGood 42 := by
  decide +kernel
