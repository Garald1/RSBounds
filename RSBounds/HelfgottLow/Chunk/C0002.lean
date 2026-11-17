import RSBounds.HelfgottLow.States

/-! Walk chunk 2, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_2 : RSBounds.HelfgottLow.ChunkGood 2 := by
  decide +kernel
