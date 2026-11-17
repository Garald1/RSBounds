import RSBounds.HelfgottLow.States

/-! Walk chunk 101, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_101 : RSBounds.HelfgottLow.ChunkGood 101 := by
  decide +kernel
