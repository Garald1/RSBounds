import RSBounds.HelfgottLow.States

/-! Walk chunk 82, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_82 : RSBounds.HelfgottLow.ChunkGood 82 := by
  decide +kernel
