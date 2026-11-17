import RSBounds.HelfgottLow.States

/-! Walk chunk 150, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_150 : RSBounds.HelfgottLow.ChunkGood 150 := by
  decide +kernel
