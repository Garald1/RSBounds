import RSBounds.HelfgottLow.States

/-! Walk chunk 75, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_75 : RSBounds.HelfgottLow.ChunkGood 75 := by
  decide +kernel
