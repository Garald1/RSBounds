import RSBounds.HelfgottLow.States

/-! Walk chunk 140, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_140 : RSBounds.HelfgottLow.ChunkGood 140 := by
  decide +kernel
