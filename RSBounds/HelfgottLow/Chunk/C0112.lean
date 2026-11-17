import RSBounds.HelfgottLow.States

/-! Walk chunk 112, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_112 : RSBounds.HelfgottLow.ChunkGood 112 := by
  decide +kernel
