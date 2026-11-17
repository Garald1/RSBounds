import RSBounds.HelfgottLow.States

/-! Walk chunk 52, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_52 : RSBounds.HelfgottLow.ChunkGood 52 := by
  decide +kernel
