import RSBounds.HelfgottLow.States

/-! Walk chunk 60, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_60 : RSBounds.HelfgottLow.ChunkGood 60 := by
  decide +kernel
