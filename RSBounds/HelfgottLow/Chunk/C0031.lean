import RSBounds.HelfgottLow.States

/-! Walk chunk 31, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_31 : RSBounds.HelfgottLow.ChunkGood 31 := by
  decide +kernel
