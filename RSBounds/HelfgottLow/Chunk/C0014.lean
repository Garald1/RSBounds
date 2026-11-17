import RSBounds.HelfgottLow.States

/-! Walk chunk 14, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_14 : RSBounds.HelfgottLow.ChunkGood 14 := by
  decide +kernel
