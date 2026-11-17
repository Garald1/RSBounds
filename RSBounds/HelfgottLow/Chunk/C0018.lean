import RSBounds.HelfgottLow.States

/-! Walk chunk 18, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_18 : RSBounds.HelfgottLow.ChunkGood 18 := by
  decide +kernel
