import RSBounds.HelfgottLow.States

/-! Walk chunk 96, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_96 : RSBounds.HelfgottLow.ChunkGood 96 := by
  decide +kernel
