import RSBounds.HelfgottLow.States

/-! Walk chunk 129, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_129 : RSBounds.HelfgottLow.ChunkGood 129 := by
  decide +kernel
