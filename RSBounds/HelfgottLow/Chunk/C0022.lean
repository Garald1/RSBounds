import RSBounds.HelfgottLow.States

/-! Walk chunk 22, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_22 : RSBounds.HelfgottLow.ChunkGood 22 := by
  decide +kernel
