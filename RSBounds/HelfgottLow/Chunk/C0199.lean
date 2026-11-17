import RSBounds.HelfgottLow.States

/-! Walk chunk 199, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_199 : RSBounds.HelfgottLow.ChunkGood 199 := by
  decide +kernel
