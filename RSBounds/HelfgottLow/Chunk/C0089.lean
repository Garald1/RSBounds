import RSBounds.HelfgottLow.States

/-! Walk chunk 89, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_89 : RSBounds.HelfgottLow.ChunkGood 89 := by
  decide +kernel
