import RSBounds.HelfgottLow.States

/-! Walk chunk 65, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_65 : RSBounds.HelfgottLow.ChunkGood 65 := by
  decide +kernel
