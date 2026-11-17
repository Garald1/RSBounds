import RSBounds.HelfgottLow.States

/-! Walk chunk 80, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_80 : RSBounds.HelfgottLow.ChunkGood 80 := by
  decide +kernel
