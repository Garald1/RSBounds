import RSBounds.HelfgottLow.States

/-! Walk chunk 40, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_40 : RSBounds.HelfgottLow.ChunkGood 40 := by
  decide +kernel
