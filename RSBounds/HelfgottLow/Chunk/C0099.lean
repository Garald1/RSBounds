import RSBounds.HelfgottLow.States

/-! Walk chunk 99, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_99 : RSBounds.HelfgottLow.ChunkGood 99 := by
  decide +kernel
