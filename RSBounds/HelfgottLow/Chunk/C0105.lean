import RSBounds.HelfgottLow.States

/-! Walk chunk 105, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_105 : RSBounds.HelfgottLow.ChunkGood 105 := by
  decide +kernel
