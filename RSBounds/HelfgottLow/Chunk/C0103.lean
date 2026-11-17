import RSBounds.HelfgottLow.States

/-! Walk chunk 103, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_103 : RSBounds.HelfgottLow.ChunkGood 103 := by
  decide +kernel
