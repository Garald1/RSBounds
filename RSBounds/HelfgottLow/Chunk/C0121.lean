import RSBounds.HelfgottLow.States

/-! Walk chunk 121, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_121 : RSBounds.HelfgottLow.ChunkGood 121 := by
  decide +kernel
