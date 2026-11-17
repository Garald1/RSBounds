import RSBounds.HelfgottLow.States

/-! Walk chunk 192, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_192 : RSBounds.HelfgottLow.ChunkGood 192 := by
  decide +kernel
