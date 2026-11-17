import RSBounds.HelfgottLow.States

/-! Walk chunk 48, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_48 : RSBounds.HelfgottLow.ChunkGood 48 := by
  decide +kernel
