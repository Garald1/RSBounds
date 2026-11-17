import RSBounds.HelfgottLow.States

/-! Walk chunk 66, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_66 : RSBounds.HelfgottLow.ChunkGood 66 := by
  decide +kernel
