import RSBounds.HelfgottLow.States

/-! Walk chunk 33, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_33 : RSBounds.HelfgottLow.ChunkGood 33 := by
  decide +kernel
