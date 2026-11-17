import RSBounds.HelfgottLow.States

/-! Walk chunk 90, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_90 : RSBounds.HelfgottLow.ChunkGood 90 := by
  decide +kernel
