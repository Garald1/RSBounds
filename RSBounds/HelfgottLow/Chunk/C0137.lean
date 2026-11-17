import RSBounds.HelfgottLow.States

/-! Walk chunk 137, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_137 : RSBounds.HelfgottLow.ChunkGood 137 := by
  decide +kernel
