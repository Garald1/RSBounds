import RSBounds.HelfgottLow.States

/-! Walk chunk 83, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_83 : RSBounds.HelfgottLow.ChunkGood 83 := by
  decide +kernel
