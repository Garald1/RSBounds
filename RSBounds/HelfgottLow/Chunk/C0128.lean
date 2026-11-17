import RSBounds.HelfgottLow.States

/-! Walk chunk 128, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_128 : RSBounds.HelfgottLow.ChunkGood 128 := by
  decide +kernel
