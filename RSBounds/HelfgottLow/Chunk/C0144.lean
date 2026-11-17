import RSBounds.HelfgottLow.States

/-! Walk chunk 144, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_144 : RSBounds.HelfgottLow.ChunkGood 144 := by
  decide +kernel
