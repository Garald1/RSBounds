import RSBounds.HelfgottLow.States

/-! Walk chunk 104, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_104 : RSBounds.HelfgottLow.ChunkGood 104 := by
  decide +kernel
