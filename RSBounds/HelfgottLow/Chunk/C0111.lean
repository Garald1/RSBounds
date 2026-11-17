import RSBounds.HelfgottLow.States

/-! Walk chunk 111, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_111 : RSBounds.HelfgottLow.ChunkGood 111 := by
  decide +kernel
