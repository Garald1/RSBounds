import RSBounds.HelfgottLow.States

/-! Walk chunk 126, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_126 : RSBounds.HelfgottLow.ChunkGood 126 := by
  decide +kernel
