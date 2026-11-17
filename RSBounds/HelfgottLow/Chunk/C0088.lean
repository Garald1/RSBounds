import RSBounds.HelfgottLow.States

/-! Walk chunk 88, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_88 : RSBounds.HelfgottLow.ChunkGood 88 := by
  decide +kernel
