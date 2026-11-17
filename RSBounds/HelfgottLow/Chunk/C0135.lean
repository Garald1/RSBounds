import RSBounds.HelfgottLow.States

/-! Walk chunk 135, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_135 : RSBounds.HelfgottLow.ChunkGood 135 := by
  decide +kernel
