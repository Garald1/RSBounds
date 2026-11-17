import RSBounds.HelfgottLow.States

/-! Walk chunk 81, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_81 : RSBounds.HelfgottLow.ChunkGood 81 := by
  decide +kernel
