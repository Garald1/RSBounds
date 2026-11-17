import RSBounds.HelfgottLow.States

/-! Walk chunk 86, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_86 : RSBounds.HelfgottLow.ChunkGood 86 := by
  decide +kernel
