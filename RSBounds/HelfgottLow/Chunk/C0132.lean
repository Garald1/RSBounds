import RSBounds.HelfgottLow.States

/-! Walk chunk 132, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_132 : RSBounds.HelfgottLow.ChunkGood 132 := by
  decide +kernel
