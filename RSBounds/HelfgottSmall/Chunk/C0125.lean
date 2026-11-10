import RSBounds.HelfgottSmall.States

/-! Walk chunk 125, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_125 : RSBounds.HelfgottSmall.ChunkGood 125 := by
  decide +kernel
