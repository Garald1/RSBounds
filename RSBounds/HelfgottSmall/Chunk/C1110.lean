import RSBounds.HelfgottSmall.States

/-! Walk chunk 1110, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1110 : RSBounds.HelfgottSmall.ChunkGood 1110 := by
  decide +kernel
