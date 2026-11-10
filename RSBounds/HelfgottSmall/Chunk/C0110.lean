import RSBounds.HelfgottSmall.States

/-! Walk chunk 110, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_110 : RSBounds.HelfgottSmall.ChunkGood 110 := by
  decide +kernel
