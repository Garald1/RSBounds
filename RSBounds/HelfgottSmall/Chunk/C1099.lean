import RSBounds.HelfgottSmall.States

/-! Walk chunk 1099, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_1099 : RSBounds.HelfgottSmall.ChunkGood 1099 := by
  decide +kernel
