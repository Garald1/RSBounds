import RSBounds.HelfgottSmall.States

/-! Walk chunk 925, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_925 : RSBounds.HelfgottSmall.ChunkGood 925 := by
  decide +kernel
