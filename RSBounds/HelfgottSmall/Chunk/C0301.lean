import RSBounds.HelfgottSmall.States

/-! Walk chunk 301, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_301 : RSBounds.HelfgottSmall.ChunkGood 301 := by
  decide +kernel
