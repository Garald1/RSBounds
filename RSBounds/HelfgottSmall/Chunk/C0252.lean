import RSBounds.HelfgottSmall.States

/-! Walk chunk 252, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_252 : RSBounds.HelfgottSmall.ChunkGood 252 := by
  decide +kernel
