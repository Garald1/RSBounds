import RSBounds.HelfgottSmall.States

/-! Walk chunk 604, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_604 : RSBounds.HelfgottSmall.ChunkGood 604 := by
  decide +kernel
